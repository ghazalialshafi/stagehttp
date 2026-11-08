## stagelane/sched — tasks, the event loop, timers, parking, cancellation and
## structured concurrency on top of the continuation core.
import ./core, ./transform
import std/[deques, monotimes, os, macros, selectors, tables]
when defined(linux):
  import std/[posix, epoll]
when defined(windows):
  import std/nativesockets      # SocketHandle: the Windows (select) selector wants it, not cint
when flowThreads:
  import std/[locks, atomics]

when defined(windows):
  # Nim's Windows selector is built on select(), which can watch at most FD_SETSIZE
  # sockets per event loop (64 unless the macro is raised before winsock2.h is
  # included).  Raise it; override with -d:flowFdSetSize=N.  Past this number
  # registering a socket raises IOSelectorsException.
  const flowFdSetSize* {.intdefine.} = 4096
  {.passC: "-DFD_SETSIZE=" & $flowFdSetSize.}

when flowThreads:
  when defined(windows):
    proc switchToThread(): int32 {.stdcall, dynlib: "kernel32", importc: "SwitchToThread".}
    proc osYield*() {.inline.} = discard switchToThread()
  else:
    proc sched_yield(): cint {.importc: "sched_yield", header: "<sched.h>".}
    proc osYield*() {.inline.} = discard sched_yield()   ## give the CPU to another runnable thread
  type
    SchedShared* = object
      ## the part of a scheduler other threads may touch: a lock-free mailbox of
      ## continuations (intrusive MPSC queue, linked through `Frame.next`) plus a
      ## wake-up event
      mhead: Atomic[pointer]    # producers: newest node (exchanged)
      mtail: pointer            # consumer only: oldest node
      stub: pointer             # permanent dummy node (pinned Frame)
      wake*: SelectEvent
      stopping*: Atomic[bool]
      sleeping*: Atomic[bool]   ## the owner is (about to be) blocked in `select`: a poster must trigger `wake`

type
  Timer* = ref object of RootObj
    at: int64                  # absolute deadline in ms (monotonic)
    next: pointer              # intrusive link inside a wheel slot
    cb: proc () {.closure.}
    leaf: pointer              # pinned continuation to resume when the timer fires
    cancelled: bool

proc `=destroy`(t: var typeof(Timer()[])) =
  if t.leaf != nil: releaseChain(t.leaf)       # the wheel was dropped with sleepers in it

type
  TimerList = object
    head, tail: pointer

  Wheel = object
    ## hierarchical timing wheel: 4 levels x 256 slots, 1 ms resolution
    now: int64
    live: int                  # armed (not cancelled, not fired) timers
    slots: array[4, array[256, TimerList]]


proc tlPush(l: var TimerList, t: sink Timer) {.inline.} =
  let p = cast[pointer](t)
  wasMoved(t)
  cast[Timer](p).next = nil
  if l.tail == nil: l.head = p else: cast[Timer](l.tail).next = p
  l.tail = p

proc tlTake(l: var TimerList): pointer {.inline.} =
  ## detach the whole list; the caller owns every element
  result = l.head
  l.head = nil
  l.tail = nil

proc tlNext(p: pointer): Timer {.inline.} =
  ## pop `p` as an owned Timer reference (no refcount change)
  copyMem(addr result, unsafeAddr p, sizeof(pointer))

proc `=destroy`(w: var Wheel) =
  for level in 0..3:
    for slot in 0..255:
      var p = w.slots[level][slot].head
      while p != nil:
        let nxt = cast[Timer](p).next
        var t = tlNext(p)       # drops the wheel's reference
        p = nxt
      w.slots[level][slot].head = nil
      w.slots[level][slot].tail = nil

proc `=copy`(dest: var Wheel, src: Wheel) {.error.}


type
  FdWait = ref object
    rd, wr: pointer            # pinned continuations waiting for readability / writability
    evs: set[Event]
    registered: bool

proc `=destroy`(f: var typeof(FdWait()[])) =
  if f.rd != nil: releaseChain(f.rd)
  if f.wr != nil: releaseChain(f.wr)

type
  CancelledError* = object of CatchableError
  DeadlockError* = object of CatchableError
  TimeoutError* = object of CatchableError

  Task*[T] = ref object of TaskBase
    when T isnot void:
      value*: T

  Scheduler* = ref object
    when flowThreads:
      shared*: ptr SchedShared
    sel: Selector[int]
    fds: Table[int, FdWait]
    fdWaiting: int
    ready: FrameList
    wheel: Wheel
    live*: int
    steps*: uint64
    when defined(linux):
      pepOn: bool                  # the persistent (edge-triggered) epoll exists
      pep: cint
      pioWaiting: int              # tasks parked on a PollFd (also counted in fdWaiting)
      pfree: pointer               # freelist of PollFdObj
      pev: array[256, EpollEvent]


var theSched {.threadvar.}: Scheduler
var curTaskP {.threadvar.}: pointer
template curTask*(): TaskBase = cast[TaskBase](curTaskP)

when flowThreads:
  proc initShared(): ptr SchedShared =
    result = cast[ptr SchedShared](allocShared0(sizeof(SchedShared)))
    result.stub = pin(Frame())
    result.mhead.store(result.stub)
    result.mtail = result.stub
    result.wake = newSelectEvent()

  proc mbLink(sh: ptr SchedShared, c: pointer) {.inline.} =
    ## wait-free publish of node `c` (Vyukov MPSC): swing the head, then link
    ## the previous head to us
    atomicStoreN(addr envOf(c).next, nil, ATOMIC_RELAXED)
    let prev = sh.mhead.exchange(c, moAcquireRelease)
    atomicStoreN(addr envOf(prev).next, c, ATOMIC_RELEASE)

  proc post*(target: ptr SchedShared, c: pointer) =
    ## hand a pinned continuation to the scheduler that owns `target` (any thread)
    mbLink(target, c)
    # Only a sleeping owner needs the (syscall) wake-up; a running one drains its
    # mailbox on the next loop turn.  The owner publishes `sleeping` *before* its
    # last look at the mailbox, so this check cannot lose a wake-up.
    if target.sleeping.load(): target.wake.trigger()

  proc mbPop(sh: ptr SchedShared): pointer =
    ## consumer side: the oldest node, or nil (also nil while a producer is
    ## between its two steps; the node shows up on a later call)
    var tail = sh.mtail
    var next = cast[pointer](atomicLoadN(addr envOf(tail).next, ATOMIC_ACQUIRE))
    if tail == sh.stub:
      if next == nil: return nil
      sh.mtail = next
      tail = next
      next = cast[pointer](atomicLoadN(addr envOf(tail).next, ATOMIC_ACQUIRE))
    if next != nil:
      sh.mtail = next
      return tail
    if tail != sh.mhead.load(): return nil      # a producer is mid-publish
    mbLink(sh, sh.stub)                         # re-insert the stub behind `tail`
    next = cast[pointer](atomicLoadN(addr envOf(tail).next, ATOMIC_ACQUIRE))
    if next != nil:
      sh.mtail = next
      return tail
    nil

proc initSched() {.noinline.} =
  if theSched == nil:
    theSched = Scheduler()
    when flowThreads:
      theSched.shared = initShared()
      theSched.sel = newSelector[int]()
      theSched.sel.registerEvent(theSched.shared.wake, 0)

template sched*(): Scheduler =
  ## the scheduler of this thread (borrowed: no refcount traffic)
  if theSched == nil: initSched()
  theSched

when flowThreads:
  proc inboxEmpty(sh: ptr SchedShared): bool {.inline.} =
    ## owner only: nothing queued and no producer mid-publish
    sh.mtail == sh.stub and sh.mhead.load() == sh.stub

  proc drainInbox(s: Scheduler) =
    let sh = s.shared
    if inboxEmpty(sh): return           # common case: two loads, no lock
    while true:
      let c = mbPop(sh)
      if c == nil: break
      s.ready.addLast c

proc nowNs*(): int64 = getMonoTime().ticks
proc nowMs(): int64 {.inline.} = getMonoTime().ticks div 1_000_000

proc newWaitQueue*(): WaitQueue =
  result = WaitQueue()
  when flowThreads: initLock(result.lock)

when flowThreads:
  # A task's completion state and its (lazily created) `doneq` are guarded by one
  # of a few global stripe locks instead of a per-task WaitQueue + mutex that
  # would have to be allocated for every task up front.
  var taskLocks: array[64, Lock]
  for i in 0..<taskLocks.len: initLock(taskLocks[i])
  template taskStripe(t: TaskBase): int = int((cast[uint](t) shr 6) and 63)

template tlock(t: TaskBase, body: untyped) =
  when flowThreads:
    {.cast(gcsafe).}:
      withLock taskLocks[taskStripe(t)]: body
  else:
    body

template qlock(q: WaitQueue, body: untyped) =
  when flowThreads:
    withLock q.lock: body
  else:
    body

proc schedule*(c: pointer) =
  ## queue a pinned continuation (routed to its owning thread when needed)
  when flowThreads:
    let s {.cursor.} = sched()
    let t = envOf(c).task
    if t != nil and t.sched != nil and t.sched != cast[pointer](s.shared):
      post(cast[ptr SchedShared](t.sched), c)
      return
    s.ready.addLast c
  else:
    sched().ready.addLast c

proc newCancelled*(): ref CancelledError =
  newException(CancelledError, "task cancelled")

proc checkpoint*() =
  ## cooperative cancellation point for non-suspending loops
  if curTaskP != nil and curTask.cancelRequested: raise newCancelled()

proc wake*(c: pointer) {.inline.} =
  ## resume a parked (pinned) continuation
  let t = envOf(c).task
  if t != nil:
    t.parked = nil
    t.parkKind = pkNone
  schedule(c)

# --- timers ----------------------------------------------------------------

proc wheelAdd(w: var Wheel, t: sink Timer) =
  if t.at <= w.now: t.at = w.now + 1
  let d = t.at - w.now
  var level = 0
  while level < 3 and d >= (1'i64 shl (8 * (level + 1))): inc level
  w.slots[level][int((t.at shr (8 * level)) and 255)].tlPush t

proc fireOrReplace(w: var Wheel, p: pointer, fire: bool) =
  var cur = p
  while cur != nil:
    let nxt = cast[Timer](cur).next
    var t = tlNext(cur)
    t.next = nil
    cur = nxt
    if t.cancelled: continue
    if fire and t.at <= w.now:
      dec w.live
      t.cancelled = true            # fired: a later `cancel` must not count again
      if t.leaf != nil:
        let lf = t.leaf
        t.leaf = nil
        wake(lf)
      elif t.cb != nil:
        let cb = t.cb
        t.cb = nil
        cb()
    else:
      wheelAdd(w, t)

proc cascade(w: var Wheel, level: int) =
  let idx = int((w.now shr (8 * level)) and 255)
  let p = w.slots[level][idx].tlTake
  if idx == 0 and level < 3: cascade(w, level + 1)
  fireOrReplace(w, p, false)

proc wheelAdvance(w: var Wheel, to: int64) =
  while w.now < to:
    inc w.now
    let s0 = int(w.now and 255)
    if s0 == 0: cascade(w, 1)
    if w.slots[0][s0].head != nil:
      let p = w.slots[0][s0].tlTake
      fireOrReplace(w, p, true)
    if w.live == 0:
      w.now = to          # nothing armed: skip the rest
      break

proc wheelNextWake(w: Wheel): int =
  ## ms until the earliest armed timer may expire (conservative); -1 if none
  if w.live == 0: return -1
  for i in 1..256:
    if w.slots[0][int((w.now + i) and 255)].head != nil: return i
  for level in 1..3:
    for i in 1..256:
      let idx = int(((w.now shr (8 * level)) + i) and 255)
      if w.slots[level][idx].head != nil:
        let start = (((w.now shr (8 * level)) + i) shl (8 * level))
        return int(max(1'i64, start - w.now))
  1

proc newTimerAt(ms: int): Timer =
  let s {.cursor.} = sched()
  if s.wheel.live == 0 and s.wheel.now < nowMs(): s.wheel.now = nowMs()
  result = Timer(at: nowMs() + max(ms, 1))
  inc s.wheel.live

proc addTimer*(ms: int, cb: proc () {.closure.}): Timer =
  result = newTimerAt(ms)
  result.cb = cb
  sched().wheel.wheelAdd result

proc addLeafTimer(ms: int, leaf: pointer): Timer =
  result = newTimerAt(ms)
  result.leaf = leaf
  sched().wheel.wheelAdd result

proc cancel*(t: Timer) =
  if t != nil and not t.cancelled:
    t.cancelled = true
    t.cb = nil
    t.leaf = nil
    dec sched().wheel.live

# --- parking -----------------------------------------------------------------
# A suspension primitive is a *hook*: `proc (c: Frame, ..): Hop`.  `c` is
# the continuation that suspends (the caller itself -- nothing is allocated).
# It already carries a pin; the hook either keeps that pin somewhere (queue,
# timer, fd table) and returns `noStep`, or returns a step to continue at once.

template cancelGuard(c: Frame) =
  if c.task != nil and c.task.cancelRequested:
    c.ex = newCancelled()
    return step(cast[pointer](c))

template markParked(c: Frame, kind: ParkKind) =
  let t = c.task
  if t != nil:
    t.parked = cast[pointer](c)
    t.parkKind = kind

type
  AnyState = ref object of RootObj
    fired: bool
    target: pointer              # the pin of the waiting continuation
    qs: seq[WaitQueue]
  AnyProxy = ref object of Frame
    st: AnyState

proc `=destroy`(a: var typeof(AnyState()[])) =
  if a.target != nil: releaseChain(a.target)

proc anyProxyStage(p: pointer): Hop = noStep
let anyProxyFn = stageFn(anyProxyStage)

proc removeWaiter(q: WaitQueue, c: pointer): bool =
  qlock q:
    result = q.waiters.remove(c)

proc removeAny(q: WaitQueue, st: AnyState) =
  qlock q:
    var p = q.waiters.head
    while p != nil:
      let nxt = envOf(p).next
      if envOf(p).fn == anyProxyFn and AnyProxy(envOf(p)).st == st:
        if q.waiters.remove(p): release(p)      # proxies own their pin
      p = nxt

proc fireAny(st: AnyState, via: WaitQueue) =
  let target = st.target
  st.target = nil
  let qs = move st.qs
  for q2 in qs:
    if q2 != via: removeAny(q2, st)
  wake(target)

proc notifyOne*(q: WaitQueue): bool {.discardable.} =
  var w: pointer = nil
  qlock q:
    inc q.epoch
    while q.waiters.len > 0:
      let cand = q.waiters.popFirst
      if envOf(cand).fn == anyProxyFn:
        let st = AnyProxy(envOf(cand)).st
        if st.fired:                 # stale entry of an already woken `waitAny`
          release(cand)
          continue
        st.fired = true
      w = cand
      break
  if w == nil: return false
  if envOf(w).fn == anyProxyFn:
    let st = AnyProxy(envOf(w)).st
    release(w)
    fireAny(st, q)
  else: wake(w)
  result = true

proc notifyAll*(q: WaitQueue) =
  while notifyOne(q): discard

proc epochOf*(q: WaitQueue): int =
  qlock q:
    result = q.epoch

proc parkHook*(c: Frame, q: WaitQueue): Hop =
  cancelGuard(c)
  let p = cast[pointer](c)
  let t = c.task
  if t != nil:
    t.parked = p; t.parkKind = pkQueue; t.parkQ = cast[pointer](q)
  qlock q:
    q.waiters.addLast p
  noStep

proc parkSinceHook*(c: Frame, q: WaitQueue, since: int): Hop =
  cancelGuard(c)
  let p = cast[pointer](c)
  var stale = false
  let t = c.task
  if t != nil:
    t.parked = p; t.parkKind = pkQueue; t.parkQ = cast[pointer](q)
  qlock q:
    if q.epoch != since: stale = true
    else: q.waiters.addLast p
  if stale:
    if t != nil: (t.parked = nil; t.parkKind = pkNone)
    return step(p)
  noStep

proc parkPendingHook*(c: Frame, target: TaskBase): Hop =
  cancelGuard(c)
  let p = cast[pointer](c)
  let t = c.task
  var finished = false
  tlock target:
    if target.state != tsPending: finished = true
    else:
      if target.doneq == nil: target.doneq = newWaitQueue()
      let q {.cursor.} = target.doneq
      if t != nil:
        t.parked = p; t.parkKind = pkQueue; t.parkQ = cast[pointer](q)
      qlock q:
        q.waiters.addLast p
  if finished: return step(p)
  noStep

proc parkAnyHook*(c: Frame, qs: seq[WaitQueue]): Hop =
  cancelGuard(c)
  let p = cast[pointer](c)
  let t = c.task
  let st = AnyState(target: p, qs: qs)
  if t != nil:
    t.parked = p; t.parkKind = pkAny; t.parkRef = cast[pointer](st)
  for q in qs:
    let proxy = pin(AnyProxy(fn: anyProxyFn, st: st))
    qlock q:
      q.waiters.addLast proxy
  noStep

proc sleepHook*(c: Frame, ms: int): Hop =
  cancelGuard(c)
  let p = cast[pointer](c)
  if ms <= 0: return step(p)
  let t = c.task
  let tm = addLeafTimer(ms, p)
  if t != nil:
    t.parkKind = pkTimer; t.parkRef = cast[pointer](tm)
    t.parked = p
  noStep

proc yieldHook*(c: Frame): Hop =
  cancelGuard(c)
  schedule(cast[pointer](c))
  noStep

const spawnHighWater* {.intdefine: "flowSpawnHighWater".} = 1024
  ## Backpressure for structured spawns: when this many continuations are already
  ## queued, `go(scope, ...)` lets them run before the spawner continues, so a
  ## burst of spawns keeps a bounded working set (hot in cache, recycled memory)
  ## instead of building a queue as large as the burst.  0 disables the check.

proc spawnHook*(c: Frame): Hop =
  let p = cast[pointer](c)
  if sched().ready.len < spawnHighWater: return step(p)    # common case: keep going
  schedule(p)
  noStep

# --- the stubs (also usable outside flow procs through `blockOn`) ------------
# `blockOn` needs a continuation object: a tiny leaf that runs the hook with
# itself as the suspended continuation and finishes when resumed.

proc doneStage(p: pointer): Hop =
  if envOf(p).ex != nil: raise popEx(envOf(p))
  finish(p)

type
  PrimLeaf = ref object of Frame
    q: WaitQueue
    n: int
    tgt: TaskBase
    qs: seq[WaitQueue]

proc leafPark(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; parkHook(c, c.q)
proc leafSince(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; parkSinceHook(c, c.q, c.n)
proc leafPending(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; parkPendingHook(c, c.tgt)
proc leafAny(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; parkAnyHook(c, c.qs)
proc leafSleep(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; sleepHook(c, c.n)
proc leafYield(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; yieldHook(c)

proc parkCtor(q: WaitQueue): Frame = PrimLeaf(fn: leafPark, q: q)
proc parkSinceCtor(q: WaitQueue, since: int): Frame =
  PrimLeaf(fn: leafSince, q: q, n: since)
proc parkPendingCtor(target: TaskBase): Frame = PrimLeaf(fn: leafPending, tgt: target)
proc parkAnyCtor(qs: seq[WaitQueue]): Frame = PrimLeaf(fn: leafAny, qs: qs)
proc sleepCtor(ms: int): Frame = PrimLeaf(fn: leafSleep, n: ms)
proc yieldCtor(): Frame = PrimLeaf(fn: leafYield)
proc spawnPointCtor(): Frame = PrimLeaf(fn: leafYield)

proc park*(q: WaitQueue) {.flowCtor: parkCtor, inlineSuspend: parkHook.} =
  ## suspend the calling flow proc until `notifyOne`/`notifyAll` wakes it
  blockOn(parkCtor(q))
proc parkSince*(q: WaitQueue, since: int) {.flowCtor: parkSinceCtor, inlineSuspend: parkSinceHook.} =
  ## like `park`, but returns immediately when `q.epoch != since` -- the
  ## lost-wakeup-free pattern for state shared between threads
  blockOn(parkSinceCtor(q, since))
proc parkPending*(target: TaskBase) {.flowCtor: parkPendingCtor, inlineSuspend: parkPendingHook.} =
  blockOn(parkPendingCtor(target))
proc waitAny*(qs: seq[WaitQueue]) {.flowCtor: parkAnyCtor, inlineSuspend: parkAnyHook.} =
  ## suspend until *any* of the queues notifies us
  blockOn(parkAnyCtor(qs))
proc delay*(ms: int) {.flowCtor: sleepCtor, inlineSuspend: sleepHook.} =
  ## suspend for `ms` milliseconds
  blockOn(sleepCtor(ms))
proc yieldNow*() {.flowCtor: yieldCtor, inlineSuspend: yieldHook.} =
  ## let other tasks run
  blockOn(yieldCtor())

proc spawnPoint*() {.flowCtor: spawnPointCtor, inlineSuspend: spawnHook.} =
  ## a yield that only happens when the run queue is long (see `spawnHighWater`);
  ## outside a flow proc there is nothing to yield from
  discard

# --- fd readiness ----------------------------------------------------------

template selFd(fd: int): untyped =
  ## the handle type the platform's selector takes
  when defined(windows): SocketHandle(fd)
  else: fd.cint                   # exactly what it was before the Windows port

proc syncFd(s: Scheduler, fd: int, st: FdWait) =
  let want = st.evs
  if want == {}:
    if st.registered:
      s.sel.unregister(selFd(fd))
      st.registered = false
    s.fds.del fd
  elif not st.registered:
    s.sel.registerHandle(selFd(fd), want, 0)
    st.registered = true
  else:
    s.sel.updateHandle(selFd(fd), want)

proc dropFdWaiter(fd: int, write: bool) =
  let s {.cursor.} = sched()
  if fd in s.fds:
    let st = s.fds[fd]
    if write:
      if st.wr != nil: dec s.fdWaiting
      st.wr = nil; st.evs.excl Event.Write
    else:
      if st.rd != nil: dec s.fdWaiting
      st.rd = nil; st.evs.excl Event.Read
    s.syncFd(fd, st)

proc ioHook(c: Frame, fd: int, write: bool): Hop =
  cancelGuard(c)
  let p = cast[pointer](c)
  let s {.cursor.} = sched()
  if s.sel == nil: s.sel = newSelector[int]()
  let st = s.fds.mgetOrPut(fd, FdWait())
  if (write and st.wr != nil) or (not write and st.rd != nil):
    c.ex = newException(IOError, "another task already waits on this fd")
    return step(p)
  let t = c.task
  if t != nil:
    t.parked = p; t.parkKind = pkFd; t.parkFd = int32(fd); t.parkWrite = write
  if write: (st.wr = p; st.evs.incl Event.Write)
  else: (st.rd = p; st.evs.incl Event.Read)
  inc s.fdWaiting
  s.syncFd(fd, st)
  noStep

proc readHook*(c: Frame, fd: int): Hop = ioHook(c, fd, false)
proc writeHook*(c: Frame, fd: int): Hop = ioHook(c, fd, true)

proc leafRead(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; readHook(c, c.n)
proc leafWrite(p: pointer): Hop =
  let c = cast[PrimLeaf](p)
  c.fn = doneStage; writeHook(c, c.n)
proc readCtor(fd: int): Frame = PrimLeaf(fn: leafRead, n: fd)
proc writeCtor(fd: int): Frame = PrimLeaf(fn: leafWrite, n: fd)

proc waitReadable*(fd: int) {.flowCtor: readCtor, inlineSuspend: readHook.} =
  ## suspend until `fd` is readable (or hung up)
  blockOn(readCtor(fd))

proc waitWritable*(fd: int) {.flowCtor: writeCtor, inlineSuspend: writeHook.} =
  ## suspend until `fd` is writable
  blockOn(writeCtor(fd))

when defined(linux):
  # --- persistent, edge-triggered descriptors ("PollFd") ---------------------
  # `waitReadable`/`waitWritable` register the fd with epoll for the duration of
  # one wait and unregister it afterwards: two epoll_ctl calls per wait, plus a
  # table lookup and an allocated result list per poll.  A server that handles
  # a request per wakeup cannot afford that.  A `PollFd` is registered ONCE
  # (edge-triggered, for read and write) and keeps two latched readiness bits:
  #   * the event handler sets the bit (and wakes the waiter, if there is one);
  #   * the I/O code clears it when the socket said EAGAIN or returned a short
  #     read (a short read on a stream socket proves it is drained: the next
  #     byte raises a new edge) and then calls `pioWaitRead/Write`, which
  #     returns at once if the bit is set and parks otherwise.
  # Result: a request costs one recv + one send, and the amortised epoll_wait.
  type
    PollFdObj* = object
      fd*: cint
      rdReady*, wrReady*: bool     ## latched readiness (see above); read/write by the owner
      rd, wr: pointer              # parked continuations
      nextFree: pointer
    PollFd* = ptr PollFdObj

  proc pioInit(s: Scheduler) {.noinline.} =
    s.pep = epoll_create1(O_CLOEXEC)
    if s.pep < 0: raiseOSError(osLastError())
    s.pepOn = true
    # nested in the selector so that legacy blocking waits notice persistent events too
    if s.sel == nil: s.sel = newSelector[int]()
    s.sel.registerHandle(s.pep.int, {Event.Read}, 0)
    when flowThreads:
      # the mailbox wake-up must also interrupt a blocking epoll_wait on `pep`
      var ev: EpollEvent
      ev.events = EPOLLIN or EPOLLET
      ev.data.u64 = 0
      let efd = cast[ptr cint](s.shared.wake)[]
      discard epoll_ctl(s.pep, EPOLL_CTL_ADD, efd, addr ev)

  proc pioOpen*(fd: int): PollFd =
    ## register `fd` (must be non-blocking) with this thread's scheduler.  Both
    ## readiness bits start as set: try the syscall first, wait on EAGAIN.
    let s {.cursor.} = sched()
    if not s.pepOn: pioInit(s)
    if s.pfree != nil:
      result = cast[PollFd](s.pfree)
      s.pfree = result.nextFree
      zeroMem(result, sizeof(PollFdObj))
    else:
      result = cast[PollFd](alloc0(sizeof(PollFdObj)))
    result.fd = fd.cint
    result.rdReady = true
    result.wrReady = true
    var ev: EpollEvent
    ev.events = EPOLLIN or EPOLLOUT or EPOLLET or EPOLLRDHUP
    ev.data.`ptr` = result
    if epoll_ctl(s.pep, EPOLL_CTL_ADD, fd.cint, addr ev) < 0:
      let e = osLastError()
      result.nextFree = s.pfree
      s.pfree = cast[pointer](result)
      raiseOSError(e)

  proc pioClose*(p: PollFd) =
    ## close the descriptor and recycle the handle.  Closing removes the fd from
    ## the epoll set (the fd is never dup'ed), so no DEL syscall is needed.
    let s {.cursor.} = sched()
    if p.rd != nil:
      let w = p.rd
      p.rd = nil; dec s.fdWaiting; dec s.pioWaiting
      wake(w)
    if p.wr != nil:
      let w = p.wr
      p.wr = nil; dec s.fdWaiting; dec s.pioWaiting
      wake(w)
    discard posix.close(p.fd)
    p.fd = -1
    p.nextFree = s.pfree
    s.pfree = cast[pointer](p)

  proc pioDrain*() =
    ## free this thread's recycled PollFd handles and close its persistent epoll
    ## (call when the thread is done with all of its PollFds)
    let s {.cursor.} = sched()
    while s.pfree != nil:
      let p = cast[PollFd](s.pfree)
      s.pfree = p.nextFree
      dealloc(p)
    if s.pepOn:
      s.sel.unregister(s.pep.int)
      discard posix.close(s.pep)
      s.pepOn = false

  proc pioDrop(p: PollFd, write: bool) =
    let s {.cursor.} = sched()
    if write:
      if p.wr != nil: (p.wr = nil; dec s.fdWaiting; dec s.pioWaiting)
    else:
      if p.rd != nil: (p.rd = nil; dec s.fdWaiting; dec s.pioWaiting)

  proc pioHook(c: Frame, p: PollFd, write: bool): Hop =
    let pc = cast[pointer](c)
    if (write and p.wrReady) or (not write and p.rdReady): return step(pc)
    cancelGuard(c)
    let s {.cursor.} = sched()
    if (write and p.wr != nil) or (not write and p.rd != nil):
      c.ex = newException(IOError, "another task already waits on this fd")
      return step(pc)
    let t = c.task
    if t != nil:
      t.parked = pc; t.parkKind = pkPio; t.parkRef = cast[pointer](p); t.parkWrite = write
    if write: p.wr = pc else: p.rd = pc
    inc s.fdWaiting; inc s.pioWaiting
    noStep

  proc pioReadHook*(c: Frame, p: PollFd): Hop = pioHook(c, p, false)
  proc pioWriteHook*(c: Frame, p: PollFd): Hop = pioHook(c, p, true)

  proc pioReadLeaf(p: pointer): Hop =
    let c = cast[PrimLeaf](p)
    c.fn = doneStage; pioHook(c, cast[PollFd](c.n), false)
  proc pioWriteLeaf(p: pointer): Hop =
    let c = cast[PrimLeaf](p)
    c.fn = doneStage; pioHook(c, cast[PollFd](c.n), true)
  proc pioReadCtor(p: PollFd): Frame = PrimLeaf(fn: pioReadLeaf, n: cast[int](p))
  proc pioWriteCtor(p: PollFd): Frame = PrimLeaf(fn: pioWriteLeaf, n: cast[int](p))

  proc pioWaitRead*(p: PollFd) {.flowCtor: pioReadCtor, inlineSuspend: pioReadHook.} =
    ## suspend until `p.rdReady` is set (returns at once when it already is)
    blockOn(pioReadCtor(p))

  proc pioWaitWrite*(p: PollFd) {.flowCtor: pioWriteCtor, inlineSuspend: pioWriteHook.} =
    ## suspend until `p.wrReady` is set (returns at once when it already is)
    blockOn(pioWriteCtor(p))

  proc pioDispatch(s: Scheduler, n: int) {.inline.} =
    for i in 0..<n:
      let ev = s.pev[i].events
      let p = cast[PollFd](s.pev[i].data.`ptr`)
      if p == nil: continue                       # the mailbox wake-up
      if (ev and (EPOLLIN or EPOLLRDHUP or EPOLLHUP or EPOLLERR)) != 0:
        p.rdReady = true
        if p.rd != nil:
          let w = p.rd
          p.rd = nil; dec s.fdWaiting; dec s.pioWaiting
          wake(w)
      if (ev and (EPOLLOUT or EPOLLHUP or EPOLLERR)) != 0:
        p.wrReady = true
        if p.wr != nil:
          let w = p.wr
          p.wr = nil; dec s.fdWaiting; dec s.pioWaiting
          wake(w)

proc pollLegacy(s: Scheduler, timeoutMs: int) =
  if s.sel == nil: return
  let evs = s.sel.select(timeoutMs)
  for k in evs:
    let fd = k.fd
    if fd notin s.fds: continue
    let st = s.fds[fd]
    let bad = Event.Error in k.events
    if (Event.Read in k.events or bad or Event.User in k.events) and st.rd != nil:
      let leaf = st.rd
      st.rd = nil; st.evs.excl Event.Read; dec s.fdWaiting
      wake(leaf)
    if (Event.Write in k.events or bad) and st.wr != nil:
      let leaf = st.wr
      st.wr = nil; st.evs.excl Event.Write; dec s.fdWaiting
      wake(leaf)
    s.syncFd(fd, st)

proc pollIo(s: Scheduler, timeoutMs: int) =
  when defined(linux):
    if s.pepOn:
      if s.fdWaiting == s.pioWaiting:
        # only persistent descriptors (the usual server case): one raw epoll_wait,
        # no allocation, no table lookups
        let n = epoll_wait(s.pep, addr s.pev[0], 256, timeoutMs.cint)
        if n > 0: pioDispatch(s, n)
        return
      pollLegacy(s, timeoutMs)
      let n = epoll_wait(s.pep, addr s.pev[0], 256, 0)
      if n > 0: pioDispatch(s, n)
      return
  pollLegacy(s, timeoutMs)

# --- tasks -----------------------------------------------------------------

proc finishTask(t: TaskBase, st: TaskState, err: ref Exception) =
  var dq: WaitQueue = nil
  tlock t:
    t.err = err
    t.state = st
    dq = t.doneq                      # waiters that parked before this point are in it
  t.parked = nil
  t.parkKind = pkNone
  dec sched().live
  if dq != nil: notifyAll(dq)
  if t.grp != nil:
    let g = t.grp
    t.grp = nil                       # break the scope <-> task cycle
    if st == tsFailed and g.failed == nil: g.failed = t
    notifyAll(g.ev)

proc completerStage(p: pointer): Hop =
  let t = cast[TaskBase](p)
  if t.ex != nil:
    let e = popEx(t)
    finishTask(t, (if e of CancelledError: tsCancelled else: tsFailed), e)
  else:
    finishTask(t, tsDone, nil)
  release(p)                  # the pin taken at launch; handles keep the task alive
  noStep

proc prepareLaunch(c: Frame, t: TaskBase): pointer =
  ## returns the pin of the root continuation; the task is pinned too
  c.task = t
  t.fn = completerStage
  t.task = t
  var tp = t                                       # +1 owned by the root's `caller`
  c.caller = pin(tp)
  result = pin(c)

proc launch*(c: sink Frame, t: TaskBase) =
  let p = prepareLaunch(c, t)
  when flowThreads: t.sched = cast[pointer](sched().shared)
  else: t.sched = cast[pointer](sched())
  inc sched().live
  schedule(p)

when flowThreads:
  proc launchOn*(c: sink Frame, t: TaskBase, target: ptr SchedShared) =
    let p = prepareLaunch(c, t)
    t.sched = cast[pointer](target)
    post(target, p)

proc goImpl*[R](c: sink Frame, _: typedesc[R]): Task[R] =
  result = Task[R]()
  when R isnot void:
    c.dest = addr result.value
  launch(c, result)

proc failInline*(t: TaskBase, e: ref Exception) =
  ## outcome of a task that ran to completion inside `go` (see `goInline`)
  t.err = e
  t.state = if e of CancelledError: tsCancelled else: tsFailed

template goInline*(R: typedesc, call: untyped): untyped =
  ## `go` of a flow proc that can never suspend.  Such a task has no
  ## suspension point to interleave at, so running it right away is one of the
  ## schedules `go` allows -- and it needs no continuation, no queue slot and
  ## no scheduler round trip: the result is an already finished `Task`.
  block:
    let flowT = Task[R]()
    try:
      when R is void: call
      else: flowT.value = call
      flowT.state = tsDone
    except Exception as flowE:
      failInline(flowT, flowE)
    flowT

macro go*(call: typed): untyped =
  ## start a flow proc as a concurrent task: `let t = go work(1, 2)`
  var cl = call
  while cl.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtList}: cl = cl[^1]
  if cl.kind notin {nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix}:
    error("go expects a call of a flow proc", call)
  let w = stubCtor(cl[0])
  if w == nil: error("`go` needs a call to a {.flow.} proc", call)
  when not defined(flowNoInlineGo):
    if not isSuspCall(cl[0]):
      return newCall(bindSym"goInline", newCall(ident"typeof", cl), cl)
  let c = newCall(w)
  for a in normArgs(cl): c.add a
  result = newCall(bindSym"goImpl", c, newCall(ident"typeof", cl))

macro prepare*(call: typed): untyped =
  ## build the continuation for a flow call without starting it
  var cl = call
  while cl.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtList}: cl = cl[^1]
  let w = stubCtor(cl[0])
  if w == nil: error("`prepare` needs a call to a {.flow.} proc", call)
  let c = newCall(w)
  for a in normArgs(cl): c.add a
  result = c

proc cancelLocal(t: TaskBase) =
  if t.state != tsPending or t.cancelRequested: return
  t.cancelRequested = true
  if t.parked != nil:
    let leaf = t.parked           # we take over its pin
    t.parked = nil
    let kind = t.parkKind
    t.parkKind = pkNone
    case kind
    of pkQueue: discard removeWaiter(cast[WaitQueue](t.parkQ), leaf)
    of pkAny:
      let st = cast[AnyState](t.parkRef)
      st.fired = true
      for q in st.qs: removeAny(q, st)
      st.qs = @[]
      st.target = nil
    of pkTimer: cancel(cast[Timer](t.parkRef))
    of pkFd: dropFdWaiter(int(t.parkFd), t.parkWrite)
    of pkPio:
      when defined(linux): pioDrop(cast[PollFd](t.parkRef), t.parkWrite)
    of pkNone: discard
    envOf(leaf).ex = newCancelled()
    schedule(leaf)

when flowThreads:
  type CancelReq = ref object of Frame
    victim: TaskBase
  proc cancelReqStage(p: pointer): Hop =
    cancelLocal(cast[CancelReq](p).victim)
    release(p)
    noStep

proc cancel*(t: TaskBase) =
  ## request cancellation; the task sees `CancelledError` at its next
  ## suspension point (or `checkpoint()`). Safe to call from any thread.
  if t.state != tsPending: return
  when flowThreads:
    if t.sched != nil and t.sched != cast[pointer](sched().shared):
      post(cast[ptr SchedShared](t.sched),
           pin(CancelReq(fn: cancelReqStage, victim: t)))
      return
  cancelLocal(t)

proc done*(t: TaskBase): bool = t.state != tsPending
proc failed*(t: TaskBase): bool = t.state == tsFailed
proc cancelled*(t: TaskBase): bool = t.state == tsCancelled

proc waitDone*(t: TaskBase) {.flow.} =
  ## suspend until `t` finished (does not raise)
  while t.state == tsPending:
    parkPending(t)

proc getValue*[T](t: Task[T]): T =
  t.observed = true
  case t.state
  of tsDone:
    when T isnot void: result = t.value
  of tsPending: raise newException(ValueError, "task not finished")
  else: raise t.err

template await*[T](t: Task[T]): T =
  ## wait for a task and return its value (re-raising its exception)
  block:
    let flowT = t
    while flowT.state == tsPending: parkPending(flowT)
    getValue(flowT)

# --- event loop -------------------------------------------------------------

proc runLoop*(until: TaskBase = nil, forever = false) =
  ## drive the scheduler of this thread until `until` is finished (or, with
  ## `forever`, until it is asked to stop -- worker threads).
  let s {.cursor.} = sched()
  while true:
    when flowThreads:
      drainInbox(s)
      if forever and s.shared.stopping.load: break
    if until != nil and until.state != tsPending: break
    if s.wheel.live > 0:
      wheelAdvance(s.wheel, nowMs())
    if s.ready.len > 0:
      let n = s.ready.len
      for _ in 0..<n:
        let c = s.ready.popFirst
        curTaskP = cast[pointer](envOf(c).task)
        inc s.steps
        drive(step(c))
      curTaskP = nil
      if s.fdWaiting > 0: pollIo(s, 0)
      continue
    when flowThreads:
      # idle: block until a timer, an fd or another thread wakes us
      let wait = wheelNextWake(s.wheel)
      if until != nil or forever or s.fdWaiting > 0 or s.wheel.live > 0:
        # Announce that we are about to block, then look at the mailbox one last
        # time: a poster either sees `sleeping` (and triggers the wake-up) or
        # posted early enough for us to see its item here.
        # Grace period: a thread that blocks the instant it runs dry turns every
        # post into two context switches (the consumer is usually faster than
        # the producer).  Yield the CPU a few times first: on one core the
        # producer then runs on and builds a batch, on many cores this is a
        # short spin.
        if s.wheel.live == 0 and s.fdWaiting == 0:
          var spins = 0
          while spins < 16 and inboxEmpty(s.shared) and
                not (forever and s.shared.stopping.load):
            osYield()
            inc spins
          if not inboxEmpty(s.shared): continue
        s.shared.sleeping.store(true)
        if not inboxEmpty(s.shared) or (forever and s.shared.stopping.load):
          s.shared.sleeping.store(false)
          continue
        pollIo(s, wait)
        s.shared.sleeping.store(false)
        continue
      break
    else:
      let wait = wheelNextWake(s.wheel)
      if s.fdWaiting > 0:
        pollIo(s, wait)
        continue
      if s.wheel.live > 0:
        if wait > 0: os.sleep(wait)
        continue
      break
  if until != nil and until.state == tsPending and not forever:
    let what = case until.parkKind
      of pkQueue: "a channel / lock / event that nothing can ever signal"
      of pkAny: "several events (select / any) none of which can fire"
      of pkTimer: "a timer"
      of pkFd, pkPio: "a file descriptor"
      of pkNone: "nothing (it was never resumed)"
    raise newException(DeadlockError,
      "event loop ran out of work but the awaited task is still pending: it is parked on " &
      what & "; " & $s.live & " task(s) are alive and all of them are blocked, " &
      "no timer or I/O is armed")

when flowThreads:
  proc freeShared*(sh: ptr SchedShared) =
    ## free a scheduler's cross-thread part; only after its thread has been joined
    ## (other threads may still be inside `post`/`trigger` until then)
    sh.wake.close()
    release(sh.stub)
    deallocShared(sh)

  proc releaseSched*(keepShared = false) =
    ## free the scheduler of the calling (worker) thread; called on thread exit.
    ## With `keepShared` the mailbox/wake-up event stay allocated for the joiner
    ## to `freeShared`.
    drainPools()
    if theSched == nil: return
    let sh = theSched.shared
    theSched.sel.close()
    theSched = nil
    if not keepShared: freeShared(sh)

proc runUntilIdle*() = runLoop(nil)

proc syncRun(c: sink Frame) {.nimcall.} =
  let t = TaskBase()
  launch(c, t)
  runLoop(t)
  if t.state == tsFailed or t.state == tsCancelled: raise t.err

syncDriver = syncRun

proc runTask*[T](t: Task[T]): T =
  when flowThreads:
    # `t` may live on another thread: wait through a local task so that its
    # completion wakes this scheduler
    let w = goImpl(parkPendingCtor(t), void)
    runLoop(w)
    discard w
  else:
    runLoop(t)
  getValue(t)

macro run*(call: typed): untyped =
  ## run a flow proc to completion on the event loop and return its result
  var cl = call
  while cl.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtList}: cl = cl[^1]
  let sp = newCall(bindSym"go", cl)
  result = newCall(bindSym"runTask", sp)

# --- structured concurrency ------------------------------------------------

type
  Scope* = ref object of GroupBase
    tasks: seq[TaskBase]
    pruneAt: int                       # compact `tasks` once it grows to this size
    joining: bool                      # `join` is walking `tasks`: do not move entries

proc newScope*(): Scope = Scope(ev: newWaitQueue(), pruneAt: 256)

proc prune(g: Scope) =
  ## drop the children that finished successfully: nobody can wait for or cancel
  ## them any more, and each one would otherwise pin its memory until the scope
  ## closes (a scope that spawns a million short tasks holds a million objects)
  var j = 0
  for i in 0..<g.tasks.len:
    if g.tasks[i].state != tsDone:
      if i != j: g.tasks[j] = move g.tasks[i]
      inc j
  g.tasks.setLen(j)
  g.pruneAt = max(256, 2 * j)

proc add*(g: Scope, t: TaskBase) =
  if t.state == tsDone: return         # finished already (see `goInline`): nothing to track
  if g.tasks.len >= g.pruneAt and not g.joining: prune(g)
  g.tasks.add t
  if t.state == tsPending:
    # a child that finishes on this thread reports to the scope directly; one that
    # lives on another thread is simply waited for in order (see `join`)
    when flowThreads:
      if t.sched == cast[pointer](sched().shared): t.grp = g
    else:
      t.grp = g
  elif t.state == tsFailed and g.failed == nil:
    g.failed = t

proc cancel*(g: Scope) =
  for t in g.tasks: cancel(t)

template go*(g: Scope, call: untyped): untyped =
  ## go `call` as a child of the group
  let flowChild = go call
  g.add flowChild
  # a child that cannot suspend ran to completion inside `go` (see `goInline`) and
  # queued nothing: only children that can suspend build up a queue
  when spawnHighWater > 0:
    when not neverSuspends(call): spawnPoint()
  flowChild

proc joinQuiet*(g: Scope) {.flow.} =
  ## wait for every child; never raises
  g.joining = true
  var i = 0
  while i < g.tasks.len:
    waitDone(g.tasks[i])
    inc i

proc join*(g: Scope) {.flow.} =
  ## wait for all children. The first failure (in time, not in spawn order) cancels
  ## the rest (fail-fast) and is re-raised once every child has stopped.
  g.joining = true
  var i = 0
  var err: ref Exception = nil
  while i < g.tasks.len:
    let t = g.tasks[i]
    try:
      if err == nil:
        while t.state == tsPending and g.failed == nil:
          park(g.ev)
      else:
        waitDone(t)
    except CancelledError:
      g.cancel()
      joinQuiet(g)
      raise
    if err == nil and g.failed != nil:
      err = g.failed.err
      g.failed.observed = true
      g.cancel()
      continue                        # now wait for `t` to stop as well
    if t.state == tsPending: continue # a child on another thread: keep waiting
    inc i
  if err != nil: raise err

template scope*(g: untyped, body: untyped) =
  ## structured concurrency scope: all tasks spawned into `g` are finished
  ## (or cancelled when the body fails) before the scope is left.
  let g = newScope()
  var flowOk = false
  try:
    body
    flowOk = true
  finally:
    if flowOk: join(g)
    else:
      g.cancel()
      joinQuiet(g)

# --- timeouts ---------------------------------------------------------------

type TimeoutFlag* = ref object
  fired*: bool
  timer*: Timer

proc startTimeout*(ms: int, q: WaitQueue): TimeoutFlag =
  let f = TimeoutFlag()
  f.timer = addTimer(ms, proc () =
    f.fired = true
    notifyAll(q))
  f

proc doneQueue*(t: TaskBase): WaitQueue =
  tlock t:
    if t.doneq == nil: t.doneq = newWaitQueue()
    result = t.doneq

proc waitFor*(t: TaskBase, ms: int): bool {.flow.} =
  ## wait up to `ms` milliseconds for `t`; returns whether it finished
  let q = t.doneQueue
  let flag = startTimeout(ms, q)
  try:
    while t.state == tsPending and not flag.fired:
      park(q)
  finally:
    cancel(flag.timer)
  result = t.state != tsPending

template withTimeout*(ms: int, call: untyped): untyped =
  ## run `call` (a flow call) as a task and cancel it after `ms` milliseconds,
  ## raising `TimeoutError`
  block:
    let flowT = go call
    if not waitFor(flowT, ms):
      cancel(flowT)
      waitDone(flowT)
      raise newException(TimeoutError, "operation timed out")
    getValue(flowT)
