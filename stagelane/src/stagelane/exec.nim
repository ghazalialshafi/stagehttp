## stagelane/exec — multi-threaded execution (build with
## `-d:flowThreads --threads:on --mm:atomicArc`).
##
## Model: *thread-per-core, task-pinned*.  Every worker thread owns a full
## scheduler (ready queue, timers, epoll).  A task is created on the
## spawning thread, handed to a worker through a lock-protected mailbox and
## then stays on that worker for its whole life; everything it wakes up is
## routed back to the owning thread.  Tasks can be awaited / cancelled from
## any thread and `SharedChan` moves data between them.
when not defined(flowThreads):
  {.error: "stagelane/exec needs -d:flowThreads --threads:on --mm:atomicArc".}

import std/[macros, atomics, locks, deques, selectors]
import ./core, ./transform, ./sched

type
  WorkerArg = object
    shared: ptr SchedShared
    ready: Atomic[bool]
  Pool* = ref object
    n*: int
    args: ptr UncheckedArray[WorkerArg]
    threads: ptr UncheckedArray[Thread[ptr WorkerArg]]
    next: Atomic[int]
    stopped: bool

proc workerMain(a: ptr WorkerArg) {.thread.} =
  {.cast(gcsafe).}:
    let s = sched()
    a.shared = s.shared
    a.ready.store(true)
    runLoop(nil, forever = true)
    releaseSched(keepShared = true)   # `shutdown` frees it after the join

proc newPool*(threads: int): Pool =
  ## start `threads` worker threads
  doAssert threads > 0
  result = Pool(n: threads)
  result.args = cast[ptr UncheckedArray[WorkerArg]](allocShared0(threads * sizeof(WorkerArg)))
  result.threads = cast[ptr UncheckedArray[Thread[ptr WorkerArg]]](
    allocShared0(threads * sizeof(Thread[ptr WorkerArg])))
  for i in 0..<threads:
    createThread(result.threads[i], workerMain, addr result.args[i])
  for i in 0..<threads:
    while not result.args[i].ready.load: osYield()

proc shutdown*(ex: Pool) =
  ## ask every worker to stop (pending work is abandoned) and join them
  if ex.stopped: return
  ex.stopped = true
  for i in 0..<ex.n:
    ex.args[i].shared.stopping.store(true)
    ex.args[i].shared.wake.trigger()
  for i in 0..<ex.n: joinThread(ex.threads[i])
  for i in 0..<ex.n: freeShared(ex.args[i].shared)
  deallocShared(ex.args)
  deallocShared(ex.threads)

const spawnBurst* {.intdefine: "flowSpawnBurst".} = 512
  ## a spawner that posts this many items in a row yields the CPU once, so the
  ## workers can drain (and recycle the memory of) what is queued instead of
  ## the queue growing with the whole burst.  On an idle multi-core machine the
  ## yield returns at once.  0 disables.

var burst {.threadvar.}: int       # posts since this thread last let the workers run

template throttle(ex: Pool) =
  when spawnBurst > 0:
    inc burst
    if burst >= spawnBurst:
      burst = 0
      osYield()

proc goPoolImpl*[R](ex: Pool, idx: int, c: sink Frame, _: typedesc[R]): Task[R] =
  result = Task[R]()
  when R isnot void:
    c.dest = addr result.value
  let i = if idx >= 0: idx mod ex.n else: ex.next.fetchAdd(1) mod ex.n
  launchOn(c, result, ex.args[i].shared)
  throttle(ex)

macro go*(ex: Pool, call: typed): untyped =
  ## run a flow call on a worker (round robin): `let t = ex.go work(1)`
  var cl = call
  while cl.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtList}: cl = cl[^1]
  let w = stubCtor(cl[0])
  if w == nil: error("`go` needs a call to a {.flow.} proc", call)
  let c = newCall(w)
  for a in normArgs(cl): c.add a
  result = newCall(bindSym"goPoolImpl", ex, newLit(-1), c, newCall(ident"typeof", cl))

proc spawnPoolImpl*(ex: Pool, idx: int, c: sink Frame) =
  ## fire-and-forget: no `Task` handle, no completion bookkeeping.  The frame runs
  ## on a worker and is freed when it finishes.  An exception that escapes it is
  ## not caught by anyone (like an unhandled exception in a thread).
  let i = if idx >= 0: idx mod ex.n else: ex.next.fetchAdd(1) mod ex.n
  post(ex.args[i].shared, pin(c))
  throttle(ex)

macro spawn*(ex: Pool, call: typed): untyped =
  ## start a flow call on a worker *without* a result handle: `ex.spawn work(1)`.
  ## Cheaper than `go` (one allocation, no completion state); use a `Latch`
  ## or a channel when you need to know that the work is done.
  var cl = call
  while cl.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtList}: cl = cl[^1]
  let w = stubCtor(cl[0])
  if w == nil: error("`spawn` needs a call to a {.flow.} proc", call)
  let c = newCall(w)
  for a in normArgs(cl): c.add a
  result = newCall(bindSym"spawnPoolImpl", ex, newLit(-1), c)

macro goAt*(ex: Pool, worker: int, call: typed): untyped =
  ## like `go` but pinned to a specific worker index
  var cl = call
  while cl.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtList}: cl = cl[^1]
  let w = stubCtor(cl[0])
  if w == nil: error("`goAt` needs a call to a {.flow.} proc", call)
  let c = newCall(w)
  for a in normArgs(cl): c.add a
  result = newCall(bindSym"goPoolImpl", ex, worker, c, newCall(ident"typeof", cl))

# --- thread-safe channel ----------------------------------------------------

type
  SharedChanClosed* = object of CatchableError
  ChanOp* = enum coOk, coWouldBlock, coClosed
  SharedChan*[T] = ref object
    lock: Lock
    buf: Deque[T]
    cap: int
    closed: bool
    recvq*, sendq*: WaitQueue

proc newSharedChan*[T](cap = 1): SharedChan[T] =
  ## bounded MPMC channel (`cap` < 0: unbounded) usable from every thread
  result = SharedChan[T](buf: initDeque[T](), cap: cap,
                         recvq: newWaitQueue(), sendq: newWaitQueue())
  initLock(result.lock)

proc tryPush*[T](ch: SharedChan[T], v: var T): ChanOp =
  withLock ch.lock:
    if ch.closed: return coClosed
    if ch.cap >= 0 and ch.buf.len >= ch.cap: return coWouldBlock
    ch.buf.addLast move(v)
  notifyOne(ch.recvq)
  coOk

proc tryPop*[T](ch: SharedChan[T], v: var T): ChanOp =
  withLock ch.lock:
    if ch.buf.len == 0:
      return (if ch.closed: coClosed else: coWouldBlock)
    v = ch.buf.popFirst
  notifyOne(ch.sendq)
  coOk

proc close*[T](ch: SharedChan[T]) =
  withLock ch.lock:
    ch.closed = true
  notifyAll(ch.recvq)
  notifyAll(ch.sendq)

proc len*[T](ch: SharedChan[T]): int =
  withLock ch.lock:
    result = ch.buf.len

template send*[T](ch: SharedChan[T], v: T) =
  ## send, suspending while full; raises `SharedChanClosed` when closed
  block:
    let flowCh = ch
    var flowV = v
    var flowDone = false
    while not flowDone:
      let flowE = epochOf(flowCh.sendq)
      case flowCh.tryPush(flowV)
      of coOk: flowDone = true
      of coClosed: raise newException(SharedChanClosed, "send on closed channel")
      of coWouldBlock: parkSince(flowCh.sendq, flowE)

template recv*[T](ch: SharedChan[T]): T =
  ## receive, suspending while empty; raises `SharedChanClosed` once drained
  block:
    let flowCh = ch
    var flowV: T
    var flowDone = false
    while not flowDone:
      let flowE = epochOf(flowCh.recvq)
      case flowCh.tryPop(flowV)
      of coOk: flowDone = true
      of coClosed: raise newException(SharedChanClosed, "channel closed and drained")
      of coWouldBlock: parkSince(flowCh.recvq, flowE)
    flowV

# --- countdown latch ----------------------------------------------------------

type Latch* = ref object
  ## thread-safe countdown: `countDown` from any thread / task, `wait` in a flow proc
  remaining: Atomic[int]
  q: WaitQueue

proc newLatch*(n: int): Latch =
  result = Latch(q: newWaitQueue())
  result.remaining.store(n)

proc countDown*(l: Latch, n = 1) =
  if l.remaining.fetchSub(n) <= n: notifyAll(l.q)

proc pending*(l: Latch): int = l.remaining.load()
proc queue*(l: Latch): WaitQueue = l.q

template wait*(l: Latch) =
  ## suspend until the count reached zero
  block:
    let flowL = l
    while flowL.pending > 0:
      let flowE = epochOf(flowL.queue)
      if flowL.pending > 0: parkSince(flowL.queue, flowE)
