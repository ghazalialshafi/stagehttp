## stagelane/sync — channels, locks and friends, all built on `park`/`notify`.
import std/[deques, macros, options]
import ./core, ./sched
export options

type
  ChanClosedError* = object of CatchableError
    ## base of both closed-channel errors: catch this to handle either
  SendOnClosedError* = object of ChanClosedError      ## `send` after `close`
  RecvOnClosedError* = object of ChanClosedError      ## `recv` on a closed, drained channel

  ChanBase* = ref object of RootObj
    cap: int                    # < 0: unbounded
    count: int
    closed: bool
    recvq, sendq: WaitQueue
  Chan*[T] = ref object of ChanBase
    buf: Deque[T]

proc newChan*[T](cap = 0): Chan[T] =
  ## `cap` > 0: bounded buffer, `cap` < 0: unbounded. `cap == 0` is treated
  ## as a one-element buffer.
  Chan[T](cap: (if cap == 0: 1 else: cap), buf: initDeque[T](),
          recvq: newWaitQueue(), sendq: newWaitQueue())

proc len*(ch: ChanBase): int = ch.count
proc isClosed*(ch: ChanBase): bool = ch.closed
proc canRecv*(ch: ChanBase): bool = ch.count > 0 or ch.closed
proc canSend*(ch: ChanBase): bool = ch.closed or ch.cap < 0 or ch.count < ch.cap
proc recvQueue*(ch: ChanBase): WaitQueue = ch.recvq
proc sendQueue*(ch: ChanBase): WaitQueue = ch.sendq

template waitSpace*(ch: ChanBase) =
  ## suspend while the channel is full (inlined: no allocation unless it parks)
  while not ch.canSend: park(ch.sendQueue)

template waitData*(ch: ChanBase) =
  ## suspend while the channel is empty
  while not ch.canRecv: park(ch.recvQueue)

proc push*[T](ch: Chan[T], v: sink T) =
  if ch.closed: raise newException(SendOnClosedError, "send on closed channel")
  ch.buf.addLast v
  inc ch.count
  notifyOne(ch.recvq)

proc pop*[T](ch: Chan[T]): T =
  if ch.count == 0:
    raise newException(RecvOnClosedError, "receive on closed, drained channel")
  result = ch.buf.popFirst
  dec ch.count
  notifyOne(ch.sendq)

proc close*(ch: ChanBase) =
  if not ch.closed:
    ch.closed = true
    notifyAll(ch.recvq)
    notifyAll(ch.sendq)

proc trySend*[T](ch: Chan[T], v: sink T): bool =
  if ch.closed or not ch.canSend: return false
  ch.push v
  true

proc tryRecv*[T](ch: Chan[T], v: var T): bool =
  if ch.count == 0: return false
  v = ch.pop()
  true

template send*[T](ch: Chan[T], v: T) =
  ## send, suspending while the channel is full
  block:
    let flowCh = ch
    let flowV = v
    waitSpace(flowCh)
    flowCh.push(flowV)

template recv*[T](ch: Chan[T]): T =
  ## receive, suspending while the channel is empty; raises
  ## `ChanClosedError` once it is closed and drained
  block:
    let flowCh = ch
    waitData(flowCh)
    flowCh.pop()

template recvOpt*[T](ch: Chan[T]): Option[T] =
  ## like `recv` but yields `none` when the channel is closed and drained
  block:
    let flowCh = ch
    waitData(flowCh)
    if flowCh.len == 0: none(T) else: some(flowCh.pop())

template eachRecv*[T](ch: Chan[T], x: untyped, body: untyped) =
  ## receive until the channel is closed and drained -- no exception needed:
  ##
  ## .. code-block:: nim
  ##   eachRecv(jobs, job):
  ##     process(job)          # `break` / `continue` work as in any loop
  block:
    let flowCh = ch
    while true:
      waitData(flowCh)
      if flowCh.len == 0: break
      let x = flowCh.pop()
      body

# --- select ------------------------------------------------------------------

macro select*(body: untyped): untyped =
  ## wait on several channel operations at once:
  ##
  ## .. code-block:: nim
  ##   select:
  ##     jobs.recv(job): echo job
  ##     results.send(42): echo "sent"
  ##     timeout(100): echo "too slow"
  ##     default: echo "nothing ready"   # makes it non-blocking
  var arms: seq[NimNode]
  var defaultBody: NimNode = nil
  var timeoutMs: NimNode = nil
  var timeoutBody: NimNode = nil
  for st in body:
    if st.kind notin {nnkCall, nnkCommand} or st.len < 2 or st[^1].kind != nnkStmtList:
      error("select: expected `chan.recv(x): body`, `chan.send(v): body`, `timeout(ms): body` or `default: body`", st)
    if st[0].kind == nnkIdent and st[0].eqIdent("default"):
      defaultBody = st[^1]
    elif st[0].kind == nnkIdent and st[0].eqIdent("timeout"):
      timeoutMs = st[1]; timeoutBody = st[^1]
    elif st[0].kind == nnkDotExpr and (st[0][1].eqIdent("recv") or st[0][1].eqIdent("send")):
      arms.add st
    else:
      error("select: unsupported arm", st)
  let sel = genSym(nskVar, "sel")
  let qsId = genSym(nskVar, "qs")
  let flag = genSym(nskVar, "tmo")
  let tq = genSym(nskLet, "tq")
  var chans: seq[NimNode]
  result = newStmtList()
  for i, a in arms:
    let cv = genSym(nskLet, "ch")
    result.add newLetStmt(cv, a[0][0])
    chans.add cv
  result.add quote do:
    var `sel` = -1
  if timeoutMs != nil:
    result.add quote do:
      var `flag`: TimeoutFlag = nil
      let `tq` = newWaitQueue()
  # selection loop
  let loopBody = newStmtList()
  var chain = newNimNode(nnkIfStmt)
  for i, a in arms:
    let cv = chans[i]
    let isRecv = a[0][1].eqIdent("recv")
    let cond = if isRecv: newCall(bindSym"canRecv", cv) else: newCall(bindSym"canSend", cv)
    chain.add newTree(nnkElifBranch, cond, newAssignment(sel, newLit(i)))
  if timeoutMs != nil:
    chain.add newTree(nnkElifBranch,
      quote do: `flag` != nil and `flag`.fired,
      newAssignment(sel, newLit(arms.len)))
  var waitQs = newNimNode(nnkBracket)
  for i, a in arms:
    let cv = chans[i]
    waitQs.add (if a[0][1].eqIdent("recv"): newCall(bindSym"recvQueue", cv)
                else: newCall(bindSym"sendQueue", cv))
  if timeoutMs != nil: waitQs.add tq
  if defaultBody != nil:
    chain.add newTree(nnkElse, newAssignment(sel, newLit(arms.len + 1)))
  else:
    var elseBody = newStmtList()
    if timeoutMs != nil:
      elseBody.add quote do:
        if `flag` == nil: `flag` = startTimeout(`timeoutMs`, `tq`)
    elseBody.add newCall(bindSym"waitAny", prefix(waitQs, "@"))
    chain.add newTree(nnkElse, elseBody)
  let wh = newTree(nnkWhileStmt, infix(sel, "<", newLit(0)), newStmtList(chain))
  result.add wh
  if timeoutMs != nil:
    result.add quote do:
      if `flag` != nil: cancel(`flag`.timer)
  let cs = newTree(nnkCaseStmt, sel)
  for i, a in arms:
    let cv = chans[i]
    let b = newStmtList()
    if a[0][1].eqIdent("recv"):
      if a.len == 3:      # chan.recv(x): body
        b.add newLetStmt(a[1], newCall(bindSym"pop", cv))
      else:
        b.add newCall(bindSym"pop", cv)
    else:
      b.add newCall(bindSym"push", cv, a[1])
    b.add a[^1]
    cs.add newTree(nnkOfBranch, newLit(i), b)
  if timeoutBody != nil:
    cs.add newTree(nnkOfBranch, newLit(arms.len), timeoutBody)
  if defaultBody != nil:
    cs.add newTree(nnkOfBranch, newLit(arms.len + 1), defaultBody)
  cs.add newTree(nnkElse, newTree(nnkDiscardStmt, newEmptyNode()))
  result.add cs
  result = newBlockStmt(result)

# --- locks & friends ---------------------------------------------------------

type
  Mutex* = ref object
    locked*: bool
    q*: WaitQueue
  Semaphore* = ref object
    permits*: int
    q*: WaitQueue
  Event* = ref object
    isSet*: bool
    q*: WaitQueue
  WaitGroup* = ref object
    pending*: int
    q*: WaitQueue

proc newMutex*(): Mutex = Mutex(q: newWaitQueue())
template lock*(m: Mutex) =
  ## acquire the mutex, suspending while it is held
  while m.locked: park(m.q)
  m.locked = true
proc tryLock*(m: Mutex): bool =
  if m.locked: false else: (m.locked = true; true)
proc unlock*(m: Mutex) =
  m.locked = false
  notifyOne(m.q)

template withLock*(m: Mutex, body: untyped) =
  let flowM = m
  lock(flowM)
  try:
    body
  finally:
    unlock(flowM)

proc newSemaphore*(permits: int): Semaphore =
  Semaphore(permits: permits, q: newWaitQueue())
template acquire*(s: Semaphore) =
  while s.permits <= 0: park(s.q)
  dec s.permits
proc release*(s: Semaphore) =
  inc s.permits
  notifyOne(s.q)

template withPermit*(s: Semaphore, body: untyped) =
  let flowS = s
  acquire(flowS)
  try:
    body
  finally:
    release(flowS)

proc newEvent*(): Event = Event(q: newWaitQueue())
proc isSet*(e: Event): bool = e.isSet
proc set*(e: Event) =
  e.isSet = true
  notifyAll(e.q)
proc clear*(e: Event) = e.isSet = false
template wait*(e: Event) =
  while not e.isSet: park(e.q)

proc newWaitGroup*(n = 0): WaitGroup = WaitGroup(pending: n, q: newWaitQueue())
proc add*(w: WaitGroup, n = 1) = w.pending += n
proc done*(w: WaitGroup) =
  dec w.pending
  if w.pending <= 0: notifyAll(w.q)
template wait*(w: WaitGroup) =
  while w.pending > 0: park(w.q)
