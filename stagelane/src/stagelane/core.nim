## stagelane/core — runtime heart of the continuation machinery.
##
## A *continuation* is a heap object (`Frame` or a subtype) holding the live
## state of a suspended computation plus `fn`, the next "stage" to execute.
## Stages are plain `nimcall` procs `proc (env: pointer): Hop`; running a
## continuation means calling its stage, which returns the *next step*: a
## `(stage, env)` pair held in two registers.  The `drive` loops on that.
##
## Ownership: a live continuation is owned by exactly one *pin* -- a raw
## pointer that is handed from holder to holder (ready queue, wait queue,
## timer wheel, fd table, the stage that is running).  Moving a pin costs
## nothing: no refcount traffic on any hop.  `finish` releases the pin, which
## frees the environment and everything it holds.  `caller` is a raw pointer to
## the caller, which is itself pinned for as long as the callee runs.

const flowThreads* = defined(flowThreads)
when flowThreads:
  import std/locks
  static:
    doAssert compileOption("threads"), "-d:flowThreads needs --threads:on"
    doAssert defined(gcAtomicArc), "-d:flowThreads needs --mm:atomicArc: task handles, wait queues and channels are shared between threads, and plain ARC/ORC count references non-atomically (single-thread use of stagelane works with plain --mm:arc / --mm:orc)"

type
  TaskState* = enum tsPending, tsDone, tsFailed, tsCancelled
  ParkKind* = enum pkNone, pkQueue, pkAny, pkTimer, pkFd, pkPio

  Hop* = object
    ## what to run next; `fn == nil` means "nothing: parked or finished"
    fn*: StageFn
    env*: pointer

  StageFn* = proc (env: pointer): Hop {.nimcall.}

  Frame* = ref object of RootObj
    ## Root of every continuation type.  User supplied base types
    ## (`{.flow: MyFrame.}`) must inherit from it.
    fn*: StageFn            ## next stage to run
    caller*: pointer         ## caller (a pinned Frame); resumed when we finish
    ex*: ref Exception    ## exception delivered from a failed child
    dest*: pointer        ## where our result must be written (owned by caller)
    next*: pointer        ## intrusive link while queued (see `FrameList`)
    task* {.cursor.}: TaskBase   ## the task this continuation belongs to

  FrameList* = object
    ## intrusive FIFO of pinned continuations, linked through `Frame.next`
    head*, tail*: pointer
    len*: int

  WaitQueue* = ref object
    ## FIFO of parked continuations (see `park`, `notifyOne`, `notifyAll`)
    waiters*: FrameList
    epoch*: int                        ## bumped on every notify (lost-wakeup guard)
    when flowThreads:
      lock*: Lock

  GroupBase* = ref object of RootObj
    ## the part of a `Scope` that tasks need to see: children report here the moment
    ## they finish, so a failure is noticed in completion order, not spawn order
    ev*: WaitQueue                     ## notified whenever a child finishes
    failed*: TaskBase                  ## the first child that failed (by time)

  TaskBase* = ref object of Frame
    ## a task is itself the root continuation's parent: when the root finishes
    ## it resumes the task, whose stage publishes the outcome.
    ## (small fields first: Nim keeps declaration order, so this avoids padding)
    state*: TaskState
    cancelRequested*: bool
    parkKind*: ParkKind                ## what it waits on (for cancellation)
    parkWrite*: bool
    observed*: bool
    parkFd*: int32
    err*: ref Exception
    parked*: pointer                   ## continuation currently parked (alias, not an owner)
    parkQ*: pointer                    ## the WaitQueue it is parked in (borrowed)
    parkRef*: pointer                  ## Timer / AnyState it waits on (borrowed)
    doneq*: WaitQueue                  ## continuations waiting for completion
    sched*: pointer                    ## owning scheduler
    grp*: GroupBase                    ## the scope this task reports to (cleared on finish)

const noStep* = Hop()

var poolDrainers {.threadvar.}: seq[proc () {.nimcall.}]

proc registerDrain*(f: proc () {.nimcall.}) =
  ## environment pools register here (once per thread) so that a thread can
  ## give its pooled memory back when it exits
  poolDrainers.add f

proc drainPools*() =
  for f in poolDrainers: f()
  reset(poolDrainers)

# --- pins ----------------------------------------------------------------------

template envOf*(p: pointer): Frame = cast[Frame](p)
  ## borrow the continuation behind a pin (no refcount traffic)

proc pin*(c: sink Frame): pointer {.inline, nodestroy.} =
  ## turn an owned reference into a pin (the reference's count now belongs to it).
  ## `nodestroy`: the sink parameter is *transferred* to the raw pointer, so the
  ## compiler must not emit a destructor call for it.
  result = cast[pointer](c)

proc unpin*(p: pointer): Frame {.inline.} =
  ## inverse of `pin`: take the pin's reference back (no refcount change)
  copyMem(addr result, unsafeAddr p, sizeof(pointer))

proc release*(p: pointer) {.inline.} =
  ## drop a pin: the environment (and its fields) is freed
  var c = unpin(p)
  discard c

proc releaseChain*(p: pointer) =
  ## drop a pin and the pins of all callers up to the root
  var q = p
  while q != nil:
    let m = envOf(q).caller
    release(q)
    q = m

proc step*(p: pointer): Hop {.inline.} =
  Hop(fn: envOf(p).fn, env: p)

# --- intrusive continuation lists --------------------------------------------

proc addLast*(l: var FrameList, p: pointer) {.inline.} =
  envOf(p).next = nil
  if l.tail == nil: l.head = p
  else: envOf(l.tail).next = p
  l.tail = p
  inc l.len

proc popFirst*(l: var FrameList): pointer {.inline.} =
  ## precondition: `l.len > 0`
  result = l.head
  let n = envOf(result).next
  envOf(result).next = nil
  l.head = n
  if n == nil: l.tail = nil
  dec l.len

proc remove*(l: var FrameList, c: pointer): bool =
  ## unlink `c` (identity); the caller takes over its pin
  var prev: pointer = nil
  var p = l.head
  while p != nil:
    let n = envOf(p).next
    if p == c:
      if prev == nil: l.head = n else: envOf(prev).next = n
      if l.tail == p: l.tail = prev
      envOf(p).next = nil
      dec l.len
      return true
    prev = p
    p = n

proc `=destroy`*(l: var FrameList) =
  while l.len > 0: releaseChain(popFirst(l))

proc `=copy`*(dest: var FrameList, src: FrameList) {.error.}

# ---------------------------------------------------------------------------
# helpers used by generated code
# ---------------------------------------------------------------------------

template stageFn*(p: typed): StageFn = p

proc popEx*(c: Frame): ref Exception {.inline.} =
  ## take the pending exception out of `c`
  result = c.ex
  c.ex = nil

proc unwindTo*(cur: pointer, e: ref Exception): Hop =
  ## An exception escaped a stage of `cur`: free it and hand the exception to the
  ## caller (which re-raises it inside its own try/except regions).  Without a
  ## caller the exception goes to the driver of the drive.
  let m = envOf(cur).caller
  release(cur)
  if m == nil: raise e
  envOf(m).ex = e
  result = step(m)

proc drive*(start: Hop) =
  ## Run stages until a continuation parks or the root finishes.
  var s = start
  var cur: pointer = nil      # the continuation whose stage is running
  while true:
    try:
      while s.fn != nil:
        cur = s.env
        {.cast(gcsafe).}:
          s = s.fn(s.env)
      return
    except Exception as e:
      let ee = e
      s = unwindTo(cur, ee)

proc stepOrNone*(m: pointer): Hop {.inline.} =
  ## resume `m` (a caller) or nothing when the finished continuation was a root
  if m == nil: noStep else: step(m)

proc finish*(p: pointer): Hop =
  ## the continuation at `p` is done: free it and resume its caller
  let m = envOf(p).caller
  release(p)
  if m == nil: noStep else: step(m)

proc finishWith*[R](p: pointer, v: sink R): Hop =
  ## write `v` into the slot our caller provided, then `finish`
  let rp = envOf(p).dest
  if rp != nil:
    cast[ptr R](rp)[] = v
  finish(p)

var syncDriver* {.threadvar.}: proc (c: sink Frame) {.nimcall.}
  ## installed by the scheduler: runs `c` to completion, driving the event loop

proc blockOn*(c: sink Frame) =
  ## drive `c` to completion on the current thread.
  if syncDriver != nil: syncDriver(c)
  else:
    let p = pin(c)
    drive(step(p))

proc blockOn*[R](c: sink Frame; _: typedesc[R]): R =
  var r: R
  c.dest = addr r
  blockOn(c)
  result = move r

# --- tiny helpers used by generated code ------------------------------------

import std/typetraits
template flowTake*(x: untyped): untyped =
  ## move a value out of a field; plain-old-data is just read (no `wasMoved` call)
  when supportsCopyMem(typeof(x)): x else: move(x)

template flowClear*(x: untyped) =
  ## put a field back to its default (what `reset` does, without the call)
  x = default(typeof(x))

# --- marker pragmas -----------------------------------------------------------

template inlineSuspend*(hook: typed) {.pragma.}
  ## inline suspension primitive: `hook(c: Frame, args..): Hop` is called
  ## straight from the stage; the *caller* is the parked continuation

template flowPrim*(c, nxt, call: untyped) =
  c.fn = nxt
  return call

template flowDirect*(direct: typed) {.pragma.}
  ## attached to the stub: names the proc that holds the synchronous version

template flowCtor*(prepare: typed) {.pragma.}
  ## attached to the direct-style stub of every flow proc; the argument is the
  ## constructor ("prepare") that creates the continuation.

template flowCall*(c, nxt, child: untyped) =
  ## suspend `c` (to resume at stage `nxt` when `child` is done) and run `child`.
  ## The freshly built child is adopted as a pin straight away; the fields are
  ## set through a borrowed view, so no owned local (and no destructor, no
  ## exception-cleanup frame) is needed on this hot path.
  let flowChP = pin(child)
  let flowCh {.cursor.} = envOf(flowChP)
  c.fn = nxt
  flowCh.task = c.task
  flowCh.caller = cast[pointer](c)
  return Hop(fn: flowCh.fn, env: flowChP)

template flowCallInto*(c, nxt, child, slot: untyped) =
  let flowChP = pin(child)
  let flowCh {.cursor.} = envOf(flowChP)
  c.fn = nxt
  flowCh.dest = cast[pointer](addr slot)
  flowCh.task = c.task
  flowCh.caller = cast[pointer](c)
  return Hop(fn: flowCh.fn, env: flowChP)

import std/sequtils
template flowSnapshot*(it: untyped): untyped = toSeq(it)
