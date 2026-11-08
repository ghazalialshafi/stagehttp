## stagelane/transform — the continuation-passing-style compiler.
##
## `{.flow.}` procs are first type-checked as ordinary code (under another
## name) and the *typed* AST is handed to `flowTransform`, which
##
##  * lifts every local that lives across a suspension into the environment
##    object (a `ref object of YourFrame`),
##  * lowers control flow (if/case/while/for/block/try/finally/defer/break/
##    continue/return) into a graph of "stages" -- one `nimcall` proc each,
##  * A-normalises expressions so that calls to other flow procs may appear
##    anywhere inside an expression (evaluation order is preserved).
##
## Anything that does not contain a suspension point is copied through
## verbatim, so ordinary Nim code costs nothing.
import std/[macros, strutils, sequtils, tables]
import ./core

var flowCounter {.compileTime.} = 0
proc fresh(base: string): string =
  inc flowCounter
  base & "_" & $flowCounter

type
  Stage = ref object
    id: int                # creation order; `high(int)-1` until started (deferred)
    name: NimNode
    body: NimNode
    frames: seq[Frame]
    checkEx: bool          # prologue re-raises exception from a failed child
    terminated: bool

  Frame = ref object       # a protected region (try/except or try/finally)
    isFinally: bool
    excStage: Stage            # where an escaping exception is sent
    excField: NimNode      # env field holding that exception
    pendField: NimNode     # finally only: pending action selector
    finStage: Stage            # finally only: the stage that runs the finally body
    actions: seq[(Stage, int)]   # finally only: queued jumps (target, depth)

  Loop = ref object        # break / continue target
    label: NimNode         # label symbol or nil
    isLoop: bool
    brk, cont: Stage
    depth: int

  Lifted = object
    sym: NimNode
    field: NimNode
    alias: NimNode         # when set the symbol is replaced by this expression

  VScope = tuple[label: NimNode, isLoop: bool]

  St = ref object
    tType, envName: NimNode
    cId: NimNode          # the borrowed environment (a cursor variable in every stage)
    pId: NimNode          # the raw pin of the running continuation
    fields: seq[(NimNode, NimNode)]
    lifted: seq[Lifted]
    locals: seq[(NimNode, NimNode)]
    stages: seq[Stage]
    cur: Stage
    frames: seq[Frame]
    loops: seq[Loop]
    exitStage: Stage
    resultField: NimNode
    resType: NimNode
    isVoid: bool
    procName: string
    handlerExc: seq[NimNode]   # env fields holding the exception being handled
    direct: bool               # building the plain native version of a pure proc
    declared: seq[NimNode]     # symbols declared inside the proc being transformed
    resultSym: NimNode         # the proc's own implicit `result`
    idCounter: int
    demotable: seq[string]     # env fields that may become plain locals of one stage
    exitBody: NimNode          # code that completes the proc (inlined at return sites)
    pragmas: seq[NimNode]      # enclosing `{.pragma.}:` blocks (re-applied to every emitted statement)

const
  LocalKinds = {nskVar, nskLet, nskTemp, nskForVar, nskParam, nskResult,
                nskLabel, nskConst, nskProc, nskFunc, nskIterator, nskMethod,
                nskTemplate, nskMacro, nskConverter}
  HiddenWrappers = {nnkHiddenStdConv, nnkHiddenSubConv}
  Hidden1 = {nnkHiddenAddr, nnkHiddenDeref, nnkStringToCString,
             nnkCStringToString, nnkObjUpConv, nnkObjDownConv, nnkCheckedFieldExpr,
             nnkChckRange, nnkChckRange64, nnkChckRangeF}
  LiteralKinds = {nnkCharLit..nnkUInt64Lit, nnkFloatLit..nnkFloat128Lit,
                  nnkStrLit..nnkTripleStrLit, nnkNilLit}
  RoutineDefs = {nnkProcDef, nnkFuncDef, nnkMethodDef, nnkIteratorDef,
                 nnkConverterDef, nnkTemplateDef, nnkMacroDef, nnkLambda,
                 nnkDo}

# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

proc cleanName(s: string): string =
  for ch in s:
    if ch in IdentChars: result.add ch
  if result.len == 0 or result[0] in {'0'..'9'}: result = "k" & result

proc collectDecls(n: NimNode, acc: var seq[NimNode]) =
  ## every symbol that is *declared* somewhere inside `n` (variables, loop
  ## variables, labels, handler variables, nested routines and their parameters).
  ## A symbol that is not in this set belongs to the outside world.
  proc add(x: NimNode, acc: var seq[NimNode]) =
    var s = x
    if s.kind == nnkPragmaExpr: s = s[0]
    if s.kind == nnkPostfix: s = s[1]     # `x*` can never be exported from a local
    if s.kind == nnkVarTuple:
      for i in 0..<s.len-2: add(s[i], acc)
    elif s.kind == nnkSym and s notin acc: acc.add s
  case n.kind
  of nnkIdentDefs, nnkVarTuple, nnkForStmt:
    for i in 0..<n.len-2: add(n[i], acc)
  of nnkBlockStmt, nnkBlockExpr: add(n[0], acc)
  of nnkInfix:
    if n.len == 3 and n[0].kind == nnkIdent and n[0].eqIdent("as"): add(n[2], acc)
  of RoutineDefs: add(n[0], acc)
  else: discard
  for ch in n: collectDecls(ch, acc)

proc skipHidden(n: NimNode): NimNode =
  result = n
  while true:
    if result.kind in HiddenWrappers: result = result[1]
    elif result.kind in Hidden1: result = result[0]
    else: break

proc stubCtor*(callee: NimNode): NimNode =
  ## the prepare symbol when `callee` is the stub of a flow proc
  if callee.kind != nnkSym: return nil
  if callee.symKind notin {nskProc, nskFunc, nskMethod}: return nil
  let impl = callee.getImpl
  if impl.kind notin {nnkProcDef, nnkFuncDef, nnkMethodDef}: return nil
  let prag = impl[4]
  if prag.kind != nnkPragma: return nil
  for p in prag:
    if p.kind == nnkExprColonExpr and p[0].eqIdent("flowCtor"):
      return p[1]

proc stubPrim*(callee: NimNode): NimNode =
  ## the inline hook when `callee` is a suspension primitive
  if callee.kind != nnkSym: return nil
  if callee.symKind notin {nskProc, nskFunc}: return nil
  let impl = callee.getImpl
  if impl.kind notin {nnkProcDef, nnkFuncDef}: return nil
  let prag = impl[4]
  if prag.kind != nnkPragma: return nil
  for p in prag:
    if p.kind == nnkExprColonExpr and p[0].eqIdent("inlineSuspend"):
      return p[1]

var analysing {.compileTime.}: Table[string, bool]
  ## procs whose body is being analysed right now -> optimistic purity (recursion)
var purityTable {.compileTime.}: Table[string, bool]
  ## prepare name -> "never suspends": such procs are compiled to native code

proc hasPragmaNamed(prag: NimNode, name: string): NimNode =
  if prag.kind != nnkPragma: return nil
  for p in prag:
    if p.kind == nnkExprColonExpr and p[0].eqIdent(name): return p[1]
    if p.kind in {nnkIdent, nnkSym} and p.eqIdent(name): return p

proc mentionsSym(n, s: NimNode): bool =
  if n.kind == nnkSym: return n == s
  for ch in n:
    if mentionsSym(ch, s): return true

proc isPureBySymbol(callee: NimNode): bool =
  ## Purity is recorded in the symbols themselves, so it survives module
  ## boundaries and compilers that do not re-run our macros: the stub names its
  ## direct proc (`flowDirect`); a *suspending* flow proc's direct proc merely
  ## drives its own constructor (`blockOn(ctor(..))`), a *pure* one holds the
  ## real code and never mentions the constructor.
  let w = stubCtor(callee)
  let impl = callee.getImpl
  if w == nil or impl.kind notin {nnkProcDef, nnkFuncDef}: return false
  let d = hasPragmaNamed(impl[4], "flowDirect")
  if d == nil or d.kind != nnkSym: return false
  let dimpl = d.getImpl
  if dimpl.kind notin {nnkProcDef, nnkFuncDef}: return false
  let body = dimpl[6]
  body.kind != nnkEmpty and not mentionsSym(body, w)

proc isSuspCall*(callee: NimNode): bool =
  ## does calling `callee` possibly suspend?
  let w = stubCtor(callee)
  if w == nil: return false
  if stubPrim(callee) != nil: return true
  if analysing.hasKey($w): return not analysing[$w]
  when not defined(flowNoPurityTable):
    # fast path, and the only source while the proc itself is being analysed
    if purityTable.hasKey($w): return not purityTable[$w]
  not isPureBySymbol(callee)

proc hasSusp(n: NimNode): bool =
  case n.kind
  of RoutineDefs, nnkTypeSection, nnkTypeOfExpr, LiteralKinds, nnkSym, nnkEmpty, nnkIdent:
    return false
  of nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit:
    if isSuspCall(n[0]): return true
  else: discard
  for ch in n:
    if hasSusp(ch): return true

proc isCall(n: NimNode): bool =
  n.kind in {nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit}

proc isMagicBool(n: NimNode, name: string): bool =
  n.kind == nnkInfix and n[0].kind == nnkSym and n[0].eqIdent(name) and
    n[0].symKind == nskProc

# ---------------------------------------------------------------------------
# environment / stages
# ---------------------------------------------------------------------------

proc access(st: St, field: NimNode): NimNode = newDotExpr(st.cId, field)

proc newField(st: St, base: string, typ: NimNode): NimNode =
  result = ident(fresh(cleanName(base)))
  st.fields.add (result, typ)

proc newStage(st: St, frames: seq[Frame], tag = "stage", deferred = false): Stage =
  ## `deferred` stages get their id when they start: they are merge points that
  ## are only ever reached by forward jumps, so jumps to them may be direct calls
  result = Stage(id: (if deferred: high(int) - 1 else: st.idCounter),
               name: ident(fresh(st.procName & "_" & tag)),
               body: newStmtList(), frames: frames)
  if not deferred: inc st.idCounter
  st.stages.add result

proc startStage(st: St, stage: Stage) =
  if stage.id == high(int) - 1:
    stage.id = st.idCounter
    inc st.idCounter
  st.cur = stage
  st.frames = stage.frames

proc alwaysLeaves(n: NimNode): bool =
  ## true when control can never fall off the end of `n`
  case n.kind
  of nnkReturnStmt, nnkRaiseStmt: true
  of nnkStmtList, nnkBlockStmt: n.len > 0 and alwaysLeaves(n[^1])
  of nnkIfStmt:
    var hasElse = false
    for br in n:
      if br.kind == nnkElse: hasElse = true
      if not alwaysLeaves(br[^1]): return false
    hasElse
  of nnkTryStmt:
    # leaves when a `finally` leaves, or when the body and every handler leave
    if n[^1].kind == nnkFinally and alwaysLeaves(n[^1][0]): return true
    if not alwaysLeaves(n[0]): return false
    for i in 1..<n.len:
      if n[i].kind == nnkExceptBranch and not alwaysLeaves(n[i][^1]): return false
    true
  else: false

proc untypedPragma(p: NimNode): NimNode =
  ## a typed pragma list -> something that can be sem-checked again
  ## (`cast(gcsafe)` is a `Cast` node after typing)
  result = newNimNode(nnkPragma, p)
  for x in p:
    if x.kind == nnkCast and x.len == 2: result.add newCall(ident"cast", copyNimTree(x[1]))
    else: result.add copyNimTree(x)

proc emit(st: St, n: NimNode) =
  if st.cur.terminated or n == nil or n.kind == nnkEmpty: return
  var e = n
  if st.pragmas.len > 0 and n.kind notin {nnkVarSection, nnkLetSection, nnkConstSection,
                                           nnkTypeSection, nnkCommentStmt}:
    for i in countdown(st.pragmas.len - 1, 0):
      e = newTree(nnkPragmaBlock, untypedPragma(st.pragmas[i]), newStmtList(e))
  st.cur.body.add e
  if alwaysLeaves(n): st.cur.terminated = true   # whatever follows would be dead code

proc stagePtr(l: Stage): NimNode = newCall(bindSym"stageFn", l.name)

proc sameFrames(a, b: seq[Frame]): bool =
  if a.len != b.len: return false
  for i in 0..<a.len:
    if a[i] != b[i]: return false
  true

proc stepOf(st: St, target: Stage): NimNode =
  newTree(nnkObjConstr, bindSym"Hop",
    newTree(nnkExprColonExpr, ident"fn", stagePtr(target)),
    newTree(nnkExprColonExpr, ident"env", st.pId))

proc plainJump(st: St, target: Stage): NimNode =
  if target.id > st.cur.id and sameFrames(target.frames, st.frames):
    result = newTree(nnkReturnStmt, newCall(target.name, st.pId))
  else:
    result = newStmtList(
      newAssignment(newDotExpr(st.cId, ident"fn"), stagePtr(target)),
      newTree(nnkReturnStmt, stepOf(st, target)))

proc jumpCode(st: St, target: Stage, depth: int, frames: seq[Frame]): NimNode =
  ## code that leaves `frames[depth..^1]` (running finally blocks) and
  ## continues at `target`
  var fin: Frame = nil
  var i = frames.len - 1
  while i >= depth:
    if frames[i].isFinally:
      fin = frames[i]
      break
    dec i
  if fin == nil:
    if target == st.exitStage and depth == 0 and st.exitBody != nil:
      return copyNimTree(st.exitBody)
    return plainJump(st, target)
  var idx = -1
  for k, a in fin.actions:
    if a[0] == target and a[1] == depth: idx = k
  if idx < 0:
    fin.actions.add (target, depth)
    idx = fin.actions.len - 1
  result = newStmtList(
    newAssignment(st.access(fin.pendField), newLit(idx + 2)),
    plainJump(st, fin.finStage))

proc jump(st: St, target: Stage, depth = 0) =
  if st.cur.terminated: return
  st.emit jumpCode(st, target, depth, st.frames)
  st.cur.terminated = true

# ---------------------------------------------------------------------------
# verbatim rebuilding (typed -> fresh, re-typecheckable AST)
# ---------------------------------------------------------------------------

proc isLocal(st: St, s: NimNode): bool =
  s.symKind in LocalKinds and s in st.declared

proc localIdent(st: St, s: NimNode): NimNode =
  for (k, v) in st.locals:
    if k == s: return v
  let nm = if s.symKind == nskResult: "result" else: cleanName(s.strVal)
  result = ident(fresh(nm))
  st.locals.add (s, result)

proc symExpr(st: St, s: NimNode): NimNode =
  for l in st.lifted:
    if l.sym == s:
      if l.alias != nil: return copyNimTree(l.alias)
      return st.access(l.field)
  if s.symKind == nskResult:
    # our own `result` lives in the frame; the implicit result of a nested
    # lambda / template routine stays what it is
    if not st.direct and st.resultField != nil and st.resultSym != nil and s == st.resultSym:
      return st.access(st.resultField)
    return ident"result"
  if st.isLocal(s):
    return st.localIdent(s)
  result = s

proc rb(st: St, n: NimNode, sc: seq[VScope] = @[]): NimNode

proc rbType(st: St, t: NimNode): NimNode =
  if t.kind == nnkBracketExpr and t.len == 2 and t[0].kind in {nnkSym, nnkIdent} and
     t[0].eqIdent("lent"):
    return rbType(st, t[1])
  case t.kind
  of nnkSym, nnkEmpty, nnkIdent: result = t
  of LiteralKinds: result = copyNimNode(t)
  of nnkType: result = rbType(st, t.getTypeInst)
  else:
    result = newNimNode(t.kind, t)
    for ch in t: result.add rbType(st, ch)

proc formalTypes(callee: NimNode): seq[NimNode] =
  ## expanded list of parameter type nodes of a callee symbol
  if callee.kind != nnkSym: return
  if callee.symKind notin {nskProc, nskFunc, nskMethod, nskConverter, nskIterator}:
    return
  let ty = callee.getTypeInst
  if ty.kind != nnkProcTy: return
  for i in 1..<ty[0].len:
    let d = ty[0][i]
    for _ in 0..<(d.len - 2): result.add d[^2]

proc normArgs*(n: NimNode): seq[NimNode] =
  ## logical argument list of a typed call (varargs wrappers spliced)
  let fts = formalTypes(n[0])
  var vstart = -1
  for i, ft in fts:
    if ft.kind == nnkBracketExpr and ft[0].kind in {nnkSym, nnkIdent} and
       ft[0].eqIdent("varargs"):
      vstart = i
  for i in 1..<n.len:
    let a = n[i]
    if vstart >= 0 and i - 1 >= vstart and a.kind in HiddenWrappers and
       a[1].kind == nnkBracket:
      for x in a[1]: result.add x
    else:
      result.add a

proc rbCall(st: St, n: NimNode, sc: seq[VScope]): NimNode =
  result = newNimNode(n.kind, n)
  var callee = n[0]
  if callee.kind in HiddenWrappers + Hidden1: callee = skipHidden(callee)
  result.add rb(st, callee, sc)
  for a in normArgs(n): result.add rb(st, a, sc)

proc rb(st: St, n: NimNode, sc: seq[VScope] = @[]): NimNode =
  case n.kind
  of nnkSym: return symExpr(st, n)
  of nnkEmpty, nnkNone, nnkIdent: return n
  of LiteralKinds: return copyNimNode(n)
  of nnkType: return rbType(st, n.getTypeInst)
  of HiddenWrappers: return rb(st, n[1], sc)
  of Hidden1: return rb(st, n[0], sc)
  of nnkHiddenCallConv:
    result = newNimNode(nnkCall, n)
    result.add rb(st, n[0], sc)
    for i in 1..<n.len: result.add rb(st, n[i], sc)
    return
  of nnkConv:
    return newNimNode(nnkCall, n).add(rbType(st, n[0]), rb(st, n[1], sc))
  of nnkCast:
    return newNimNode(nnkCast, n).add(rbType(st, n[0]), rb(st, n[1], sc))
  of nnkClosure:
    return rb(st, n[0], sc)
  of nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit:
    return rbCall(st, n, sc)
  of nnkDotExpr:
    if n[1].kind == nnkSym and n[1].symKind == nskField:
      return newDotExpr(rb(st, n[0], sc), ident(n[1].strVal))
  of nnkExprColonExpr:
    if n[0].kind == nnkSym and n[0].symKind == nskField:
      return newNimNode(nnkExprColonExpr, n).add(ident(n[0].strVal), rb(st, n[1], sc))
  of nnkStmtListExpr:
    var allEmpty = true
    for i in 0..<n.len-1:
      if n[i].kind != nnkEmpty: allEmpty = false
    if allEmpty: return rb(st, n[^1], sc)
  of nnkBlockStmt, nnkBlockExpr:
    var sc2 = sc
    let lbl = if n[0].kind == nnkSym: n[0] else: nil
    sc2.add((label: lbl, isLoop: false))
    result = newNimNode(n.kind, n)
    result.add rb(st, n[0], sc2)
    for i in 1..<n.len: result.add rb(st, n[i], sc2)
    return
  of nnkWhileStmt, nnkForStmt:
    var sc2 = sc
    sc2.add((label: NimNode(nil), isLoop: true))
    result = newNimNode(n.kind, n)
    for ch in n: result.add rb(st, ch, sc2)
    return
  of nnkBreakStmt:
    if st.direct:
      result = newNimNode(nnkBreakStmt, n)
      for ch in n: result.add rb(st, ch, sc)
      return
    if n[0].kind == nnkSym:
      for s in sc:
        if s.label != nil and s.label == n[0]:
          return newNimNode(nnkBreakStmt, n).add(rb(st, n[0], sc))
      for i in countdown(st.loops.len - 1, 0):
        let lp = st.loops[i]
        if lp.label != nil and lp.label == n[0]:
          return jumpCode(st, lp.brk, lp.depth, st.frames)
      error("break target not found", n)
    else:
      for s in sc:
        if s.isLoop: return n.copyNimNode.add(newEmptyNode())
      for i in countdown(st.loops.len - 1, 0):
        if st.loops[i].isLoop:
          return jumpCode(st, st.loops[i].brk, st.loops[i].depth, st.frames)
      error("`break` outside of a loop", n)
  of nnkContinueStmt:
    if st.direct:
      return newNimNode(nnkContinueStmt, n).add(newEmptyNode())
    for s in sc:
      if s.isLoop: return n.copyNimNode.add(newEmptyNode())
    for i in countdown(st.loops.len - 1, 0):
      if st.loops[i].isLoop:
        return jumpCode(st, st.loops[i].cont, st.loops[i].depth, st.frames)
    error("`continue` outside of a loop", n)
  of nnkReturnStmt:
    if st.direct:
      result = newStmtList()
      if n[0].kind != nnkEmpty: result.add rb(st, n[0], sc)
      result.add newTree(nnkReturnStmt, newEmptyNode())
      return
    result = newStmtList()
    if n[0].kind != nnkEmpty:
      result.add rb(st, n[0], sc)
    result.add jumpCode(st, st.exitStage, 0, st.frames)
    return
  of RoutineDefs:
    result = newNimNode(n.kind, n)
    for i in 0..<min(n.len, 7):
      # an anonymous proc stays anonymous (typed lambdas carry a hidden name)
      if i == 0 and n.kind in {nnkLambda, nnkDo}: result.add newEmptyNode()
      else: result.add rb(st, n[i], sc)
    return
  of nnkFastAsgn:
    result = newNimNode(nnkAsgn, n)
    for ch in n: result.add rb(st, ch, sc)
    return
  else: discard
  result = newNimNode(n.kind, n)
  for ch in n: result.add rb(st, ch, sc)

# ---------------------------------------------------------------------------
# lowering
# ---------------------------------------------------------------------------

proc lower(st: St, n: NimNode, dest: NimNode)
proc flat(st: St, n: NimNode): NimNode

proc typeOf(n: NimNode): NimNode = n.getTypeInst

proc spillable(n: NimNode): bool =
  if n.kind == nnkHiddenAddr: return false
  case n.typeKind
  of ntyVar, ntyOpenArray, ntyVarargs, ntyTypeDesc, ntyVoid,
     ntyNone, ntyStmt, ntyStatic: false
  else: true

proc isPure(n: NimNode): bool =
  n.kind in LiteralKinds + {nnkSym, nnkEmpty, nnkType, nnkIdent}

proc newTemp(st: St, e: NimNode): NimNode =
  let t = typeOf(e)
  result = st.newField("tmp", rbType(st, t))
  st.demotable.add $result

proc spill(st: St, orig: NimNode, rebuilt: NimNode): NimNode =
  let f = st.newTemp(orig)
  st.emit newAssignment(st.access(f), rebuilt)
  result = newCall(bindSym"flowTake", st.access(f))

proc flatOperands(st: St, ops: seq[NimNode], byRef: seq[bool] = @[]): seq[NimNode] =
  ## evaluate operands left to right, hoisting suspension points.  `byRef[i]`
  ## marks operands that are passed to a `var` parameter: they are lvalues and
  ## must never be copied into a temporary.
  var last = -1
  for i, o in ops:
    if hasSusp(o): last = i
  for i, o in ops:
    if i < last:
      if hasSusp(o): result.add flat(st, o)
      elif (i < byRef.len and byRef[i]) or isPure(skipHidden(o)) or not spillable(o):
        result.add rb(st, o)
      else: result.add spill(st, o, rb(st, o))
    elif i == last: result.add flat(st, o)
    else: result.add rb(st, o)

proc callIsVoid(n: NimNode): bool =
  let ty = n[0].getTypeInst
  if ty.kind != nnkProcTy: return n.typeKind in {ntyVoid, ntyNone, ntyEmpty}
  let r = ty[0][0]
  r.kind == nnkEmpty or (r.kind == nnkSym and r.eqIdent("void"))

proc flatCall(st: St, n: NimNode, slot: NimNode): NimNode =
  ## emit a flow call; the value lands in `slot` (an env field) when given,
  ## otherwise in a fresh temporary whose `move` expression is returned.
  let hook = stubPrim(n[0])
  if hook != nil:
    if not callIsVoid(n): error("stagelane: inline primitives must return void", n)
    let args = flatOperands(st, normArgs(n))
    let pc = newCall(hook, st.cId)
    for a in args:
      let tmp = ident(fresh("flowA"))
      st.emit newLetStmt(tmp, a)
      pc.add tmp
    let nxt = st.newStage(st.frames, "after")
    nxt.checkEx = true
    st.emit newCall(bindSym"flowPrim", st.cId, stagePtr(nxt), pc)
    st.cur.terminated = true
    st.startStage(nxt)
    return newEmptyNode()
  let w = stubCtor(n[0])
  var args = flatOperands(st, normArgs(n))
  let call = newCall(w)
  for a in args: call.add a
  let nxt = st.newStage(st.frames, "after")
  nxt.checkEx = true
  let isVoid = callIsVoid(n)
  if isVoid:
    st.emit newCall(bindSym"flowCall", st.cId, stagePtr(nxt), call)
  else:
    var f = slot
    var ret: NimNode = nil
    if f == nil:
      f = st.newTemp(n)
      ret = newCall(bindSym"flowTake", st.access(f))
    st.emit newCall(bindSym"flowCallInto", st.cId, stagePtr(nxt), call, st.access(f))
    result = ret
  st.cur.terminated = true
  st.startStage(nxt)
  if isVoid: result = newEmptyNode()

proc flat(st: St, n: NimNode): NimNode =
  if not hasSusp(n): return rb(st, n)
  case n.kind
  of nnkHiddenStdConv, nnkHiddenSubConv: return flat(st, n[1])
  of Hidden1: return flat(st, n[0])
  of nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit:
    if isSuspCall(n[0]):
      return flatCall(st, n, nil)
    if n.isMagicBool("and") or n.isMagicBool("or"):
      # short-circuit: only evaluate the rhs when needed
      let isAnd = n.isMagicBool("and")
      let tmp = st.newField("sc", ident"bool")
      let l = flat(st, n[1])
      st.emit newAssignment(st.access(tmp), l)
      if hasSusp(n[2]):
        let rhsStage = st.newStage(st.frames, "rhs")
        let after = st.newStage(st.frames, "scend")
        let cond = if isAnd: st.access(tmp)
                   else: newCall(bindSym"not", st.access(tmp))
        st.emit newTree(nnkIfStmt, newTree(nnkElifBranch, cond,
          st.jumpCode(rhsStage, st.frames.len, st.frames)),
          newTree(nnkElse, st.jumpCode(after, st.frames.len, st.frames)))
        st.cur.terminated = true
        st.startStage(rhsStage)
        let r = flat(st, n[2])
        st.emit newAssignment(st.access(tmp), r)
        st.jump(after, st.frames.len)
        st.startStage(after)
      else:
        let r = rb(st, n[2])
        let cond = if isAnd: st.access(tmp)
                   else: newCall(bindSym"not", st.access(tmp))
        st.emit newTree(nnkIfStmt, newTree(nnkElifBranch, cond,
          newAssignment(st.access(tmp), r)))
      return st.access(tmp)
    var callee = skipHidden(n[0])
    var ops = @[callee] & normArgs(n)
    # operands bound to `var` parameters are lvalues: never spill them
    var byRef = @[false]
    for ft in formalTypes(n[0]): byRef.add(ft.kind == nnkVarTy)
    # the callee itself may contain a suspension (rare); treat uniformly
    let f = flatOperands(st, ops, byRef)
    result = newNimNode(n.kind, n)
    for x in f: result.add x
  of nnkHiddenCallConv:
    var ops: seq[NimNode]
    for ch in n: ops.add skipHidden(ch)
    let f = flatOperands(st, ops)
    result = newNimNode(nnkCall, n)
    for x in f: result.add x
  of nnkStmtListExpr:
    for i in 0..<n.len-1: lower(st, n[i], nil)
    return flat(st, n[^1])
  of nnkIfExpr, nnkIfStmt, nnkCaseStmt, nnkBlockExpr, nnkBlockStmt, nnkTryStmt,
     nnkWhenStmt:
    let f = st.newTemp(n)
    lower(st, n, st.access(f))
    return newCall(bindSym"flowTake", st.access(f))
  of nnkDotExpr:
    let f = flatOperands(st, @[n[0]])
    return newDotExpr(f[0], rb(st, n[1]))
  of nnkConv:
    let f = flatOperands(st, @[n[1]])
    return newNimNode(nnkCall, n).add(rbType(st, n[0]), f[0])
  of nnkCast:
    let f = flatOperands(st, @[n[1]])
    return newNimNode(nnkCast, n).add(rbType(st, n[0]), f[0])
  of nnkObjConstr:
    var vals: seq[NimNode]
    for i in 1..<n.len: vals.add n[i][1]
    let f = flatOperands(st, vals)
    result = newNimNode(nnkObjConstr, n)
    result.add rbType(st, n[0])
    for i in 1..<n.len:
      result.add newNimNode(nnkExprColonExpr, n[i]).add(
        ident(n[i][0].strVal), f[i-1])
  of nnkExprColonExpr:
    let f = flatOperands(st, @[n[1]])
    return newNimNode(nnkExprColonExpr, n).add(rb(st, n[0]), f[0])
  of nnkPar, nnkTupleConstr, nnkBracket, nnkCurly, nnkBracketExpr, nnkDerefExpr,
     nnkAddr, nnkRange, nnkCurlyExpr:
    var ops: seq[NimNode]
    for ch in n: ops.add ch
    let f = flatOperands(st, ops)
    result = newNimNode(n.kind, n)
    for x in f: result.add x
  else:
    error("stagelane: a suspension point may not appear inside this kind of expression (" &
          $n.kind & ")", n)

proc declare(st: St, s: NimNode, demote = true, typ: NimNode = nil): NimNode =
  ## lift a local into the environment (it may be demoted again after lowering
  ## if it never crosses a stage boundary).  `typ` overrides the field type
  ## (an `openArray` parameter is stored as an owning `seq`)
  for l in st.lifted:
    if l.sym == s: return l.field
  var s = s
  if s.kind == nnkPostfix: s = s[1]
  let f = st.newField(s.strVal, if typ != nil: typ else: rbType(st, s.getTypeInst))
  st.lifted.add Lifted(sym: s, field: f)
  if demote: st.demotable.add $f
  result = f

proc newExcField(st: St): NimNode =
  st.newField("exc", newTree(nnkRefTy, ident"Exception"))

# --- statements ---------------------------------------------------------------

proc lowerIdentDefs(st: St, d: NimNode, isConst: bool) =
  if d.kind == nnkVarTuple:
    let value = d[^1]
    var lhs = newNimNode(nnkPar)
    for i in 0..<d.len-2:
      lhs.add st.access(st.declare(d[i]))
    let e = flat(st, value)
    st.emit newAssignment(lhs, e)
    return
  let value = d[^1]
  let ns = d.len - 2
  for i in 0..<ns:
    let s = d[i]
    let f = st.declare(s)
    if value.kind == nnkEmpty:
      st.emit newCall(bindSym"reset", st.access(f))
    else:
      let v = skipHidden(value)
      if i == 0 and isCall(v) and isSuspCall(v[0]) and ns == 1 and stubPrim(v[0]) == nil:
        discard flatCall(st, v, f)   # result goes straight into the field
      else:
        let e = flat(st, value)
        st.emit newAssignment(st.access(f), e)

template inBranch(st: St, host: Stage, list: NimNode, code: untyped) =
  ## lower `body` so that its first statements land in `list`, a nested block
  ## of the stage `host`; stages created by suspensions in there take over.
  st.cur = host
  st.frames = host.frames
  host.body = list
  host.terminated = false
  code

proc lowerIfAt(st: St, n: NimNode, i: int, dest: NimNode, after: Stage) =
  let br = n[i]
  if br.kind notin {nnkElifBranch, nnkElifExpr}:
    lower(st, br[0], dest)
    st.jump(after, st.frames.len)
    return
  let cond = flat(st, br[0])
  let host = st.cur
  let thenL = newStmtList()
  let elseL = newStmtList()
  host.body.add newTree(nnkIfStmt, newTree(nnkElifBranch, cond, thenL),
                        newTree(nnkElse, elseL))
  let saved = host.body
  inBranch(st, host, thenL):
    lower(st, br[1], dest)
    st.jump(after, st.frames.len)
  inBranch(st, host, elseL):
    if i + 1 < n.len: lowerIfAt(st, n, i + 1, dest, after)
    else: st.jump(after, st.frames.len)
  host.body = saved
  host.terminated = true

proc lowerIf(st: St, n: NimNode, dest: NimNode) =
  let after = st.newStage(st.frames, "ifend", deferred = true)
  lowerIfAt(st, n, 0, dest, after)
  st.startStage(after)

proc lowerCase(st: St, n: NimNode, dest: NimNode) =
  let sel = flat(st, n[0])
  let after = st.newStage(st.frames, "caseend", deferred = true)
  let host = st.cur
  let cs = newNimNode(nnkCaseStmt, n)
  cs.add sel
  host.body.add cs
  let saved = host.body
  var hasElse = false
  for i in 1..<n.len:
    let br = n[i]
    let nb = newNimNode(br.kind, br)
    for j in 0..<br.len-1: nb.add rb(st, br[j])
    let lst = newStmtList()
    nb.add lst
    cs.add nb
    if br.kind == nnkElse: hasElse = true
    inBranch(st, host, lst):
      lower(st, br[^1], dest)
      st.jump(after, st.frames.len)
  # (no synthetic `else`: a valid `case` without one is exhaustive)
  host.body = saved
  host.terminated = true
  st.startStage(after)

proc lowerWhile(st: St, n: NimNode) =
  let head = st.newStage(st.frames, "while")
  let after = st.newStage(st.frames, "wend", deferred = true)
  st.jump(head, st.frames.len)
  st.startStage(head)
  let cond = flat(st, n[0])
  let host = st.cur
  let bodyL = newStmtList()
  let exitL = newStmtList()
  host.body.add newTree(nnkIfStmt, newTree(nnkElifBranch, cond, bodyL),
                        newTree(nnkElse, exitL))
  let saved = host.body
  inBranch(st, host, bodyL):
    st.loops.add Loop(label: nil, isLoop: true, brk: after, cont: head,
                      depth: st.frames.len)
    lower(st, n[1], nil)
    discard st.loops.pop
    st.jump(head, st.frames.len)
  inBranch(st, host, exitL):
    st.jump(after, st.frames.len)
  host.body = saved
  host.terminated = true
  st.startStage(after)

proc lowerBlock(st: St, n: NimNode, dest: NimNode) =
  let after = st.newStage(st.frames, "bend", deferred = true)
  st.loops.add Loop(label: (if n[0].kind == nnkSym: n[0] else: nil),
                    isLoop: false, brk: after, cont: nil, depth: st.frames.len)
  lower(st, n[1], dest)
  discard st.loops.pop
  st.jump(after, st.frames.len)
  st.startStage(after)

proc iterName(n: NimNode): string =
  let c = skipHidden(n)
  if isCall(c) and c[0].kind == nnkSym: c[0].strVal else: ""

proc lowerFor(st: St, n: NimNode) =
  # `for (a, b) in xs` arrives as a single `VarTuple` loop variable
  let unpack = n.len == 3 and n[0].kind == nnkVarTuple
  var vars: seq[NimNode]
  if unpack:
    for i in 0..<n[0].len-1: vars.add n[0][i]
  else:
    for i in 0..<n.len-2: vars.add n[i]
  let nv = vars.len
  let body = n[^1]
  let it = skipHidden(n[^2])
  let head = st.newStage(st.frames, "for")
  let bodyStage = st.newStage(st.frames, "fbody")
  # `fstep` is only entered from the body (forward) and ends in the back-edge hop:
  # deferring its id makes the jumps into it direct calls instead of driver hops
  let step = st.newStage(st.frames, "fstep", deferred = true)
  let after = st.newStage(st.frames, "fend", deferred = true)
  var stepEmit: proc ()
  let incSym = bindSym"inc"        # resolved here: `bindSym` inside a closure is dynamic
  let name = iterName(it)
  let idxT = ident"int"
  var okIntRange = false
  var rangeIncl = true
  var lo, hi: NimNode
  if it.kind == nnkInfix and it[0].kind == nnkSym and nv == 1 and
     (it[0].eqIdent("..") or it[0].eqIdent("..<")):
    okIntRange = true
    rangeIncl = it[0].eqIdent("..")
    lo = it[1]; hi = it[2]
  elif isCall(it) and nv == 1 and it.len == 3 and name in ["countup"]:
    okIntRange = true; lo = it[1]; hi = it[2]
  # ------------------------------------------------------------------ ranges
  if okIntRange:
    let iv = st.access(st.declare(vars[0]))
    let hiF = st.newField("hi", rbType(st, vars[0].getTypeInst))
    let e = flatOperands(st, @[lo, hi])
    st.emit newAssignment(iv, e[0])
    st.emit newAssignment(st.access(hiF), e[1])
    st.jump(head, st.frames.len)
    st.startStage(head)
    let hiA = st.access(hiF)
    let cond = if rangeIncl: newTree(nnkInfix, ident"<=", iv, hiA)
               else: newTree(nnkInfix, ident"<", iv, hiA)
    st.emit newTree(nnkIfStmt,
      newTree(nnkElifBranch, cond, jumpCode(st, bodyStage, st.frames.len, st.frames)),
      newTree(nnkElse, jumpCode(st, after, st.frames.len, st.frames)))
    st.cur.terminated = true
    stepEmit = proc () =
      st.startStage(step)
      if rangeIncl:
        st.emit newTree(nnkIfStmt,
          newTree(nnkElifBranch, newTree(nnkInfix, ident">=", iv, hiA),
            jumpCode(st, after, st.frames.len, st.frames)))
        st.emit newCall(incSym, iv)
        st.jump(bodyStage, st.frames.len)
      else:
        st.emit newCall(incSym, iv)
        st.jump(head, st.frames.len)
  else:
    # ------------------------------------------------- collections / snapshot
    let ivar = st.newField("idx", idxT)
    let idx = st.access(ivar)
    var coll: NimNode
    var mode = 0          # 0 items, 1 pairs, 2 mitems, 3 mpairs, 4 snapshot
    let argTk = if isCall(it) and it.len == 2: skipHidden(it[1]).typeKind else: ntyNone
    if isCall(it) and it.len == 2 and name in ["items", "pairs", "mitems", "mpairs"] and
       argTk in {ntySequence, ntyArray, ntyString, ntyOpenArray}:
      mode = ["items", "pairs", "mitems", "mpairs"].find(name)
      let a = skipHidden(it[1])
      if a.kind == nnkSym and not st.isLocal(a) or
         (a.kind == nnkSym and st.lifted.len > 0 and (block:
            var found = false
            for l in st.lifted:
              if l.sym == a: found = true
            found)):
        coll = rb(st, a)
      else:
        let f = st.newTemp(it[1])
        st.emit newAssignment(st.access(f), flat(st, it[1]))
        coll = st.access(f)
      st.emit newAssignment(idx, newLit(0))
    else:
      mode = 4
      proc strip(t: NimNode): NimNode =
        if t.kind == nnkVarTy: t[0] else: t
      var elemT: NimNode
      if nv == 1: elemT = rbType(st, strip(vars[0].getTypeInst))
      else:
        elemT = newNimNode(nnkTupleConstr)
        for i in 0..<nv: elemT.add rbType(st, strip(vars[i].getTypeInst))
      let sf = st.newField("snap", newTree(nnkBracketExpr, ident"seq", elemT))
      let tmpNames = (0..<nv).mapIt(ident("flowV" & $it))
      let fl = newNimNode(nnkForStmt)
      if unpack:
        let vt = newNimNode(nnkVarTuple)
        for t in tmpNames: vt.add t
        vt.add newEmptyNode()
        fl.add vt
      else:
        for t in tmpNames: fl.add t
      fl.add flat(st, it)
      var item: NimNode
      if nv == 1: item = tmpNames[0]
      else:
        item = newNimNode(nnkTupleConstr)
        for t in tmpNames: item.add t
      fl.add newCall(newDotExpr(st.access(sf), ident"add"), item)
      st.emit newCall(bindSym"reset", st.access(sf))   # a nested loop re-fills it every time
      st.emit fl
      coll = st.access(sf)
      st.emit newAssignment(idx, newLit(0))
    st.jump(head, st.frames.len)
    st.startStage(head)
    let cond = newTree(nnkInfix, ident"<", idx, newCall(bindSym"len", coll))
    # bind loop variables
    let elem = newTree(nnkBracketExpr, coll, idx)
    var bindStmts = newStmtList()
    case mode
    of 0:
      if unpack and nv > 1:
        var lhs = newNimNode(nnkPar)
        for i in 0..<nv: lhs.add st.access(st.declare(vars[i]))
        bindStmts.add newAssignment(lhs, elem)
      else:
        bindStmts.add newAssignment(st.access(st.declare(vars[0])), elem)
    of 1:
      bindStmts.add newAssignment(st.access(st.declare(vars[0])), copyNimTree(idx))
      bindStmts.add newAssignment(st.access(st.declare(vars[1])), copyNimTree(elem))
    of 2:
      if unpack and nv > 1:
        # `for (a, b) in mitems(xs)`: each name aliases one field of the element in place
        for i in 0..<nv:
          st.lifted.add Lifted(sym: vars[i],
            alias: newTree(nnkBracketExpr, copyNimTree(elem), newLit(i)))
      else:
        st.lifted.add Lifted(sym: vars[0], alias: copyNimTree(elem))
    of 3:
      st.lifted.add Lifted(sym: vars[0], field: ident"_", alias: copyNimTree(idx))
      st.lifted.add Lifted(sym: vars[1], field: ident"_", alias: copyNimTree(elem))
    else:
      if nv == 1:
        bindStmts.add newAssignment(st.access(st.declare(vars[0])), elem)
      else:
        var lhs = newNimNode(nnkPar)
        for i in 0..<nv: lhs.add st.access(st.declare(vars[i]))
        bindStmts.add newAssignment(lhs, elem)
    st.emit newTree(nnkIfStmt,
      newTree(nnkElifBranch, cond, newStmtList(bindStmts,
        jumpCode(st, bodyStage, st.frames.len, st.frames))),
      newTree(nnkElse, jumpCode(st, after, st.frames.len, st.frames)))
    st.cur.terminated = true
    stepEmit = proc () =
      st.startStage(step)
      st.emit newCall(incSym, copyNimTree(idx))
      st.jump(head, st.frames.len)
  # ------------------------------------------------------------- loop body
  st.startStage(bodyStage)
  st.loops.add Loop(label: nil, isLoop: true, brk: after, cont: step,
                    depth: st.frames.len)
  lower(st, body, nil)
  discard st.loops.pop
  st.jump(step, st.frames.len)
  stepEmit()                      # the step stage starts *after* the body (see above)
  st.startStage(after)

proc assignLast(dest, r: NimNode): NimNode =
  case r.kind
  of nnkStmtList:
    result = newNimNode(nnkStmtList, r)
    for i in 0..<r.len-1: result.add r[i]
    if r.len > 0: result.add assignLast(dest, r[^1])
  of nnkReturnStmt, nnkRaiseStmt, nnkBreakStmt, nnkContinueStmt, nnkDiscardStmt,
     nnkAsgn, nnkEmpty:
    result = r
  else:
    result = newAssignment(dest, r)

proc rbInto(st: St, n: NimNode, dest: NimNode): NimNode =
  ## verbatim rebuild of a value-producing statement, storing the value in
  ## `dest` (an lvalue)
  case n.kind
  of nnkStmtList:
    result = newNimNode(nnkStmtList, n)
    for i in 0..<n.len:
      if i == n.len - 1: result.add rbInto(st, n[i], dest)
      else: result.add rb(st, n[i])
  of nnkStmtListExpr:
    result = newNimNode(nnkStmtList, n)
    for i in 0..<n.len:
      if i == n.len - 1: result.add rbInto(st, n[i], dest)
      else: result.add rb(st, n[i])
  of nnkIfStmt, nnkIfExpr:
    result = newNimNode(nnkIfStmt, n)
    for br in n:
      let nb = newNimNode(if br.kind in {nnkElifBranch, nnkElifExpr}: nnkElifBranch else: nnkElse, br)
      for j in 0..<br.len-1: nb.add rb(st, br[j])
      nb.add rbInto(st, br[^1], dest)
      result.add nb
  of nnkCaseStmt:
    result = newNimNode(nnkCaseStmt, n)
    result.add rb(st, n[0])
    for i in 1..<n.len:
      let br = n[i]
      let nb = newNimNode(br.kind, br)
      for j in 0..<br.len-1: nb.add rb(st, br[j])
      nb.add rbInto(st, br[^1], dest)
      result.add nb
  of nnkTryStmt:
    result = newNimNode(nnkTryStmt, n)
    result.add rbInto(st, n[0], dest)
    for i in 1..<n.len:
      let br = n[i]
      if br.kind == nnkExceptBranch:
        let nb = newNimNode(br.kind, br)
        for j in 0..<br.len-1: nb.add rb(st, br[j])
        nb.add rbInto(st, br[^1], dest)
        result.add nb
      else:
        result.add rb(st, br)
  of nnkHiddenStdConv, nnkHiddenSubConv, Hidden1:
    result = rbInto(st, skipHidden(n), dest)
  of nnkReturnStmt, nnkRaiseStmt, nnkBreakStmt, nnkContinueStmt, nnkDiscardStmt,
     nnkAsgn, nnkFastAsgn, nnkEmpty, nnkCommentStmt, nnkWhileStmt, nnkForStmt:
    result = rb(st, n)
  else:
    if n.typeKind in {ntyVoid, ntyNone, ntyStmt} and n.kind in {nnkCall, nnkCommand}:
      result = rb(st, n)
    else:
      result = newAssignment(dest, rb(st, n))

proc lowerTry(st: St, n: NimNode, dest: NimNode) =
  if not hasSusp(n):
    if dest != nil: st.emit rbInto(st, n, dest) else: st.emit rb(st, n)
    return
  let body = n[0]
  var exceptBranches: seq[NimNode]
  var finallyBody: NimNode = nil
  for i in 1..<n.len:
    if n[i].kind == nnkExceptBranch: exceptBranches.add n[i]
    elif n[i].kind == nnkFinally: finallyBody = n[i][0]
  let outer = st.frames
  let afterTry = st.newStage(outer, "tryend", deferred = true)
  var finF: Frame = nil
  var inFin = outer
  if finallyBody != nil:
    let finStage = st.newStage(outer, "finally")
    let finEntry = st.newStage(outer, "finentry")
    finF = Frame(isFinally: true, excStage: finEntry, excField: st.newExcField(),
                 pendField: st.newField("pend", ident"int"), finStage: finStage)
    inFin = outer & @[finF]
    # finEntry: an exception escaped the protected region
    let savedCur = st.cur
    st.startStage(finEntry)
    st.emit newAssignment(st.access(finF.pendField), newLit(1))
    st.emit plainJump(st, finStage)
    finEntry.terminated = true
    st.cur = savedCur
    st.frames = savedCur.frames
  let afterHandlers = if finF != nil: st.newStage(inFin, "handlers_end") else: afterTry
  var X: Frame = nil
  var catchStage: Stage = nil
  var bodyFrames = inFin
  if exceptBranches.len > 0:
    catchStage = st.newStage(inFin, "catch")
    X = Frame(isFinally: false, excStage: catchStage, excField: st.newExcField())
    bodyFrames = inFin & @[X]
  let bodyStage = st.newStage(bodyFrames, "try")
  st.jump(bodyStage, st.frames.len)
  st.startStage(bodyStage)
  lower(st, body, dest)
  st.jump(afterHandlers, inFin.len)
  if catchStage != nil:
    st.startStage(catchStage)
    let exv = st.access(X.excField)
    var chain = newTree(nnkIfStmt)
    var pending: seq[(Stage, NimNode)]
    for br in exceptBranches:
      let hbody = br[^1]
      var tys: seq[NimNode]
      var asVar: NimNode = nil
      for j in 0..<br.len-1:
        let t = br[j]
        if t.kind == nnkInfix:
          tys.add rbType(st, t[1]); asVar = t[2]
        else:
          tys.add rbType(st, t)
      var cond: NimNode = nil
      if tys.len == 0: cond = ident"true"
      else:
        for t in tys:
          let c1 = newTree(nnkInfix, ident"of", copyNimTree(exv), (if t.kind == nnkSym: ident(t.strVal) else: t))
          cond = if cond == nil: c1 else: newTree(nnkInfix, ident"or", cond, c1)
      if hasSusp(hbody):
        let hl = st.newStage(inFin, "handler")
        let act = newStmtList()
        if asVar != nil:
          act.add newAssignment(st.access(st.declare(asVar)),
            newCall(rbType(st, asVar.getTypeInst), copyNimTree(exv)))
        act.add plainJump(st, hl)
        chain.add newTree(nnkElifBranch, cond, act)
        pending.add (hl, hbody)
      else:
        st.handlerExc.add copyNimTree(exv)
        let r = if dest != nil and hbody.typeKind notin {ntyVoid, ntyNone}:
                  rbInto(st, hbody, dest) else: rb(st, hbody)
        discard st.handlerExc.pop
        let excT = newTree(nnkExceptBranch)
        if asVar != nil and tys.len == 1:
          excT.add newTree(nnkInfix, ident"as", tys[0], st.localIdent(asVar))
        else:
          for t in tys: excT.add t
        excT.add r
        chain.add newTree(nnkElifBranch, cond, newTree(nnkTryStmt,
          newStmtList(newTree(nnkRaiseStmt, copyNimTree(exv))), excT))
    chain.add newTree(nnkElse, newTree(nnkRaiseStmt, copyNimTree(exv)))
    st.emit chain
    st.emit plainJump(st, afterHandlers)
    st.cur.terminated = true
    for (hl, hbody) in pending:
      st.startStage(hl)
      st.handlerExc.add copyNimTree(exv)
      lower(st, hbody, dest)
      discard st.handlerExc.pop
      st.jump(afterHandlers, inFin.len)
  if finF != nil:
    st.startStage(afterHandlers)
    st.emit newAssignment(st.access(finF.pendField), newLit(0))
    st.emit plainJump(st, finF.finStage)
    st.cur.terminated = true
    st.startStage(finF.finStage)
    lower(st, finallyBody, nil)
    let disp = newTree(nnkCaseStmt, st.access(finF.pendField))
    disp.add newTree(nnkOfBranch, newLit(0), jumpCode(st, afterTry, outer.len, st.frames))
    disp.add newTree(nnkOfBranch, newLit(1), newStmtList(
      newAssignment(st.access(finF.pendField), newLit(0)),
      newTree(nnkRaiseStmt, st.access(finF.excField))))
    # actions can still be registered while we emit their code (nested
    # finally frames), so iterate by index
    var k = 0
    while k < finF.actions.len:
      let a = finF.actions[k]
      disp.add newTree(nnkOfBranch, newLit(k + 2), newStmtList(
        newAssignment(st.access(finF.pendField), newLit(0)),
        jumpCode(st, a[0], a[1], st.frames)))
      inc k
    disp.add newTree(nnkElse, newTree(nnkDiscardStmt, newEmptyNode()))
    st.emit disp
    st.cur.terminated = true
  st.startStage(afterTry)

proc lowerStmtList(st: St, n: NimNode, dest: NimNode, start = 0) =
  for i in start..<n.len:
    let ch = n[i]
    if st.cur.terminated:
      # dead code after break/continue/return: still type-checked but dropped
      return
    if ch.kind == nnkDefer:
      var rest = newNimNode(nnkStmtList, n)
      for j in i+1..<n.len: rest.add n[j]
      if rest.len == 0: rest.add newTree(nnkDiscardStmt, newEmptyNode())
      let tr = newTree(nnkTryStmt, rest, newTree(nnkFinally, ch[0]))
      lowerTry(st, tr, dest)
      return
    lower(st, ch, (if i == n.len - 1: dest else: nil))

proc lower(st: St, n: NimNode, dest: NimNode) =
  if st.cur.terminated: return
  if n.kind == nnkRaiseStmt and n[0].kind == nnkEmpty and st.handlerExc.len > 0:
    st.emit newTree(nnkRaiseStmt, copyNimTree(st.handlerExc[^1]))
    st.cur.terminated = true
    return
  if not hasSusp(n):
    # verbatim -- but declarations must still be lifted when in lowered scope
    case n.kind
    of nnkVarSection, nnkLetSection:
      for d in n: lowerIdentDefs(st, d, false)
      return
    of nnkConstSection, nnkEmpty, nnkCommentStmt: 
      if n.kind == nnkConstSection: st.emit rb(st, n)
      return
    of nnkStmtList:
      lowerStmtList(st, n, dest)
      return
    else:
      # may contain escapes (break/continue/return) -- rb turns them into jumps
      if dest != nil and n.kind notin {nnkWhileStmt, nnkForStmt}:
        st.emit rbInto(st, n, dest)
      else:
        st.emit rb(st, n)
      return
  case n.kind
  of nnkStmtList: lowerStmtList(st, n, dest)
  of nnkStmtListExpr:
    for i in 0..<n.len-1: lower(st, n[i], nil)
    lower(st, n[^1], dest)
  of nnkVarSection, nnkLetSection:
    for d in n: lowerIdentDefs(st, d, false)
  of nnkAsgn, nnkFastAsgn:
    let lhs = skipHidden(n[0])
    let rhs = skipHidden(n[1])
    if lhs.kind == nnkSym and isCall(rhs) and isSuspCall(rhs[0]) and stubPrim(rhs[0]) == nil:
      let slot = block:
        var s: NimNode = nil
        let e = st.symExpr(lhs)
        if e.kind == nnkDotExpr and e[0] == st.cId: s = e[1]
        s
      if slot != nil:
        discard flatCall(st, rhs, slot)
        return
    let l = if hasSusp(n[0]): flat(st, n[0]) else: rb(st, n[0])
    let r = flat(st, n[1])
    st.emit newAssignment(l, r)
  of nnkDiscardStmt:
    let v = skipHidden(n[0])
    if isCall(v) and isSuspCall(v[0]) and stubPrim(v[0]) == nil:
      # `discard foo()`: no slot needed
      let w = stubCtor(v[0])
      let args = flatOperands(st, normArgs(v))
      let call = newCall(w)
      for a in args: call.add a
      let nxt = st.newStage(st.frames, "after")
      nxt.checkEx = true
      st.emit newCall(bindSym"flowCall", st.cId, stagePtr(nxt), call)
      st.cur.terminated = true
      st.startStage(nxt)
    else:
      let e = flat(st, n[0])
      st.emit newTree(nnkDiscardStmt, e)
  of nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix, nnkCallStrLit:
    let e = flat(st, n)
    if dest != nil and n.typeKind != ntyVoid and e.kind != nnkEmpty:
      st.emit newAssignment(dest, e)
    elif e.kind != nnkEmpty:
      if n.typeKind in {ntyVoid, ntyNone, ntyStmt, ntyEmpty}: st.emit e
      else: st.emit newTree(nnkDiscardStmt, e)
  of nnkIfStmt, nnkIfExpr: lowerIf(st, n, dest)
  of nnkCaseStmt: lowerCase(st, n, dest)
  of nnkWhileStmt: lowerWhile(st, n)
  of nnkForStmt: lowerFor(st, n)
  of nnkBlockStmt, nnkBlockExpr: lowerBlock(st, n, dest)
  of nnkTryStmt: lowerTry(st, n, dest)
  of nnkPragmaBlock:
    # keep the block's pragmas in force for everything emitted from inside it
    st.pragmas.add n[0]
    lower(st, n[^1], dest)
    discard st.pragmas.pop
  of nnkReturnStmt:
    if n[0].kind != nnkEmpty:
      lower(st, n[0], nil)
    st.jump(st.exitStage, 0)
  of nnkRaiseStmt:
    if n[0].kind == nnkEmpty:
      if st.handlerExc.len > 0: st.emit newTree(nnkRaiseStmt, copyNimTree(st.handlerExc[^1]))
      else: st.emit rb(st, n)
    else:
      let e = flat(st, n[0])
      st.emit newTree(nnkRaiseStmt, e)
  of nnkHiddenStdConv, nnkHiddenSubConv, Hidden1:
    lower(st, skipHidden(n), dest)
  else:
    let e = flat(st, n)
    if dest != nil: st.emit newAssignment(dest, e) else: st.emit e

# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------

proc stageProc(st: St, l: Stage, envT: NimNode, forwardOnly: bool): NimNode =
  let params = @[bindSym"Hop", newIdentDefs(st.pId, ident"pointer")]
  var body = newStmtList()
  if forwardOnly:
    body = newEmptyNode()
  else:
    if not l.terminated:
      error("stagelane internal error: stage '" & $l.name & "' is not terminated")
    var inner = newStmtList()
    if l.checkEx:
      inner.add newTree(nnkIfStmt, newTree(nnkElifBranch,
        newTree(nnkInfix, ident"!=", newDotExpr(st.cId, ident"ex"), newNilLit()),
        newTree(nnkRaiseStmt, newCall(bindSym"popEx", st.cId))))
    inner.add l.body
    if l.frames.len > 0:
      let fr = l.frames[^1]
      let exv = ident"flowEx"
      body.add newTree(nnkTryStmt, inner,
        newTree(nnkExceptBranch, newTree(nnkInfix, ident"as", ident"Exception", exv),
          newStmtList(
            newAssignment(st.access(fr.excField), exv),
            newAssignment(newDotExpr(st.cId, ident"fn"), stagePtr(fr.excStage)),
            newTree(nnkReturnStmt, stepOf(st, fr.excStage)))))
    else:
      body = inner
    # borrow the environment: no refcount traffic
    body = newStmtList(
      newTree(nnkLetSection, newIdentDefs(
        newTree(nnkPragmaExpr, st.cId, newTree(nnkPragma, ident"cursor")),
        newEmptyNode(), newTree(nnkCast, envT, st.pId))),
      body)
  result = newTree(nnkProcDef, l.name, newEmptyNode(), newEmptyNode(),
    newTree(nnkFormalParams, params[0], params[1]),
    newTree(nnkPragma, ident"nimcall"), newEmptyNode(), body)

# --- selective lifting ---------------------------------------------------------
# Every local starts out as an environment field.  After lowering we know
# exactly which stages touch which field: a field used by a single stage never has
# to survive a suspension, so it becomes an ordinary stack variable of that stage.

type FieldUse = object
  name: string
  stages: seq[int]
  addrTaken: bool

proc scanUses(n: NimNode, cname: string, stage: int, inAddr: bool,
              uses: var seq[FieldUse], cand: seq[string]) =
  if n.kind == nnkDotExpr and n[0].kind == nnkIdent and n[0].eqIdent(cname) and
     n[1].kind == nnkIdent and $n[1] in cand:
    var idx = -1
    for i, u in uses:
      if u.name == $n[1]: idx = i
    if idx < 0:
      uses.add FieldUse(name: $n[1])
      idx = uses.len - 1
    if stage notin uses[idx].stages: uses[idx].stages.add stage
    if inAddr: uses[idx].addrTaken = true
    return
  var childAddr = inAddr
  case n.kind
  of nnkAddr, nnkHiddenAddr: childAddr = true
  of nnkCall, nnkCommand:
    if n[0].kind in {nnkIdent, nnkSym}:
      let nm = n[0].strVal
      if nm in ["addr", "unsafeAddr", "flowCallInto"]: childAddr = true
  else: discard
  for ch in n:
    scanUses(ch, cname, stage, childAddr, uses, cand)

proc replaceUses(n: NimNode, cname: string, names: seq[string]) =
  for i in 0..<n.len:
    let ch = n[i]
    if ch.kind == nnkDotExpr and ch[0].kind == nnkIdent and ch[0].eqIdent(cname) and
       ch[1].kind == nnkIdent and $ch[1] in names:
      n[i] = ident($ch[1])
    else:
      replaceUses(ch, cname, names)

proc demoteFields(st: St) =
  var uses: seq[FieldUse]
  for li, l in st.stages:
    scanUses(l.body, "flowC", li, false, uses, st.demotable)
  var demoted: seq[string]
  var perStage = newSeq[seq[string]](st.stages.len)
  for u in uses:
    if u.stages.len == 1 and not u.addrTaken:
      demoted.add u.name
      perStage[u.stages[0]].add u.name
  # fields that are never touched at all can simply disappear
  for f in st.demotable:
    var seen = false
    for u in uses:
      if u.name == f: seen = true
    if not seen: demoted.add f
  if demoted.len == 0: return
  for li, l in st.stages:
    replaceUses(l.body, "flowC", demoted)
    var decls = newStmtList()
    for nm in perStage[li]:
      for (f, ty) in st.fields:
        if $f == nm:
          decls.add newTree(nnkVarSection, newIdentDefs(ident(nm), copyNimTree(ty)))
    if decls.len > 0:
      for k in countdown(decls.len - 1, 0): l.body.insert(0, decls[k])
  var keep: seq[(NimNode, NimNode)]
  for (f, ty) in st.fields:
    if $f notin demoted: keep.add (f, ty)
  when defined(flowStats):
    echo st.procName, ": env fields ", st.fields.len, " -> ", keep.len
  st.fields = keep

proc transformImpl(tType, ctorName, ctorParams, directName, directParams,
                   directPragmaList: NimNode, heap: bool, procDef: NimNode,
                   generic: bool): NimNode =
  ## see module docs.  `procDef` is the type-checked body of a flow proc.
  ## `generic`: we are expanding *inside* the constructor of a generic flow proc
  ## (once per instantiation, `procDef` is already concrete): the environment type
  ## and the stages become local to that constructor, which ends with the
  ## environment object itself.
  var directPragma = newEmptyNode()
  if directPragmaList.kind == nnkBracket:
    directPragma = newTree(nnkPragma)
    for p in directPragmaList: directPragma.add p
  var pd = procDef
  if pd.kind == nnkStmtList: pd = pd[0]
  if pd.kind != nnkProcDef:
    error("stagelane: expected a proc definition", procDef)
  let params = pd[3]
  let procName = $pd[0]
  # --- can this proc ever suspend?  (optimistic about itself: recursion) ---
  var isPure = false
  if not generic:       # generic flow procs always suspend-capable (see flowImpl)
    analysing[$ctorName] = not heap
    isPure = (not heap) and not hasSusp(pd[6])
    analysing.del($ctorName)
    purityTable[$ctorName] = isPure
  let st = St(tType: tType, cId: ident"flowC", pId: ident"flowP", procName: procName)
  collectDecls(pd, st.declared)
  if pd.len > 7 and pd[7].kind == nnkSym and pd[7].symKind == nskResult: st.resultSym = pd[7]
  st.envName = ident(fresh("FlowEnv_" & cleanName(procName)))
  # --- result ---
  let retT = params[0]
  st.isVoid = retT.kind == nnkEmpty or
    (retT.kind == nnkSym and retT.eqIdent("void"))
  if not st.isVoid:
    st.resType = rbType(st, retT)
    st.resultField = ident("flowResult")
    st.fields.add (st.resultField, st.resType)
  # --- parameters become fields ---
  var ctorFields: seq[(NimNode, NimNode)]   # field, value the constructor stores
  var refParam = ""     # a `var` parameter: only proc bodies that never suspend can have one
  for i in 1..<params.len:
    let d = params[i]
    let tk = d[^2].typeKind
    for j in 0..<d.len-2:
      let s = d[j]
      case tk
      of ntyVar:
        refParam = s.strVal
      of ntyOpenArray, ntyVarargs:
        # copy-in: the environment owns a snapshot of the elements
        let t = s.getTypeInst
        if t.kind != nnkBracketExpr or t.len != 2:
          error("stagelane: cannot determine the element type of `" & s.strVal & "`", d)
        let f = st.declare(s, demote = false, typ = newTree(nnkBracketExpr, ident"seq", rbType(st, t[1])))
        ctorFields.add (f, newTree(nnkPrefix, ident"@", ident(s.strVal)))
      of ntyTypeDesc, ntyStatic:
        discard   # compile-time metadata: nothing to store, nothing to restore
      else:
        let f = st.declare(s, demote = false)   # initialised by the constructor
        ctorFields.add (f, ident(s.strVal))
  if refParam.len > 0:
    if not isPure:
      error("stagelane: parameter `" & refParam & "` is `var`, which cannot live in a " &
            "suspendable frame; a flow proc that never suspends may take `var` parameters, " &
            "otherwise pass a `ref` (or copy in / copy out through a result)", params)
    # A pure proc is plain native code; there is no environment to build.  It can
    # be called (also from other flow procs) but not spawned.
    let ds = St(direct: true, procName: procName, cId: ident"flowC", pId: ident"flowP")
    collectDecls(pd, ds.declared)
    for i in 1..<params.len:
      for j in 0..<params[i].len-2:
        ds.locals.add (params[i][j], ident(params[i][j].strVal))
    result = newStmtList()
    result.add newTree(nnkProcDef, directName, newEmptyNode(), newEmptyNode(),
      directParams, directPragma, newEmptyNode(), newStmtList(rb(ds, pd[6])))
    result.add newTree(nnkProcDef, ctorName, newEmptyNode(), newEmptyNode(),
      ctorParams, newEmptyNode(), newEmptyNode(), newStmtList(newTree(nnkRaiseStmt,
        newCall(ident"newException", ident"Defect", newLit("stagelane: `" & procName &
          "` has `var` parameters and cannot be spawned; call it directly")))))
    return copyNimTree(result)
  # --- stages ---
  st.exitStage = Stage(id: 1_000_000, name: ident(fresh(procName & "_exit")),
                   body: newStmtList(), frames: @[])
  st.stages.add st.exitStage
  # the code that completes this proc (inlined at every return site)
  let poolable = (not generic) and $tType == "Frame"   # we know every field of the default base
  let poolHead = ident(fresh("flowPoolHead"))
  let poolLen = ident(fresh("flowPoolLen"))
  let recycle = ident(fresh("flowRecycle"))
  let drain = ident(fresh("flowDrain"))
  let poolReg = ident(fresh("flowPoolReg"))
  st.exitBody = newStmtList()
  if st.isVoid:
    if poolable:
      st.exitBody.add newTree(nnkReturnStmt,
        newCall(bindSym"stepOrNone", newCall(recycle, st.pId)))
    else:
      st.exitBody.add newTree(nnkReturnStmt, newCall(bindSym"finish", st.pId))
  else:
    let r = ident"flowRes"
    if poolable:
      st.exitBody.add newTree(nnkBlockStmt, newEmptyNode(), newStmtList(
        newTree(nnkLetSection, newIdentDefs(r, newEmptyNode(),
          newCall(bindSym"flowTake", st.access(st.resultField)))),
        newTree(nnkIfStmt, newTree(nnkElifBranch,
          newTree(nnkInfix, ident"!=", newDotExpr(st.cId, ident"dest"), newNilLit()),
          newAssignment(newTree(nnkDerefExpr,
            newTree(nnkCast, newTree(nnkPtrTy, copyNimTree(st.resType)),
                    newDotExpr(st.cId, ident"dest"))), r))),
        newTree(nnkReturnStmt, newCall(bindSym"stepOrNone", newCall(recycle, st.pId)))))
    else:
      st.exitBody.add newTree(nnkBlockStmt, newEmptyNode(), newStmtList(
        newTree(nnkLetSection, newIdentDefs(r, newEmptyNode(),
          newCall(bindSym"flowTake", st.access(st.resultField)))),
        newTree(nnkReturnStmt, newCall(bindSym"finishWith", st.pId, r))))
  let first = st.newStage(@[], "start")
  st.startStage(first)
  # lower the body
  let body = pd[6]
  if st.isVoid: lower(st, body, nil)
  else: lower(st, body, nil)
  if not st.cur.terminated: st.jump(st.exitStage, 0)
  # exit stage
  st.cur = st.exitStage
  st.frames = @[]
  if st.isVoid:
    st.emit newTree(nnkReturnStmt, newCall(bindSym"finish", st.pId))
  else:
    let r = ident"flowRes"
    st.emit newTree(nnkLetSection, newIdentDefs(r, newEmptyNode(),
      newCall(bindSym"flowTake", st.access(st.resultField))))
    st.emit newTree(nnkReturnStmt, newCall(bindSym"finishWith", st.pId, r))
  st.exitStage.terminated = true
  demoteFields(st)
  # --- assemble ---
  result = newStmtList()
  var recList = newNimNode(nnkRecList)
  for (f, t) in st.fields:
    recList.add newIdentDefs(f, t)
  if recList.len == 0: recList = newEmptyNode()
  let envNameDef =
    when defined(flowAcyclic):
      newTree(nnkPragmaExpr, st.envName, newTree(nnkPragma, ident"acyclic"))
    else: st.envName
  result.add newTree(nnkTypeSection, newTree(nnkTypeDef, envNameDef,
    newEmptyNode(), newTree(nnkRefTy, newTree(nnkObjectTy, newEmptyNode(),
      newTree(nnkOfInherit, tType), recList))))
  for l in st.stages:
    result.add stageProc(st, l, st.envName, true)
  for l in st.stages:
    result.add stageProc(st, l, st.envName, false)
  if generic:
    var ctor = newTree(nnkObjConstr, st.envName,
      newTree(nnkExprColonExpr, ident"fn", stagePtr(first)))
    for (f, p) in ctorFields:
      ctor.add newTree(nnkExprColonExpr, f, p)
    result.add ctor     # the value of the constructor body
    return copyNimTree(result)
  # direct version: native code for pure procs, a synchronous driver otherwise
  block:
    let dparams = directParams
    var dbody = newStmtList()
    if isPure:
      let ds = St(direct: true, procName: procName, cId: ident"flowC", pId: ident"flowP")
      collectDecls(pd, ds.declared)
      for i in 1..<params.len:
        for j in 0..<params[i].len-2:
          ds.locals.add (params[i][j], ident(params[i][j].strVal))
      dbody.add rb(ds, pd[6])
    else:
      let call = newCall(ctorName)
      for i in 1..<params.len:
        for j in 0..<params[i].len-2: call.add ident(params[i][j].strVal)
      if st.isVoid: dbody.add newCall(bindSym"blockOn", call)
      else: dbody.add newAssignment(ident"result",
        newCall(bindSym"blockOn", call, copyNimTree(directParams[0])))
    result.add newTree(nnkProcDef, directName, newEmptyNode(), newEmptyNode(),
      dparams, directPragma, newEmptyNode(), dbody)
  # prepare (reuses a pooled environment when one is available)
  let envT = st.envName
  var inits = newStmtList()
  inits.add newAssignment(newDotExpr(ident"flowE", ident"fn"), stagePtr(first))
  for (f, p) in ctorFields:
    inits.add newAssignment(newDotExpr(ident"flowE", f), p)
  var wbody = newStmtList()
  var poolStmts = newStmtList()
  if poolable:
    poolStmts.add quote do:
      var `poolHead` {.threadvar.}: pointer
      var `poolLen` {.threadvar.}: int
      var `poolReg` {.threadvar.}: bool
    poolStmts.add quote do:
      proc `drain`() {.nimcall.} =
        while `poolHead` != nil:
          let q = `poolHead`
          `poolHead` = envOf(q).next
          envOf(q).next = nil
          dec `poolLen`
          release(q)
    # recycler: reset every field, then park the object on the freelist
    var rbody = newStmtList()
    rbody.add newTree(nnkLetSection, newIdentDefs(
      newTree(nnkPragmaExpr, ident"flowC", newTree(nnkPragma, ident"cursor")),
      newEmptyNode(), newTree(nnkCast, envT, ident"flowP")))
    rbody.add newAssignment(ident"result", newDotExpr(ident"flowC", ident"caller"))
    let fullI = poolLen
    let pI0 = ident"flowP"
    rbody.add quote do:
      if `fullI` >= 1024:                  # pool full: plain free, fields die with the object
        release(`pI0`)
        return
    for (f, ty) in st.fields:
      rbody.add newCall(bindSym"flowClear", newDotExpr(ident"flowC", f))
    let exF = newDotExpr(ident"flowC", ident"ex")
    rbody.add quote do:
      if `exF` != nil: `exF` = nil
    rbody.add newAssignment(newDotExpr(ident"flowC", ident"dest"), newNilLit())
    rbody.add newAssignment(newDotExpr(ident"flowC", ident"caller"), newNilLit())
    rbody.add newAssignment(newDotExpr(ident"flowC", ident"task"), newNilLit())
    let cI = ident"flowC"
    let pI = ident"flowP"
    rbody.add quote do:
      if not `poolReg`:
        `poolReg` = true
        registerDrain(`drain`)
      `cI`.next = `poolHead`
      `poolHead` = `pI`
      inc `poolLen`
    poolStmts.add newTree(nnkProcDef, recycle, newEmptyNode(), newEmptyNode(),
      newTree(nnkFormalParams, ident"pointer", newIdentDefs(ident"flowP", ident"pointer")),
      newEmptyNode(), newEmptyNode(), rbody)
    result.insert(1, poolStmts)
    let eId = ident"flowE"
    let qId = ident"flowQ"
    wbody.add quote do:
      var `eId`: `envT`
      if `poolHead` != nil:
        let `qId` = `poolHead`
        `poolHead` = envOf(`qId`).next
        envOf(`qId`).next = nil
        dec `poolLen`
        copyMem(addr `eId`, unsafeAddr `qId`, sizeof(pointer))   # adopt the pooled pin: no refcount traffic
      else:
        `eId` = `envT`()
    wbody.add inits
    wbody.add newAssignment(ident"result", ident"flowE")
  else:
    var ctor = newTree(nnkObjConstr, st.envName,
      newTree(nnkExprColonExpr, ident"fn", stagePtr(first)))
    for (f, p) in ctorFields:
      ctor.add newTree(nnkExprColonExpr, f, p)
    wbody.add newAssignment(ident"result", ctor)
  result.add newTree(nnkProcDef, ctorName, newEmptyNode(), newEmptyNode(),
    ctorParams, newEmptyNode(), newEmptyNode(), wbody)
  result = copyNimTree(result)   # break node sharing (sem mutates nodes in place)
  when defined(flowDebug):
    echo result.repr

macro flowTransform*(tType: typedesc, ctorName: untyped, ctorParams: untyped,
                     directName: untyped, directParams: untyped, directPragmaList: untyped,
                     heap: static bool, procDef: typed): untyped =
  transformImpl(tType, ctorName, ctorParams, directName, directParams,
                directPragmaList, heap, procDef, false)

macro flowTransformG*(tType: typedesc, procDef: typed): untyped =
  ## the body of the constructor of a generic flow proc
  transformImpl(tType, newEmptyNode(), newEmptyNode(), newEmptyNode(), newEmptyNode(),
                newEmptyNode(), false, procDef, true)

# ---------------------------------------------------------------------------
# the user facing pragma
# ---------------------------------------------------------------------------

proc isCtParam(t: NimNode): bool =
  ## `typedesc[T]` / `static int`: compile-time parameters make a proc generic
  var h = t
  if h.kind in {nnkBracketExpr, nnkCommand, nnkCall} and h.len > 0: h = h[0]
  h.kind in {nnkIdent, nnkSym} and h.strVal.nimIdentNormalize in ["typedesc", "static"]

proc mentionsIdent(n: NimNode, nm: string): bool =
  if n.kind in {nnkIdent, nnkSym}: return n.eqIdent(nm)
  for ch in n:
    if mentionsIdent(ch, nm): return true

proc flowImpl(tType, n: NimNode): NimNode =
  if n.kind notin {nnkProcDef, nnkFuncDef}:
    error("{.flow.} can only be applied to procs", n)
  let nameNode = n[0]
  var plain = nameNode
  if plain.kind == nnkPostfix: plain = plain[1]
  if plain.kind == nnkAccQuoted: plain = plain[0]
  let nm = $plain
  let wname = ident(fresh("flowW_" & cleanName(nm)))
  # prepare: same parameters, returns the continuation base type
  let fp = n[3].copyNimTree
  # a parameter called `_` cannot be forwarded: give it a real name
  var anon = 0
  for i in 1..<fp.len:
    for j in 0..<fp[i].len-2:
      if fp[i][j].kind == nnkIdent and fp[i][j].eqIdent("_"):
        fp[i][j] = ident("flowAnon" & $anon)
        inc anon
  var generic = n[2].kind != nnkEmpty
  for i in 1..<fp.len:
    if isCtParam(fp[i][^2]): generic = true      # typedesc / static: implicitly generic
  let wparams = newTree(nnkFormalParams, tType)
  for i in 1..<fp.len: wparams.add fp[i].copyNimTree
  let gparams = if generic: n[2].copyNimTree else: newEmptyNode()
  let fwd = newTree(nnkProcDef, wname, newEmptyNode(), gparams.copyNimTree,
    wparams.copyNimTree, newEmptyNode(), newEmptyNode(), newEmptyNode())
  let dname = ident(fresh("flowD_" & cleanName(nm)))
  # calling-convention / inlining pragmas belong to the direct proc too; the
  # `nimcall` stages keep their own signature
  var dprag = newEmptyNode()
  if n[4].kind == nnkPragma:
    for p in n[4]:
      let pn = if p.kind == nnkExprColonExpr: p[0] else: p
      if pn.kind == nnkIdent and pn.strVal.nimIdentNormalize in
         ["inline", "noinline", "cdecl", "stdcall", "fastcall", "thiscall", "safecall", "syscall"]:
        if dprag.kind == nnkEmpty: dprag = newTree(nnkBracket)
        dprag.add p.copyNimTree
  var dprList = newEmptyNode()      # the same list as a real pragma node
  if dprag.kind == nnkBracket:
    dprList = newTree(nnkPragma)
    for p in dprag: dprList.add p.copyNimTree
  let dfwd = newTree(nnkProcDef, dname, newEmptyNode(), gparams.copyNimTree,
    fp.copyNimTree, dprList, newEmptyNode(), newEmptyNode())
  var heap = false
  # stub
  let stub = n.copyNimTree
  var prag = newTree(nnkPragma)
  if n[4].kind == nnkPragma:
    for p in n[4]:
      if p.kind == nnkIdent and p.eqIdent("heap"): heap = true
      elif not (p.kind == nnkIdent and p.eqIdent("flow")) and
         not (p.kind == nnkExprColonExpr and p[0].eqIdent("flow")): prag.add p
  prag.add newTree(nnkExprColonExpr, bindSym"flowCtor", wname)
  prag.add newTree(nnkExprColonExpr, bindSym"flowDirect", dname)
  stub[4] = prag
  stub[3] = fp.copyNimTree
  let retT = fp[0]
  let isVoid = retT.kind == nnkEmpty or (retT.kind == nnkIdent and retT.eqIdent("void"))
  let call = newCall(dname)
  for i in 1..<fp.len:
    for j in 0..<fp[i].len-2: call.add ident($fp[i][j])
  if isVoid: stub[6] = newStmtList(call)
  else: stub[6] = newStmtList(newAssignment(ident"result", call))
  if generic:
    # Every explicit generic parameter must be deducible from the arguments: callers
    # reach the constructor through the stub's instantiated symbol only.
    if n[2].kind != nnkEmpty:
      for g in n[2]:
        for j in 0..<g.len-2:
          var seen = false
          for i in 1..<fp.len:
            if mentionsIdent(fp[i][^2], $g[j]): seen = true
          if not seen:
            error("stagelane: generic parameter `" & $g[j] & "` of a flow proc must appear in " &
                  "a parameter type (add `_: typedesc[" & $g[j] & "]`)", g)
    # a generic proc is never "pure": the constructor must always be reachable
    purityTable[$wname] = false
    # The constructor is generic; each instantiation expands `flowTransformG` on a
    # nested, fully typed copy of the body (runtime parameters only -- typedesc /
    # static parameters stay visible from the constructor's own scope).
    let nested = newTree(nnkProcDef, ident(nm & "_flowBody"), newEmptyNode(), newEmptyNode(),
      newTree(nnkFormalParams, fp[0].copyNimTree), newEmptyNode(), newEmptyNode(),
      n[6].copyNimTree)
    for i in 1..<fp.len:
      if not isCtParam(fp[i][^2]): nested[3].add fp[i].copyNimTree
    let ctorDef = newTree(nnkProcDef, wname, newEmptyNode(), gparams.copyNimTree,
      wparams.copyNimTree, newEmptyNode(), newEmptyNode(),
      newStmtList(newCall(bindSym"flowTransformG", tType, nested)))
    let dcall = newCall(wname)
    for i in 1..<fp.len:
      for j in 0..<fp[i].len-2: dcall.add ident($fp[i][j])
    let dbody =
      if isVoid: newStmtList(newCall(bindSym"blockOn", dcall))
      else: newStmtList(newAssignment(ident"result",
              newCall(bindSym"blockOn", dcall, copyNimTree(fp[0]))))
    let dDef = newTree(nnkProcDef, dname, newEmptyNode(), gparams.copyNimTree,
      fp.copyNimTree, dprList.copyNimTree, newEmptyNode(), dbody)
    return newStmtList(fwd, dfwd, stub, ctorDef, dDef)
  # body proc, checked under another name
  let bodyProc = n.copyNimTree
  bodyProc[0] = ident(nm & "_flowBody")
  bodyProc[4] = newEmptyNode()
  # the pragma macro already stripped; keep other pragmas out of the body
  result = newStmtList(fwd, dfwd, stub,
    newCall(bindSym"flowTransform", tType, wname, wparams.copyNimTree, dname,
            fp.copyNimTree, dprag.copyNimTree, newLit(heap), bodyProc))

macro flow*(tType: untyped, n: untyped): untyped =
  ## `proc foo(x: int): int {.flow: MyFrame.} = ...`
  flowImpl(tType, n)

macro flow*(n: untyped): untyped =
  ## `proc foo(x: int): int {.flow.} = ...` -- uses the plain `Frame` base
  flowImpl(ident"Frame", n)

macro neverSuspends*(call: typed): bool =
  ## compile-time query: `true` when the call is a `{.flow.}` proc that is
  ## compiled to plain native code (it can never suspend)
  var cl = call
  while cl.kind in {nnkHiddenStdConv, nnkHiddenSubConv, nnkStmtList}: cl = cl[^1]
  if cl.kind notin {nnkCall, nnkCommand, nnkInfix, nnkPrefix, nnkPostfix} or
     stubCtor(cl[0]) == nil:
    error("neverSuspends expects a call of a {.flow.} proc", call)
  result = newLit(not isSuspCall(cl[0]))
