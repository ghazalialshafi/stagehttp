## stagehttp -- a Stagelane-powered HTTP/1.1 server for GuildenStern.
##
## Architecture (M OS threads x N tasks):
##
##  * M worker threads, each with its own Stagelane scheduler (thread-per-core,
##    shared-nothing).  Every worker owns an `SO_REUSEPORT` listener, so the
##    kernel spreads new connections over the workers; a connection never
##    leaves the worker that accepted it, so there is no locking, no hand-off
##    queue and no cross-thread wake-up on the request path.
##  * One Stagelane task per connection (N per worker).  A semaphore holds the
##    task limit: at the limit the worker stops calling accept() and the kernel
##    backlog absorbs the burst (back-pressure), see `maxConns`.
##  * Sockets are persistent, edge-triggered `PollFd`s (registered once; see
##    stagelane/sched).  A keep-alive request costs one recv() and one send();
##    there is no epoll_ctl, no recv()->EAGAIN probe and no allocation.
##  * Requests are parsed in place (`Span` views into the read buffer).  Reads
##    land in a per-worker scratch buffer that is *leased* only while a request
##    is being processed, so an idle connection holds no buffer at all.
##    Pipelined requests are answered with a single send().
##  * Handlers are ordinary procs - or `{.flow.}` procs that may pause (timers,
##    channels, other sockets) without blocking the worker.  A handler that
##    never pauses compiles to a plain native call.
##
## Usage:
##    import guildenstern/stagehttp
##    proc onRequest(req: Request, res: Response) =      # or {.flow.}
##      if req.isPath("/hello"): res.sendText("Hello, World!")
##      else: res.send(404, "not found")
##    httpServer(serve, onRequest)
##    serve(ServerConfig(port: 8080))
import std/[posix, os, atomics, times, strutils]
from std/osproc import countProcessors
import stagelane, stagelane/sched, stagelane/sync
export stagelane

{.push checks: off, boundChecks: off, overflowChecks: off.}

const
  ScratchSize* = 64 * 1024
  TCP_DEFER_ACCEPT = 9.cint
  SOCK_NB = 0o4000.cint
  SOCK_CE = 0o2000000.cint

proc accept4(s: cint, a: ptr SockAddr, l: ptr SockLen, flags: cint): cint
  {.importc: "accept4", header: "<sys/socket.h>".}
proc memchr(s: pointer, c: cint, n: csize_t): pointer {.importc, header: "<string.h>".}
proc sendfile(outFd, inFd: cint, off: ptr int64, count: csize_t): int
  {.importc: "sendfile", header: "<sys/sendfile.h>".}

type
  ConnectionClosed* = object of IOError

  HttpMethod* = enum hmGet, hmPost, hmPut, hmDelete, hmHead, hmOptions, hmPatch, hmOther

  Span* = object
    ## non-owning view of bytes inside the connection's read buffer; valid only
    ## until the handler returns (copy with `$`)
    p*: ptr UncheckedArray[char]
    n*: int

  Request* = ref object
    meth*: HttpMethod
    target*: Span            ## the raw request target, e.g. /a/b?x=1
    path*: Span              ## the part of target before '?'
    query*: Span             ## the part after '?', without it
    headers*: Span           ## raw header block (use `header`)
    body*: Span
    contentLength*: int
    keepAlive*: bool
    http10*: bool
    expectContinue: bool
    hdrEnd: int

  Response* = ref object
    pf: PollFd
    fd: cint
    ob: ptr UncheckedArray[char]
    olen, ocap, osent: int
    obHeap: bool
    date: ptr UncheckedArray[char]       # "Date: ...\r\n" (37 bytes) or nil
    responded*: bool
    closeAfter*: bool                    ## close the connection after this response
    headOnly: bool
    chunked: bool
    ffd: cint                            # pending sendfile
    foff: int64
    fleft: int
    xh: string                           # extra headers added with `header`

  ServerConfig* = object
    host*: string
    port*: int
    workers*: int            ## M: OS threads (0 = one per CPU)
    maxConns*: int           ## N: live connection tasks per worker (back-pressure); 0 = 10000
    backlog*: int            ## 0 = 4096
    maxHeaderBytes*: int     ## 0 = 16 KiB
    maxBodyBytes*: int       ## 0 = 1 MiB
    idleTimeoutSec*: int     ## close connections idle this long; 0 = 30
    sendDate*: bool          ## add a (cached) Date header
    noDelay*: bool

  Conn* = ref object
    pf*: PollFd
    fd*: cint
    busy*: bool
    working*: bool
    lastTick*: int
    rb: ptr UncheckedArray[char]
    rcap, rlen, rpos: int
    carry: ptr UncheckedArray[char]      # unconsumed request bytes between wake-ups
    carryCap, carryLen: int
    scanFrom: int
    need: int                            # bytes needed from rpos to complete the pending request (0 = unknown)
    req*: Request
    res*: Response
    closing*: bool
    sentContinue: bool

  Worker* = ref object
    id*: int
    cfg*: ServerConfig
    lfd: cint
    lpf: PollFd
    sem: Semaphore
    active*: int
    conns: seq[Conn]
    freeConns: seq[Conn]
    scratchIn, scratchOut: ptr UncheckedArray[char]
    inBusy, outBusy: bool
    tick*: int
    date: ptr UncheckedArray[char]
    served*: int

# ---------------------------------------------------------------------------
# Span helpers
# ---------------------------------------------------------------------------

proc len*(s: Span): int {.inline.} = s.n
proc `$`*(s: Span): string =
  result = newString(s.n)
  if s.n > 0: copyMem(addr result[0], s.p, s.n)
proc `==`*(s: Span, t: string): bool {.inline.} =
  s.n == t.len and (s.n == 0 or equalMem(s.p, unsafeAddr t[0], s.n))
proc startsWith*(s: Span, t: string): bool {.inline.} =
  s.n >= t.len and (t.len == 0 or equalMem(s.p, unsafeAddr t[0], t.len))
proc `[]`*(s: Span, i: int): char {.inline.} = s.p[i]
proc slice*(s: Span, a, b: int): Span {.inline.} =
  ## bytes a..<b of s
  Span(p: cast[ptr UncheckedArray[char]](addr s.p[a]), n: b - a)

const tokTab = block:
  var t: array[256, char]            # lower-cased token char, or '\0' if not a token char
  for c in 0..255:
    let ch = char(c)
    if ch in {'a'..'z', '0'..'9', '!', '#', '$', '%', '&', '\'', '*', '+', '-', '.', '^', '_', '`', '|', '~'}:
      t[c] = ch
    elif ch in {'A'..'Z'}: t[c] = char(c + 32)
  t

proc eqLower(p: ptr UncheckedArray[char], i, n: int, lit: static string): bool {.inline.} =
  ## `lit` is lower case; the bytes at p[i..<i+n] were already validated as token chars
  if n != lit.len: return false
  for k in 0 ..< lit.len:
    if tokTab[p[i + k].int] != lit[k]: return false
  true

proc hasToken(p: ptr UncheckedArray[char], i, n: int, lit: static string): bool =
  ## comma separated list contains `lit` (case-insensitive)
  var a = i
  let e = i + n
  while a < e:
    var b = a
    while b < e and p[b] != ',': inc b
    var x = a
    var y = b
    while x < y and (p[x] == ' ' or p[x] == '\t'): inc x
    while y > x and (p[y - 1] == ' ' or p[y - 1] == '\t'): dec y
    if y - x == lit.len:
      var ok = true
      for k in 0 ..< lit.len:
        if (p[x + k].byte or 0x20'u8) != lit[k].byte: ok = false; break
      if ok: return true
    a = b + 1
  false

# ---------------------------------------------------------------------------
# Request helpers for handlers
# ---------------------------------------------------------------------------

proc isPath*(req: Request, s: string): bool {.inline.} = req.path == s
proc pathStarts*(req: Request, s: string): bool {.inline.} = req.path.startsWith(s)
proc isMethod*(req: Request, m: HttpMethod): bool {.inline.} = req.meth == m

proc header*(req: Request, name: static string): Span =
  ## case-insensitive header lookup, no allocation (`name` in lower case); empty Span if absent
  let h = req.headers
  var i = 0
  while i < h.n:
    var j = i
    while j < h.n and h.p[j] != '\n': inc j
    var c = i
    while c < j and h.p[c] != ':': inc c
    if eqLower(h.p, i, c - i, name):
      var a = c + 1
      var b = j
      if b > a and h.p[b - 1] == '\r': dec b
      while a < b and (h.p[a] == ' ' or h.p[a] == '\t'): inc a
      while b > a and (h.p[b - 1] == ' ' or h.p[b - 1] == '\t'): dec b
      return Span(p: cast[ptr UncheckedArray[char]](addr h.p[a]), n: b - a)
    i = j + 1
  Span()

proc queryParam*(req: Request, name: string): Span =
  ## raw (not url-decoded) value of query parameter `name`; empty Span if absent
  let q = req.query
  var i = 0
  while i < q.n:
    var j = i
    while j < q.n and q.p[j] != '&': inc j
    var e = i
    while e < j and q.p[e] != '=': inc e
    if e - i == name.len and (name.len == 0 or equalMem(addr q.p[i], unsafeAddr name[0], name.len)):
      return if e < j: Span(p: cast[ptr UncheckedArray[char]](addr q.p[e + 1]), n: j - e - 1) else: Span()
    i = j + 1
  Span()

proc hexVal(c: char): int {.inline.} =
  case c
  of '0'..'9': ord(c) - 48
  of 'a'..'f': ord(c) - 87
  of 'A'..'F': ord(c) - 55
  else: -1

proc urlDecode*(s: Span): string =
  ## percent-decode (and '+' -> ' ')
  result = newStringOfCap(s.n)
  var i = 0
  while i < s.n:
    let c = s.p[i]
    if c == '+': result.add ' '
    elif c == '%' and i + 2 < s.n and hexVal(s.p[i+1]) >= 0 and hexVal(s.p[i+2]) >= 0:
      result.add chr(hexVal(s.p[i+1]) * 16 + hexVal(s.p[i+2]))
      i += 2
    else: result.add c
    inc i

# ---------------------------------------------------------------------------
# Response writing (plain procs: they only append to the output buffer)
# ---------------------------------------------------------------------------

proc statusLine(code: int): string =
  case code
  of 100: "HTTP/1.1 100 Continue\r\n"
  of 101: "HTTP/1.1 101 Switching Protocols\r\n"
  of 200: "HTTP/1.1 200 OK\r\n"
  of 201: "HTTP/1.1 201 Created\r\n"
  of 202: "HTTP/1.1 202 Accepted\r\n"
  of 204: "HTTP/1.1 204 No Content\r\n"
  of 206: "HTTP/1.1 206 Partial Content\r\n"
  of 301: "HTTP/1.1 301 Moved Permanently\r\n"
  of 302: "HTTP/1.1 302 Found\r\n"
  of 303: "HTTP/1.1 303 See Other\r\n"
  of 304: "HTTP/1.1 304 Not Modified\r\n"
  of 307: "HTTP/1.1 307 Temporary Redirect\r\n"
  of 308: "HTTP/1.1 308 Permanent Redirect\r\n"
  of 400: "HTTP/1.1 400 Bad Request\r\n"
  of 401: "HTTP/1.1 401 Unauthorized\r\n"
  of 403: "HTTP/1.1 403 Forbidden\r\n"
  of 404: "HTTP/1.1 404 Not Found\r\n"
  of 405: "HTTP/1.1 405 Method Not Allowed\r\n"
  of 408: "HTTP/1.1 408 Request Timeout\r\n"
  of 409: "HTTP/1.1 409 Conflict\r\n"
  of 411: "HTTP/1.1 411 Length Required\r\n"
  of 413: "HTTP/1.1 413 Content Too Large\r\n"
  of 414: "HTTP/1.1 414 URI Too Long\r\n"
  of 415: "HTTP/1.1 415 Unsupported Media Type\r\n"
  of 417: "HTTP/1.1 417 Expectation Failed\r\n"
  of 422: "HTTP/1.1 422 Unprocessable Content\r\n"
  of 429: "HTTP/1.1 429 Too Many Requests\r\n"
  of 431: "HTTP/1.1 431 Request Header Fields Too Large\r\n"
  of 500: "HTTP/1.1 500 Internal Server Error\r\n"
  of 501: "HTTP/1.1 501 Not Implemented\r\n"
  of 502: "HTTP/1.1 502 Bad Gateway\r\n"
  of 503: "HTTP/1.1 503 Service Unavailable\r\n"
  of 504: "HTTP/1.1 504 Gateway Timeout\r\n"
  else: "HTTP/1.1 " & $code & " Status\r\n"

proc ensure(res: Response, extra: int) {.inline.} =
  if res.olen + extra > res.ocap:
    let ncap = max(res.ocap * 2, res.olen + extra + 256)
    let np = cast[ptr UncheckedArray[char]](alloc(ncap))
    copyMem(np, res.ob, res.olen)
    if res.obHeap: dealloc(res.ob)
    res.ob = np
    res.ocap = ncap
    res.obHeap = true

proc putStr(res: Response, s: string) {.inline.} =
  if s.len > 0:
    copyMem(addr res.ob[res.olen], unsafeAddr s[0], s.len)
    res.olen += s.len

proc putInt(res: Response, v: int) {.inline.} =
  var tmp: array[20, char]
  var i = 20
  var x = v
  if x == 0:
    res.ob[res.olen] = '0'; inc res.olen; return
  while x > 0:
    dec i
    tmp[i] = char(48 + x mod 10)
    x = x div 10
  let n = 20 - i
  copyMem(addr res.ob[res.olen], addr tmp[i], n)
  res.olen += n

proc beginHead(res: Response, code: int, ctype: string, clen: int) =
  let sl = statusLine(code)
  res.ensure(sl.len + 37 + ctype.len + res.xh.len + 96)
  res.putStr sl
  if res.date != nil:
    copyMem(addr res.ob[res.olen], res.date, 37)
    res.olen += 37
  if ctype.len > 0:
    res.putStr "Content-Type: "
    res.putStr ctype
    res.putStr "\r\n"
  if clen >= 0:
    res.putStr "Content-Length: "
    res.putInt clen
    res.putStr "\r\n"
  if res.xh.len > 0:
    res.putStr res.xh
    res.xh.setLen(0)
  if res.closeAfter: res.putStr "Connection: close\r\n"
  res.putStr "\r\n"

proc header*(res: Response, name, value: string) =
  ## add a response header for the next `send*` call
  res.xh.add name; res.xh.add ": "; res.xh.add value; res.xh.add "\r\n"

proc sendPtr*(res: Response, code: int, body: pointer, n: int,
              contentType = "text/plain; charset=utf-8") =
  ## respond with `n` bytes at `body` (copied into the output buffer)
  if res.responded: return
  res.responded = true
  let noBody = code == 204 or code == 304 or (code >= 100 and code < 200)
  res.beginHead(code, (if noBody: "" else: contentType), (if noBody: -1 else: n))
  if n > 0 and not res.headOnly and not noBody:
    res.ensure(n)
    copyMem(addr res.ob[res.olen], body, n)
    res.olen += n

proc send*(res: Response, code: int, body: string, contentType = "text/plain; charset=utf-8") {.inline.} =
  res.sendPtr(code, (if body.len > 0: unsafeAddr body[0] else: nil), body.len, contentType)

proc sendText*(res: Response, body: string) {.inline.} = res.send(200, body)
proc sendHtml*(res: Response, body: string) {.inline.} = res.send(200, body, "text/html; charset=utf-8")
proc sendJson*(res: Response, body: string) {.inline.} = res.send(200, body, "application/json")
proc sendEmpty*(res: Response, code = 204) {.inline.} = res.sendPtr(code, nil, 0)

proc redirect*(res: Response, location: string, code = 302) =
  res.header("Location", location)
  res.send(code, "")

proc mimeOf(path: string): string =
  let ext = path.rsplit('.', maxsplit = 1)
  if ext.len < 2: return "application/octet-stream"
  case ext[1].toLowerAscii
  of "html", "htm": "text/html; charset=utf-8"
  of "css": "text/css"
  of "js", "mjs": "text/javascript"
  of "json": "application/json"
  of "txt": "text/plain; charset=utf-8"
  of "png": "image/png"
  of "jpg", "jpeg": "image/jpeg"
  of "gif": "image/gif"
  of "svg": "image/svg+xml"
  of "ico": "image/x-icon"
  of "wasm": "application/wasm"
  of "pdf": "application/pdf"
  else: "application/octet-stream"

proc sendFile*(res: Response, path: string): bool =
  ## zero-copy file response (sendfile(2)); false (and nothing sent) if the file cannot be opened
  if res.responded: return false
  let fd = posix.open(path.cstring, O_RDONLY or O_CLOEXEC)
  if fd < 0: return false
  var st: Stat
  if fstat(fd, st) != 0 or not S_ISREG(st.st_mode):
    discard posix.close(fd); return false
  res.responded = true
  res.beginHead(200, mimeOf(path), st.st_size.int)
  if res.headOnly or st.st_size == 0: discard posix.close(fd)
  else:
    res.ffd = fd; res.foff = 0; res.fleft = st.st_size.int
  true

proc startChunked*(res: Response, code = 200, contentType = "text/plain; charset=utf-8") =
  ## begin a `Transfer-Encoding: chunked` response; follow with `chunk`/`flush`/`endChunked`
  if res.responded: return
  res.responded = true
  res.chunked = true
  res.header("Transfer-Encoding", "chunked")
  res.beginHead(code, contentType, -1)

proc chunk*(res: Response, data: string) =
  if data.len == 0 or res.headOnly: return
  res.ensure(data.len + 24)
  var tmp: array[16, char]
  var k = 16
  var x = data.len
  while x > 0:
    dec k
    tmp[k] = "0123456789ABCDEF"[x and 15]
    x = x shr 4
  copyMem(addr res.ob[res.olen], addr tmp[k], 16 - k)
  res.olen += 16 - k
  res.putStr "\r\n"
  res.putStr data
  res.putStr "\r\n"

proc endChunked*(res: Response) =
  res.ensure(8)
  res.putStr "0\r\n\r\n"
  res.chunked = false

# --- socket I/O ---------------------------------------------------------------

proc trySend(res: Response): int {.inline.} =
  ## 1 = progress/finished, 0 = would block (wait writable), -1 = connection error
  while res.osent < res.olen:
    if not res.pf.wrReady: return 0
    let r = posix.send(res.fd.SocketHandle, addr res.ob[res.osent], res.olen - res.osent, MSG_NOSIGNAL)
    if r > 0:
      res.osent += r
      if res.osent < res.olen: res.pf.wrReady = false      # kernel buffer full: wait for the edge
    elif r < 0:
      let e = errno
      if e == EAGAIN or e == EWOULDBLOCK: res.pf.wrReady = false; return 0
      if e == EINTR: continue
      return -1
    else: return -1
  while res.fleft > 0:
    if not res.pf.wrReady: return 0
    let r = sendfile(res.fd, res.ffd, addr res.foff, res.fleft.csize_t)
    if r > 0:
      res.fleft -= r
      if res.fleft > 0 and r < 65536: discard
    elif r < 0:
      let e = errno
      if e == EAGAIN or e == EWOULDBLOCK: res.pf.wrReady = false; return 0
      if e == EINTR: continue
      return -1
    else: return -1
  if res.ffd >= 0 and res.fleft == 0:
    discard posix.close(res.ffd); res.ffd = -1
  res.olen = 0; res.osent = 0
  1

template drainOut*(res: Response) =
  ## send everything queued, pausing the task while the socket is full
  while res.olen > 0 or res.fleft > 0:
    let flowR = trySend(res)
    if flowR < 0:
      res.olen = 0; res.osent = 0
      raise newException(ConnectionClosed, "write failed")
    if flowR == 0: pioWaitWrite(res.pf)

proc flush*(res: Response) {.flow.} =
  ## push queued output to the client now (for streaming / chunked handlers)
  drainOut(res)

# ---------------------------------------------------------------------------
# Request parser: in place, no allocation.  Returns
#   1 ok, 0 need more bytes, 2 need more + send "100 Continue", <0: -status
# ---------------------------------------------------------------------------

proc findHeaderEnd(rb: ptr UncheckedArray[char], start, `from`, to: int): int =
  var i = max(`from`, start + 3)
  while i < to:
    let q = memchr(addr rb[i], '\n'.cint, (to - i).csize_t)
    if q == nil: return -1
    let j = cast[int](q) - cast[int](rb)
    if j >= start + 3 and rb[j - 1] == '\r' and rb[j - 2] == '\n' and rb[j - 3] == '\r':
      return j + 1
    i = j + 1
  -1

proc parseRequest(c: Conn, maxHdr, maxBody: int, consumed: var int): int =
  let rb = c.rb
  var start = c.rpos
  let to = c.rlen
  while start < to and (rb[start] == '\r' or rb[start] == '\n'): inc start   # stray CRLF between requests
  c.rpos = start
  if start == to: return 0
  let he = findHeaderEnd(rb, start, c.scanFrom, to)
  if he < 0:
    if to - start > maxHdr: return -431
    c.scanFrom = to
    c.need = 0
    return 0
  if he - start > maxHdr: return -431
  let req = c.req
  # --- request line
  var i = start
  while i < he and rb[i] != ' ' and tokTab[rb[i].int] != '\0': inc i
  if i == start or i >= he or rb[i] != ' ': return -400
  let ml = i - start
  req.meth =
    case ml
    of 3:
      if rb[start] == 'G' and rb[start+1] == 'E' and rb[start+2] == 'T': hmGet
      elif rb[start] == 'P' and rb[start+1] == 'U' and rb[start+2] == 'T': hmPut
      else: hmOther
    of 4:
      if rb[start] == 'P' and rb[start+1] == 'O' and rb[start+2] == 'S' and rb[start+3] == 'T': hmPost
      elif rb[start] == 'H' and rb[start+1] == 'E' and rb[start+2] == 'A' and rb[start+3] == 'D': hmHead
      else: hmOther
    of 5: (if equalMem(addr rb[start], "PATCH".cstring, 5): hmPatch else: hmOther)
    of 6: (if equalMem(addr rb[start], "DELETE".cstring, 6): hmDelete else: hmOther)
    of 7: (if equalMem(addr rb[start], "OPTIONS".cstring, 7): hmOptions else: hmOther)
    else: hmOther
  inc i
  let ts = i
  var qpos = -1
  while i < he and rb[i] != ' ':
    let ch = rb[i]
    if ch <= ' ' or ch == '\x7f': return -400
    if ch == '?' and qpos < 0: qpos = i
    inc i
  if i >= he or i == ts: return -400
  req.target = Span(p: cast[ptr UncheckedArray[char]](addr rb[ts]), n: i - ts)
  if qpos < 0:
    req.path = req.target
    req.query = Span()
  else:
    req.path = Span(p: req.target.p, n: qpos - ts)
    req.query = Span(p: cast[ptr UncheckedArray[char]](addr rb[qpos + 1]), n: i - qpos - 1)
  inc i
  if he - i < 10 or rb[i] != 'H' or rb[i+1] != 'T' or rb[i+2] != 'T' or rb[i+3] != 'P' or rb[i+4] != '/' or
     rb[i+5] != '1' or rb[i+6] != '.' or rb[i+8] != '\r' or rb[i+9] != '\n': return -400
  case rb[i+7]
  of '1': req.http10 = false
  of '0': req.http10 = true
  else: return -505
  i += 10
  req.headers = Span(p: cast[ptr UncheckedArray[char]](addr rb[i]), n: he - i)
  # --- header fields
  var clen = -1
  var keep = not req.http10
  var chunked = false
  req.expectContinue = false
  while i < he:
    if rb[i] == '\r': break                                  # blank line: end of header
    let q = memchr(addr rb[i], '\n'.cint, (he - i).csize_t)
    let j = cast[int](q) - cast[int](rb)                     # exists: he is past the last "\r\n"
    if rb[j - 1] != '\r': return -400                        # bare LF
    var k = i
    while k < j and tokTab[rb[k].int] != '\0': inc k
    if k == i or k >= j or rb[k] != ':': return -400
    let nl = k - i
    var a = k + 1
    var b = j - 1
    while a < b and (rb[a] == ' ' or rb[a] == '\t'): inc a
    while b > a and (rb[b - 1] == ' ' or rb[b - 1] == '\t'): dec b
    # a bare CR inside the line would let two parsers see different headers
    let cr = memchr(addr rb[a], '\r'.cint, (j - a).csize_t)
    if cr != nil and cast[int](cr) - cast[int](rb) != j - 1: return -400
    case nl
    of 14:
      if eqLower(rb, i, 14, "content-length"):
        if b == a or b - a > 18: return -400
        var v = 0
        for x in a ..< b:
          let d = rb[x].int - 48
          if d < 0 or d > 9: return -400
          v = v * 10 + d
        if clen >= 0 and clen != v: return -400
        clen = v
    of 10:
      if eqLower(rb, i, 10, "connection"):
        if hasToken(rb, a, b - a, "close"): keep = false
        elif hasToken(rb, a, b - a, "keep-alive"): keep = true
    of 17:
      if eqLower(rb, i, 17, "transfer-encoding"):
        chunked = true
    of 6:
      if eqLower(rb, i, 6, "expect"):
        if hasToken(rb, a, b - a, "100-continue"): req.expectContinue = true
        else: return -417
    else: discard
    i = j + 1
  if chunked:
    if clen >= 0: return -400                                # request smuggling guard
    return -501
  req.keepAlive = keep
  req.contentLength = max(clen, 0)
  if req.contentLength > maxBody: return -413
  let total = he + req.contentLength
  if total > to:
    # need the rest of the body (the header end stays found: scanFrom is not advanced)
    c.need = total - start
    return (if req.expectContinue and not c.sentContinue: 2 else: 0)
  req.body = Span(p: cast[ptr UncheckedArray[char]](addr rb[he]), n: req.contentLength)
  req.hdrEnd = he
  consumed = total
  1

# ---------------------------------------------------------------------------
# Buffer leasing
# ---------------------------------------------------------------------------

proc leaseIn(w: Worker, c: Conn) {.inline.} =
  if c.carry != nil:
    c.rb = c.carry; c.rcap = c.carryCap; c.rpos = 0; c.rlen = c.carryLen
  elif not w.inBusy:
    w.inBusy = true
    c.rb = w.scratchIn; c.rcap = ScratchSize; c.rpos = 0; c.rlen = 0
  else:
    c.carryCap = 16 * 1024
    c.carry = cast[ptr UncheckedArray[char]](alloc(c.carryCap))
    c.carryLen = 0
    c.rb = c.carry; c.rcap = c.carryCap; c.rpos = 0; c.rlen = 0
  c.scanFrom = 0
  c.need = 0

proc growIn(w: Worker, c: Conn, need: int) =
  ## make the read buffer hold at least `need` bytes (moving it to a heap carry buffer when needed)
  let left = c.rlen - c.rpos
  let shift = c.rpos
  if c.rb == c.carry:
    if c.rpos > 0:
      moveMem(c.carry, addr c.carry[c.rpos], left)
      c.rpos = 0; c.rlen = left
    if need > c.carryCap:
      let ncap = max(need, c.carryCap * 2)
      c.carry = cast[ptr UncheckedArray[char]](realloc(c.carry, ncap))
      c.carryCap = ncap
  else:
    let ncap = max(need, 16 * 1024)
    let nb = cast[ptr UncheckedArray[char]](alloc(ncap))
    copyMem(nb, addr c.rb[c.rpos], left)
    w.inBusy = false                         # the scratch buffer is free again
    c.carry = nb; c.carryCap = ncap
  c.rb = c.carry; c.rcap = c.carryCap; c.rpos = 0; c.rlen = left
  c.scanFrom = max(0, c.scanFrom - shift)

proc releaseIn(w: Worker, c: Conn) {.inline.} =
  let left = c.rlen - c.rpos
  if c.rb == w.scratchIn:
    if left > 0:
      c.carryCap = max(left, 4096)
      c.carry = cast[ptr UncheckedArray[char]](alloc(c.carryCap))
      copyMem(c.carry, addr c.rb[c.rpos], left)
      c.carryLen = left
    w.inBusy = false
  else:
    if left == 0:
      dealloc(c.carry); c.carry = nil; c.carryCap = 0; c.carryLen = 0
    else:
      if c.rpos > 0: moveMem(c.carry, addr c.carry[c.rpos], left)
      c.carryLen = left
  c.rb = nil

proc leaseOut(w: Worker, c: Conn) {.inline.} =
  let r = c.res
  if not w.outBusy:
    w.outBusy = true
    r.ob = w.scratchOut; r.ocap = ScratchSize; r.obHeap = false
  else:
    r.ob = cast[ptr UncheckedArray[char]](alloc(16 * 1024)); r.ocap = 16 * 1024; r.obHeap = true
  r.olen = 0; r.osent = 0

proc releaseOut(w: Worker, c: Conn) {.inline.} =
  let r = c.res
  if r.obHeap: dealloc(r.ob)
  else: w.outBusy = false
  r.ob = nil; r.ocap = 0; r.obHeap = false

# ---------------------------------------------------------------------------
# Per-request bookkeeping (plain procs)
# ---------------------------------------------------------------------------

proc recvInto(c: Conn): int {.inline.} =
  ## >0 bytes read, 0 EOF, -1 nothing available (readiness cleared), -2 error
  if not c.pf.rdReady: return -1
  let space = c.rcap - c.rlen
  while true:
    let r = posix.recv(c.fd.SocketHandle, addr c.rb[c.rlen], space, 0)
    if r > 0:
      c.rlen += r
      if r < space: c.pf.rdReady = false         # short read: drained; the next byte raises a new edge
      return r
    if r == 0: return 0
    let e = errno
    if e == EAGAIN or e == EWOULDBLOCK: c.pf.rdReady = false; return -1
    if e == EINTR: continue
    return -2

proc beginRequest(c: Conn) {.inline.} =
  let r = c.res
  r.responded = false
  r.closeAfter = not c.req.keepAlive
  r.headOnly = c.req.meth == hmHead
  r.chunked = false
  r.xh.setLen(0)

proc errorResponse(c: Conn, code: int) =
  let r = c.res
  r.responded = false
  r.closeAfter = true
  r.headOnly = false
  r.xh.setLen(0)
  let msg = statusLine(code)[9 .. ^3]
  r.send(code, msg & "\n")
  c.closing = true

proc endRequest(c: Conn, consumed: int) {.inline.} =
  let r = c.res
  if not r.responded:
    c.errorResponse(500)
  elif r.closeAfter: c.closing = true
  c.rpos = consumed                  # absolute end of this request in the buffer
  c.scanFrom = 0
  c.need = 0
  c.sentContinue = false

# ---------------------------------------------------------------------------
# Server plumbing
# ---------------------------------------------------------------------------

var stopFlag: Atomic[bool]
var listenFds: array[256, Atomic[cint]]
var listenCount: Atomic[int]

proc isStopping*(): bool {.inline.} = stopFlag.load(moRelaxed)

proc stopServer*() =
  ## ask all workers to finish (signal-safe)
  stopFlag.store(true)
  for i in 0 ..< min(listenCount.load(), 256):
    let fd = listenFds[i].load()
    if fd >= 0: discard posix.shutdown(fd.SocketHandle, SHUT_RDWR)

proc newWorker*(cfg: ServerConfig, id: int): Worker =
  result = Worker(id: id, cfg: cfg)
  result.sem = newSemaphore(cfg.maxConns)
  result.scratchIn = cast[ptr UncheckedArray[char]](alloc(ScratchSize))
  result.scratchOut = cast[ptr UncheckedArray[char]](alloc(ScratchSize))
  result.date = cast[ptr UncheckedArray[char]](alloc0(40))

proc setDate(w: Worker) =
  if not w.cfg.sendDate: return
  let s = "Date: " & now().utc.format("ddd, dd MMM yyyy HH:mm:ss") & " GMT\r\n"
  if s.len == 37: copyMem(w.date, unsafeAddr s[0], 37)

proc openListener(w: Worker) =
  let cfg = w.cfg
  let fd = socket(AF_INET, SOCK_STREAM or SOCK_NB or SOCK_CE, 0)
  if fd.cint < 0: raiseOSError(osLastError())
  var one = 1.cint
  discard setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, addr one, sizeof(one).SockLen)
  discard setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, addr one, sizeof(one).SockLen)
  if cfg.noDelay:
    discard setsockopt(fd, IPPROTO_TCP.cint, TCP_NODELAY, addr one, sizeof(one).SockLen)   # inherited by accepted sockets
  var defer1 = 1.cint
  discard setsockopt(fd, IPPROTO_TCP.cint, TCP_DEFER_ACCEPT, addr defer1, sizeof(defer1).SockLen)
  var sa: Sockaddr_in
  sa.sin_family = AF_INET.TSa_Family
  sa.sin_port = htons(cfg.port.uint16)
  if inet_pton(AF_INET, cfg.host.cstring, addr sa.sin_addr) != 1:
    raise newException(ValueError, "bad host address: " & cfg.host)
  if bindSocket(fd, cast[ptr SockAddr](addr sa), sizeof(sa).SockLen) < 0:
    let e = osLastError()
    discard posix.close(fd)
    raiseOSError(e, "bind " & cfg.host & ":" & $cfg.port)
  if listen(fd, cfg.backlog.cint) < 0: raiseOSError(osLastError())
  w.lfd = fd.cint
  w.lpf = pioOpen(fd.int)
  let slot = listenCount.fetchAdd(1)
  if slot < 256: listenFds[slot].store(fd.cint)

proc acceptNb(w: Worker): cint {.inline.} =
  ## >=0 new connected socket; -1 nothing to accept (readiness cleared); -2 transient failure
  while true:
    let fd = accept4(w.lfd, nil, nil, SOCK_NB or SOCK_CE)
    if fd >= 0: return fd
    let e = errno
    if e == EAGAIN or e == EWOULDBLOCK: w.lpf.rdReady = false; return -1
    if e == EINTR or e == ECONNABORTED or e == EPROTO: continue
    if isStopping(): return -3
    if e == EMFILE or e == ENFILE or e == ENOBUFS or e == ENOMEM: return -2
    return -3        # listener shut down / closed

proc newSession(w: Worker, fd: cint): Conn =
  if w.freeConns.len > 0: result = w.freeConns.pop()
  else:
    result = Conn(req: Request(), res: Response(ffd: -1))
    w.conns.add result
  result.fd = fd
  result.pf = pioOpen(fd.int)
  result.busy = true
  result.working = false
  result.closing = false
  result.sentContinue = false
  result.lastTick = w.tick
  result.carry = nil; result.carryCap = 0; result.carryLen = 0
  result.res.pf = result.pf
  result.res.fd = fd
  result.res.date = if w.cfg.sendDate: w.date else: nil
  result.res.ffd = -1
  inc w.active

proc endSession(w: Worker, c: Conn) =
  if c.carry != nil: dealloc(c.carry); c.carry = nil
  if c.res.ob != nil: releaseOut(w, c)
  if c.res.ffd >= 0: discard posix.close(c.res.ffd); c.res.ffd = -1
  c.res.xh.setLen(0)
  pioClose(c.pf)
  c.pf = nil
  c.busy = false
  dec w.active
  w.freeConns.add c
  w.sem.release()

proc sweep(w: Worker) =
  ## once a second: refresh the Date header, close idle connections
  inc w.tick
  w.setDate()
  let lim = w.cfg.idleTimeoutSec
  for c in w.conns:
    if c.busy and not c.working and w.tick - c.lastTick >= lim:
      discard posix.shutdown(c.fd.SocketHandle, SHUT_RDWR)   # the session sees EOF and cleans up

proc freeWorker(w: Worker) =
  ## release everything the worker owns (call after its event loop has ended)
  for c in w.conns:
    if c.carry != nil: dealloc(c.carry); c.carry = nil
  w.conns.setLen(0); w.freeConns.setLen(0)
  dealloc(w.scratchIn); dealloc(w.scratchOut); dealloc(w.date)
  if w.lpf != nil: pioClose(w.lpf); w.lpf = nil
  pioDrain()

proc killAll(w: Worker) =
  for c in w.conns:
    if c.busy: discard posix.shutdown(c.fd.SocketHandle, SHUT_RDWR)

proc reaper*(w: Worker) {.flow.} =
  while not isStopping():
    delay(1000)
    w.sweep()

proc normalize(cfg: var ServerConfig) =
  if cfg.host.len == 0: cfg.host = "0.0.0.0"
  if cfg.workers <= 0: cfg.workers = max(1, countProcessors())
  if cfg.maxConns <= 0: cfg.maxConns = 10_000
  if cfg.backlog <= 0: cfg.backlog = 4096
  if cfg.maxHeaderBytes <= 0: cfg.maxHeaderBytes = 16 * 1024
  if cfg.maxBodyBytes <= 0: cfg.maxBodyBytes = 1 shl 20
  if cfg.idleTimeoutSec <= 0: cfg.idleTimeoutSec = 30

type WorkerArg* = object
  cfg*: ptr ServerConfig
  id*: int
  err*: cstring

# ---------------------------------------------------------------------------
# The server generator: instantiates the session / accept tasks around `handler`
# ---------------------------------------------------------------------------

template httpServer*(runName: untyped, handler: untyped) =
  ## Define `proc runName(cfg: ServerConfig)`: runs the server (blocks until
  ## `stopServer()` or SIGINT/SIGTERM) with `handler(req: Request, res: Response)`
  ## being a plain proc or a `{.flow.}` proc.

  proc stagehttpSession(w: Worker, c: Conn) {.flow.} =
    try:
      while true:
        # 1. wait for the socket (an idle connection holds no buffer)
        if not c.pf.rdReady: pioWaitRead(c.pf)
        # 2. lease the buffers for the duration of this burst of requests
        leaseIn(w, c)
        leaseOut(w, c)
        var eof = false
        while true:
          let n = recvInto(c)
          if n == 0 or n == -2: eof = true
          elif n > 0: c.lastTick = w.tick
          # 3. answer every complete request in the buffer (pipelining)
          var more = true
          while more:
            var consumed = 0
            let st = parseRequest(c, w.cfg.maxHeaderBytes, w.cfg.maxBodyBytes, consumed)
            if st == 1:
              c.working = true
              beginRequest(c)
              try:
                handler(c.req, c.res)
              except CatchableError as e:
                if e of ConnectionClosed or e of CancelledError: raise
                c.res.xh.setLen(0)
                c.res.responded = false
                c.res.chunked = false
                errorResponse(c, 500)
              c.working = false
              endRequest(c, consumed)
              inc w.served
              if c.closing: more = false
              elif c.res.olen > 32 * 1024: drainOut(c.res)
            elif st < 0:
              errorResponse(c, -st)
              more = false
            else:
              if st == 2:
                c.sentContinue = true
                c.res.putStr "HTTP/1.1 100 Continue\r\n\r\n"
              more = false
          if c.closing: break
          let left = c.rlen - c.rpos
          if left == 0:
            c.rpos = 0; c.rlen = 0                   # drained: reuse the buffer from the start
            if eof: break
            break                                    # wait for the next edge
          # a partial request is buffered: make room, push pending output, wait for the rest
          if eof: break
          if c.need > c.rcap - c.rpos or c.rlen == c.rcap:
            let want = if c.need > 0: c.need + 1024
                       else: min(c.rcap * 2, w.cfg.maxHeaderBytes + 1024)
            growIn(w, c, max(want, c.rlen - c.rpos + 1024))
          if c.res.olen > 0: drainOut(c.res)
          if not c.pf.rdReady: pioWaitRead(c.pf)
        # 4. flush this burst's responses with one send, then give the buffers back
        if c.res.olen > 0 or c.res.fleft > 0: drainOut(c.res)
        if c.closing or eof: break
        releaseOut(w, c)
        releaseIn(w, c)
    except ConnectionClosed: discard
    except CancelledError: discard
    except IOError: discard
    except OSError: discard
    finally:
      if c.rb != nil:
        c.rpos = c.rlen
        releaseIn(w, c)
      endSession(w, c)

  proc stagehttpAccept(w: Worker) {.flow.} =
    while not isStopping():
      acquire(w.sem)                          # N-limit: at most maxConns live sessions
      var cfd: cint = -1
      while cfd < 0:
        cfd = acceptNb(w)
        if cfd == -1:
          pioWaitRead(w.lpf)
          if isStopping(): cfd = -3
        elif cfd == -2: delay(5)              # out of descriptors: back off instead of spinning
        if cfd == -3: break
      if cfd < 0:
        w.sem.release()
        break
      let c = newSession(w, cfd)
      discard go stagehttpSession(w, c)

  proc stagehttpMain(w: Worker) {.flow.} =
    let rp = go reaper(w)
    stagehttpAccept(w)
    cancel(rp)
    w.killAll()
    var spins = 0
    while w.active > 0 and spins < 5000:       # let sessions notice and clean up (<= 5 s)
      delay(1)
      inc spins

  proc stagehttpThread(a: ptr WorkerArg) {.thread.} =
    {.cast(gcsafe).}:
      try:
        let w = newWorker(a.cfg[], a.id)
        w.setDate()
        w.openListener()
        run stagehttpMain(w)
        freeWorker(w)
      except CatchableError as e:
        a.err = cstring(e.msg)
        stopServer()

  proc runName*(config: ServerConfig) =
    var cfg = config
    cfg.normalize()
    stopFlag.store(false)
    listenCount.store(0)
    signal(SIGPIPE, SIG_IGN)
    signal(SIGINT, proc (s: cint) {.noconv.} = stopServer())
    signal(SIGTERM, proc (s: cint) {.noconv.} = stopServer())
    var args = newSeq[WorkerArg](cfg.workers)
    var threads = newSeq[Thread[ptr WorkerArg]](cfg.workers)
    for i in 0 ..< cfg.workers:
      args[i] = WorkerArg(cfg: addr cfg, id: i)
    for i in 1 ..< cfg.workers: createThread(threads[i], stagehttpThread, addr args[i])
    stagehttpThread(addr args[0])              # the calling thread is worker 0
    for i in 1 ..< cfg.workers: joinThread(threads[i])
    for i in 0 ..< cfg.workers:
      if args[i].err != nil: raise newException(IOError, $args[i].err)

{.pop.}
