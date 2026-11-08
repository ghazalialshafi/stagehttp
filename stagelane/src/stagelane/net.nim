## stagelane/net — non-blocking TCP on top of the event loop (POSIX and Windows).
import std/[nativesockets, os]
when defined(windows):
  import std/winlean
else:
  import std/posix
import ./core, ./transform, ./sched

# --- the few socket calls that differ between Winsock and POSIX ---------------
when defined(windows):
  const wsaEintr = 10004'i32
  const wsaEwouldblock = 10035'i32
  proc lastNetError(): int {.inline.} = int(wsaGetLastError())
  proc errWouldBlock(e: int): bool {.inline.} = e == wsaEwouldblock or e == wsaEintr
  proc errInProgress(e: int): bool {.inline.} = e == wsaEwouldblock     # connect() on a non-blocking socket
  proc sockListen(fd: SocketHandle, backlog: int): int {.inline.} = int(winlean.listen(fd, backlog.cint))
  proc sockName(fd: SocketHandle, sa: ptr SockAddr, len: ptr SockLen): int {.inline.} =
    int(winlean.getsockname(fd, sa, len))
  proc sockAccept(fd: SocketHandle, sa: ptr SockAddr, len: ptr SockLen): SocketHandle {.inline.} =
    winlean.accept(fd, sa, len)
  proc sockConnect(fd: SocketHandle, sa: ptr SockAddr, len: SockLen): int {.inline.} =
    int(winlean.connect(fd, sa, len))
  proc sockRecv(fd: SocketHandle, buf: pointer, n: int): int {.inline.} =
    int(winlean.recv(fd, cast[cstring](buf), n.cint, 0))
  proc sockSend(fd: SocketHandle, buf: pointer, n: int): int {.inline.} =
    int(winlean.send(fd, cast[cstring](buf), n.cint, 0))
  proc sockPendingError(fd: SocketHandle): int {.inline.} =
    var err: cint
    var len = SockLen(sizeof(err))
    discard winlean.getsockopt(fd, SOL_SOCKET, SO_ERROR, cast[cstring](addr err), addr len)
    int(err)
  proc netToHostPort(p: uint16): int {.inline.} = int(nativesockets.ntohs(p))
else:
  proc lastNetError(): int {.inline.} = int(errno)
  proc errWouldBlock(e: int): bool {.inline.} = e == int(EAGAIN) or e == int(EWOULDBLOCK) or e == int(EINTR)
  proc errInProgress(e: int): bool {.inline.} = e == int(EINPROGRESS)
  proc sockListen(fd: SocketHandle, backlog: int): int {.inline.} = int(posix.listen(fd, backlog.cint))
  proc sockName(fd: SocketHandle, sa: ptr SockAddr, len: ptr SockLen): int {.inline.} =
    int(posix.getsockname(fd, sa, len))
  proc sockAccept(fd: SocketHandle, sa: ptr SockAddr, len: ptr SockLen): SocketHandle {.inline.} =
    posix.accept(fd, sa, len)
  proc sockConnect(fd: SocketHandle, sa: ptr SockAddr, len: SockLen): int {.inline.} =
    int(posix.connect(fd, sa, len))
  proc sockRecv(fd: SocketHandle, buf: pointer, n: int): int {.inline.} = int(posix.recv(fd, buf, n, 0))
  proc sockSend(fd: SocketHandle, buf: pointer, n: int): int {.inline.} =
    int(posix.send(fd, buf, n, MSG_NOSIGNAL))        # unchanged from before the Windows port
  proc sockPendingError(fd: SocketHandle): int {.inline.} =
    var err: cint
    var len = SockLen(sizeof(err))
    discard posix.getsockopt(fd, SOL_SOCKET, SO_ERROR, addr err, addr len)
    int(err)
  proc netToHostPort(p: uint16): int {.inline.} = int(posix.ntohs(p))

type
  TcpStream* = ref object
    fd*: SocketHandle
    closed: bool
    rbuf: string
  TcpListener* = ref object
    fd*: SocketHandle

proc setNonBlock(fd: SocketHandle) = fd.setBlocking(false)

proc newTcpSocket(): SocketHandle =
  createNativeSocket(nativesockets.Domain.AF_INET, nativesockets.SockType.SOCK_STREAM,
                     nativesockets.Protocol.IPPROTO_TCP)

proc resolve(host: string, port: int): ptr AddrInfo =
  getAddrInfo(host, Port(port), nativesockets.Domain.AF_INET,
              nativesockets.SockType.SOCK_STREAM, nativesockets.Protocol.IPPROTO_TCP)


proc wouldBlock(): bool = errWouldBlock(lastNetError())

proc listenTcp*(port: int, host = "0.0.0.0", backlog = 128): TcpListener =
  let fd = newTcpSocket()
  if fd == osInvalidSocket: raiseOSError(osLastError())
  fd.setSockOptInt(SOL_SOCKET, SO_REUSEADDR, 1)
  var ai = resolve(host, port)
  if bindAddr(fd, ai.ai_addr, ai.ai_addrlen.SockLen) < 0:
    freeAddrInfo(ai); raiseOSError(osLastError())
  freeAddrInfo(ai)
  if sockListen(fd, backlog) < 0: raiseOSError(osLastError())
  setNonBlock(fd)
  TcpListener(fd: fd)

proc localPort*(l: TcpListener): int =
  var sa: Sockaddr_in
  var len = SockLen(sizeof(sa))
  discard sockName(l.fd, cast[ptr SockAddr](addr sa), addr len)
  netToHostPort(sa.sin_port.uint16)

proc close*(l: TcpListener) = close(l.fd)

proc close*(s: TcpStream) =
  if not s.closed:
    s.closed = true
    close(s.fd)

proc accept*(l: TcpListener): TcpStream {.flow.} =
  ## wait for and accept a connection
  while true:
    var sa: Sockaddr_in
    var len = SockLen(sizeof(sa))
    let fd = sockAccept(l.fd, cast[ptr SockAddr](addr sa), addr len)
    if fd != osInvalidSocket:
      setNonBlock(fd)
      return TcpStream(fd: fd)
    if not wouldBlock(): raiseOSError(osLastError())
    waitReadable(int(l.fd))

proc connectTcp*(host: string, port: int): TcpStream {.flow.} =
  ## connect to `host:port`
  let fd = newTcpSocket()
  if fd == osInvalidSocket: raiseOSError(osLastError())
  setNonBlock(fd)
  var ai = resolve(host, port)
  let r = sockConnect(fd, ai.ai_addr, ai.ai_addrlen.SockLen)
  let e = lastNetError()
  freeAddrInfo(ai)
  if r < 0 and not errInProgress(e):
    close(fd); raiseOSError(OSErrorCode(e))
  if r < 0:
    waitWritable(int(fd))
    let err = sockPendingError(fd)
    if err != 0:
      close(fd); raiseOSError(OSErrorCode(err))
  return TcpStream(fd: fd)

proc readSome*(s: TcpStream, n: int = 4096): string {.flow.} =
  ## read up to `n` bytes; returns "" at end of stream
  if s.rbuf.len > 0:
    let k = min(n, s.rbuf.len)
    result = s.rbuf[0..<k]
    s.rbuf = s.rbuf[k..^1]
    return
  var buf = newString(n)
  while true:
    let r = sockRecv(s.fd, addr buf[0], n)
    if r >= 0:
      buf.setLen(r)
      return buf
    if not wouldBlock(): raiseOSError(osLastError())
    waitReadable(int(s.fd))

proc readLine*(s: TcpStream): string {.flow.} =
  ## read up to and excluding "\n" ("\r\n" tolerated); "" + EOF -> raises IOError
  while true:
    let i = s.rbuf.find('\n')
    if i >= 0:
      result = s.rbuf[0..<i]
      if result.len > 0 and result[^1] == '\r': result.setLen(result.len - 1)
      s.rbuf = s.rbuf[i+1..^1]
      return
    var buf = newString(4096)
    var got = -1
    while got < 0:
      let r = sockRecv(s.fd, addr buf[0], 4096)
      if r >= 0: got = r
      elif not wouldBlock(): raiseOSError(osLastError())
      else: waitReadable(int(s.fd))
    if got == 0:
      if s.rbuf.len > 0:
        result = s.rbuf; s.rbuf = ""; return
      raise newException(IOError, "connection closed")
    buf.setLen(got)
    s.rbuf.add buf

proc write*(s: TcpStream, data: string) {.flow.} =
  ## write all of `data`
  var off = 0
  while off < data.len:
    let r = sockSend(s.fd, unsafeAddr data[off], data.len - off)
    if r >= 0: off += r
    elif wouldBlock(): waitWritable(int(s.fd))
    else: raiseOSError(osLastError())
