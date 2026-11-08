#!/usr/bin/env python3
"""Black-box tests for the stagehttp demo server (examples/demo.nim).
usage: python3 tests/test_server.py [port]"""
import socket, sys, time, threading, re

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8083
fails = 0
def check(name, cond, extra=""):
    global fails
    print(("PASS " if cond else "FAIL ") + name + ("" if cond else "  " + str(extra)))
    if not cond: fails += 1

def conn():
    s = socket.create_connection(("127.0.0.1", PORT)); s.settimeout(3); return s

def read_resp(s, buf=b""):
    """read exactly one response; returns (status, headers dict, body, rest)"""
    while b"\r\n\r\n" not in buf:
        d = s.recv(65536)
        if not d: raise EOFError(buf)
        buf += d
    head, rest = buf.split(b"\r\n\r\n", 1)
    lines = head.decode().split("\r\n")
    status = int(lines[0].split()[1])
    h = {k.lower(): v for k, v in (l.split(": ", 1) for l in lines[1:])}
    if h.get("transfer-encoding") == "chunked":
        body = b""
        while True:
            while b"\r\n" not in rest: rest += s.recv(65536)
            szl, rest = rest.split(b"\r\n", 1)
            sz = int(szl, 16)
            while len(rest) < sz + 2: rest += s.recv(65536)
            body += rest[:sz]; rest = rest[sz + 2:]
            if sz == 0: break
        return status, h, body, rest
    n = int(h.get("content-length", 0))
    while len(rest) < n:
        d = s.recv(65536)
        if not d: raise EOFError
        rest += d
    return status, h, rest[:n], rest[n:]

def get(path, extra=""):
    s = conn(); s.sendall(f"GET {path} HTTP/1.1\r\nHost: t\r\n{extra}Connection: close\r\n\r\n".encode())
    r = read_resp(s); s.close(); return r

# basic ---------------------------------------------------------------
st, h, b, _ = get("/hello")
check("hello", st == 200 and b == b"Hello, World!" and h["content-length"] == "13" and "date" in h)
check("404", get("/nope")[0] == 404)
st, h, b, _ = get("/q?a=1&b=x%20y%2Bz+w"); check("query + urldecode", b == b"1|x y+z w", b)
st, h, b, _ = get("/hdr", "X-TeSt: Value  \r\n"); check("header lookup, ci + trim", b == b"Value", b)
st, h, b, _ = get("/hdrs"); check("extra response headers", h.get("x-a") == "1" and h.get("x-b") == "2")
check("500 on handler exception", get("/boom")[0] == 500)

# keep-alive + pipelining ------------------------------------------------
s = conn()
for i in range(5):
    s.sendall(b"GET /hello HTTP/1.1\r\nHost: t\r\n\r\n"); st, h, b, _ = read_resp(s)
check("keep-alive x5", st == 200)
s.sendall((b"GET /hello HTTP/1.1\r\nHost: t\r\n\r\n" * 100))
ok = 0; rest = b""
for i in range(100):
    st, h, b, rest = read_resp(s, rest); ok += (st == 200 and b == b"Hello, World!")
check("pipelining x100 in order", ok == 100, ok)
# pipelined mix with POST bodies
reqs = b"".join(b"POST /echo HTTP/1.1\r\nHost: t\r\nContent-Length: %d\r\n\r\n%s" % (len(str(i)) * 3, (str(i) * 3).encode()) for i in range(50))
s.sendall(reqs); good = 0; rest = b""
for i in range(50):
    st, h, b, rest = read_resp(s, rest); good += (b == (str(i) * 3).encode())
check("pipelined POST bodies", good == 50, good)
s.close()

# partial arrivals --------------------------------------------------------
s = conn(); raw = b"POST /echo HTTP/1.1\r\nHost: t\r\nContent-Length: 11\r\n\r\nhello world"
for i in range(len(raw)):
    s.sendall(raw[i:i+1]); time.sleep(0.002)
st, h, b, _ = read_resp(s); check("byte-by-byte request", b == b"hello world", b); s.close()

# bodies ---------------------------------------------------------------------
big = bytes(range(256)) * 2000  # 512000
s = conn(); s.sendall(b"POST /echo HTTP/1.1\r\nHost: t\r\nContent-Length: %d\r\n\r\n" % len(big) + big)
st, h, b, _ = read_resp(s); check("512 KB body (bigger than scratch) echoed", b == big, len(b)); s.close()
s = conn(); s.sendall(b"POST /len HTTP/1.1\r\nHost: t\r\nContent-Length: 5000000\r\n\r\n")
st, h, b, _ = read_resp(s); check("413 for oversized body", st == 413, st); s.close()
s = conn(); s.sendall(b"POST /echo HTTP/1.1\r\nHost: t\r\nExpect: 100-continue\r\nContent-Length: 4\r\n\r\n")
d = s.recv(100); check("100-continue sent", d.startswith(b"HTTP/1.1 100 Continue"), d)
s.sendall(b"data"); st, h, b, _ = read_resp(s, d.split(b"\r\n\r\n", 1)[1]); check("body after 100-continue", b == b"data", b); s.close()
st, h, b, _ = get("/big"); check("300 KB response body", len(b) == 300000 and set(b) == {120})

# response modes -------------------------------------------------------------------
st, h, b, _ = get("/chunked"); check("chunked streaming response", b == b"part1;part2;part3;" and h["transfer-encoding"] == "chunked", b)
st, h, b, _ = get("/file"); check("sendfile", st == 200 and b.startswith(b"## Demo / test server") and int(h["content-length"]) == len(b))
s = conn(); s.sendall(b"HEAD /hello HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
d = b""
while True:
    x = s.recv(1000)
    if not x: break
    d += x
check("HEAD: content-length but no body", b"Content-Length: 13" in d and d.endswith(b"\r\n\r\n"), d); s.close()
s = conn(); s.sendall(b"GET /hello HTTP/1.0\r\n\r\n"); d = b""
while True:
    x = s.recv(1000)
    if not x: break
    d += x
check("HTTP/1.0 closes", d.startswith(b"HTTP/1.1 200") and b"Connection: close" in d, d); s.close()

# flow handler: slow routes must not block each other ---------------------------------
res = []
def slow(ms):
    t = time.time(); st, h, b, _ = get(f"/slow?ms={ms}"); res.append((ms, st, b, time.time() - t))
ths = [threading.Thread(target=slow, args=(300,)) for _ in range(40)]
t0 = time.time()
[t.start() for t in ths]; [t.join() for t in ths]
el = time.time() - t0
check("40 concurrent 300ms handlers overlap (flow handler)", el < 1.5 and all(r[1] == 200 and r[2] == b"slept 300" for r in res), el)
# fast requests are served while a slow one is parked
th = threading.Thread(target=slow, args=(800,)); th.start(); time.sleep(0.1)
t = time.time(); get("/hello"); fast = time.time() - t; th.join()
check("fast request not delayed by parked slow task", fast < 0.3, fast)

# malformed / hostile -----------------------------------------------------------------
def raw(data, expect=None):
    s = conn(); s.sendall(data)
    try: r = read_resp(s)[0]
    except EOFError: r = None
    s.close(); return r
check("garbage -> 400", raw(b"GARBAGE\r\n\r\n") == 400)
check("bare LF header -> 400", raw(b"GET /hello HTTP/1.1\r\nHost: t\nX: y\r\n\r\n") == 400)
check("space before colon -> 400", raw(b"GET /hello HTTP/1.1\r\nContent-Length : 5\r\n\r\n") == 400)
check("CL + TE smuggling -> 400", raw(b"POST /echo HTTP/1.1\r\nContent-Length: 4\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n") == 400)
check("conflicting CL -> 400", raw(b"POST /echo HTTP/1.1\r\nContent-Length: 4\r\nContent-Length: 5\r\n\r\nabcd") == 400)
check("non-numeric CL -> 400", raw(b"POST /echo HTTP/1.1\r\nContent-Length: 4x\r\n\r\nabcd") == 400)
check("bare CR in header -> 400", raw(b"GET /hello HTTP/1.1\r\nX: a\rb\r\n\r\n") == 400)
check("chunked request body -> 501", raw(b"POST /echo HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n") == 501)
check("HTTP/2.0 -> 505/400", raw(b"GET /hello HTTP/2.0\r\n\r\n") in (400, 505))
check("huge header -> 431", raw(b"GET /hello HTTP/1.1\r\nX: " + b"a" * 40000 + b"\r\n\r\n") == 431)
check("leading CRLF tolerated", raw(b"\r\nGET /hello HTTP/1.1\r\nConnection: close\r\n\r\n") == 200)

# idle timeout (server started with idleTimeoutSec=3) ----------------------------------------
s = conn(); s.settimeout(8); t = time.time()
try: d = s.recv(10)
except socket.timeout: d = None
check("idle connection is closed by the server (<= ~5s)", d == b"" , (d, time.time() - t)); s.close()

# survives all of the above
st, h, b, _ = get("/hello"); check("still serving", st == 200)
print("\nFAILURES:", fails); sys.exit(1 if fails else 0)
