## Demo / test server for stagehttp.  Handler is a {.flow.} proc: routes may pause.
import guildenstern/stagehttp
import std/[os, strutils]

proc slowAnswer(ms: int): string {.flow.} =
  delay(ms)                       # pauses this connection's task only, not the worker
  "slept " & $ms

proc onRequest(req: Request, res: Response) {.flow.} =
  if req.isPath("/hello"): res.sendText("Hello, World!")
  elif req.isPath("/echo"):
    res.send(200, $req.body, "application/octet-stream")
  elif req.isPath("/len"): res.sendText($req.body.len)
  elif req.isPath("/q"):
    res.sendText($req.queryParam("a") & "|" & urlDecode(req.queryParam("b")))
  elif req.isPath("/hdr"): res.sendText($req.header("x-test"))
  elif req.isPath("/slow"):
    let ms = parseInt($req.queryParam("ms"))
    res.sendText(slowAnswer(ms))           # a flow call: the task parks, other connections keep running
  elif req.isPath("/big"):
    res.send(200, 'x'.repeat(300_000))
  elif req.isPath("/chunked"):
    res.startChunked()
    for i in 1..3:
      res.chunk("part" & $i & ";")
      res.flush()                           # flow call: push now
      delay(5)
    res.endChunked()
  elif req.isPath("/file"):
    if not res.sendFile(getAppDir() / "examples" / "demo.nim"): res.send(404, "nofile")
  elif req.isPath("/boom"): raise newException(ValueError, "boom")
  elif req.isPath("/hdrs"):
    res.header("X-A", "1"); res.header("X-B", "2")
    res.sendText("ok")
  else: res.send(404, "not found")

httpServer(serve, onRequest)
let port = if paramCount() > 0: parseInt(paramStr(1)) else: 8083
let workers = if paramCount() > 1: parseInt(paramStr(2)) else: 2
let maxc = if paramCount() > 2: parseInt(paramStr(3)) else: 0
serve(ServerConfig(port: port, workers: workers, maxConns: maxc, maxBodyBytes: 1_000_000,
                   idleTimeoutSec: 3, sendDate: true, noDelay: true))
echo "server stopped cleanly"
