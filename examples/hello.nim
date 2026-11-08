import guildenstern/stagehttp

proc onRequest(req: Request, res: Response) =
  if req.isPath("/hello"): res.sendText("Hello, World!")
  else: res.send(404, "not found")

httpServer(serve, onRequest)
serve(ServerConfig(port: 8082, workers: 1, sendDate: true, noDelay: true))
