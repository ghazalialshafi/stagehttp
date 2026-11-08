import guildenstern/[epolldispatcher, httpserver]
proc onRequest() {.gcsafe, nimcall, raises: [].} =
  if isUri("/hello"): reply("Hello, World!")
  else: reply(Http404)
let s = newHttpServer(onRequest, contenttype = NoBody)
s.start(8081, 1)
joinThread(s.thread)
