# GuildenStern + Stagelane

`guildenstern/stagehttp.nim` is a new HTTP/1.1 server for GuildenStern built on
Stagelane. The original modules are untouched. `stagelane/` is our library
with one addition : persistent edge-triggered descriptors which is from local dev version from stagelane itself.

The core architecture was suggested by [Alex Boisvert](https://github.com/aboisvert) all thanks to him. with last 2 addition and extras are by author.

## Architecture (M threads x N tasks)
* **M** worker threads, each with its own Stagelane scheduler and its own
  `SO_REUSEPORT` listener. A connection never leaves its worker: no locks, no
  hand-off queue, no cross-thread wakeups.
* **N** = `maxConns`: a semaphore bounds live connection tasks per worker. At the
  limit the worker stops calling `accept()` and the kernel backlog absorbs the
  burst (verified: 20 requests, limit 4 -> served in clean batches of 4).
* Handlers are plain procs **or `{.flow.}` procs** that may `delay`, use channels, etc.
  without blocking the worker.
* Zero allocation per request: in-place parser (`Span` views), leased scratch
  buffers (idle connections hold none), pipelined replies coalesced into one `send()`.
* Extras the original lacks: pipelining, `Connection: close`/HTTP 1.0, `Expect: 100-continue`,
  HEAD, chunked responses, `sendfile`, request-smuggling guards (CL+TE, duplicate CL,
  bare CR/LF, bad header names), 413/431/501, idle timeout, graceful SIGTERM.
  
## Build / run
    nim c -d:danger --threads:on --mm:arc --path:stagelane/src --path:. -o:demo examples/demo.nim
    ./demo 8083 4        # port, workers
    python3 tests/test_server.py 8083
Plain `--mm:arc` is enough (no `-d:flowThreads`): workers share nothing.

## Measured (1 worker, 1 core with the load generator, so only ratios matter)
| | original | stagehttp |
|---|---|---|
| 64 conns, no pipelining | ~105-170k req/s | ~200-300k req/s (1.6-1.9x) |
| server CPU per request | 3.7-4.0 us | 1.7-1.8 us (bare C epoll floor: 1.5 us) |
| 64 conns, pipeline 16 | does not pipeline (21 req/s) | 1.4-2.0M req/s |
| connection per request | never closes on `Connection: close` | ~37k conn/s |
| 10,000 conns | 5.98 us/req | 5.72 us/req (kernel/cache bound: no real gain) |
Memory is flat (2 MB RSS) after millions of requests; ASAN clean (no errors; ~60 KB of
shutdown-time stagelane frames reported by LSan).
  
## Stagelane change from local version not committed on Stagelane git till now.
`waitReadable` registers and unregisters the fd with epoll on every wait, and
`select` allocates a seq per poll. `PollFd` (`pioOpen/pioWaitRead/pioWaitWrite/pioClose`)
registers once, edge-triggered, latches readiness, skips the `recv()->EAGAIN`
probe after a short read, and polls with a raw `epoll_wait`. Legacy waits still
work alongside it; Linux only.


## Limits / not done
* Request bodies must fit in memory (`maxBodyBytes`); chunked *request* bodies -> 501.
* WebSocket/multipart servers still use the old dispatcher.
* Mostly focus was on linux part as i don't have windows or mac to test.
