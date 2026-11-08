version       = "0.1.0"
author        = "stagelane contributors"
description   = "Stagelane: continuation-passing style and structured concurrency for Nim (ARC/ORC)"
license       = "MIT"
srcDir        = "src"

requires "nim >= 2.2.0"

task test, "run the test-suite under ARC, ORC and atomicArc+threads (with ASAN)":
  exec "sh tests/run_all.sh"

task bench, "run the micro benchmarks":
  exec "nim c -d:danger --mm:arc -r bench/bench.nim"
  exec "nim c -d:danger --mm:arc -r bench/vs_async.nim"
