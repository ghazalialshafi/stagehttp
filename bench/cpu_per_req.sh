#!/bin/bash
# usage: cpu_per_req.sh <binary> <port> <conns> <pipe> [secs]
BIN=$1; PORT=$2; C=$3; P=$4; T=${5:-4}
setsid nohup $BIN >/dev/null 2>&1 < /dev/null &
sleep 0.7
PID=$(pgrep -f "^$BIN" | head -1)
ticks() { awk '{print $14+$15, $14, $15}' /proc/$PID/stat; }
read t0 u0 s0 < <(ticks)
OUT=$(./load $PORT $C $P $T /hello)
read t1 u1 s1 < <(ticks)
RATE=$(echo "$OUT" | sed 's/.* \([0-9]*\) req\/s/\1/')
CLK=$(getconf CLK_TCK)
awk -v r=$RATE -v T=$T -v t=$((t1-t0)) -v u=$((u1-u0)) -v s=$((s1-s0)) -v clk=$CLK -v name=$BIN 'BEGIN{reqs=r*T; printf "%-12s %8d req/s | server CPU/req: %.2f us (user %.2f + sys %.2f)\n", name, r, t/clk*1e6/reqs, u/clk*1e6/reqs, s/clk*1e6/reqs}'
kill $PID 2>/dev/null; sleep 0.3
