#!/bin/bash
# conron-diag.sh EXPORT OUTDIR : run con-ron with per-check progress and kill it when RSS exceeds 120 GB.
E=$1; O=$2; mkdir -p $O; TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin
$TC/con-ron --verified --jobs=16 --progress=1 $E > $O/out.log 2> $O/progress.log &
P=$!
while kill -0 $P 2>/dev/null; do
  R=$(awk "/VmRSS/{print \$2}" /proc/$P/status 2>/dev/null || echo 0)
  echo "$(date -u +%T) rss_kb=$R $(tail -1 $O/progress.log | cut -c1-160)" >> $O/watch.log
  if [ "${R:-0}" -gt 125829120 ]; then echo "KILLED at rss_kb=$R" >> $O/watch.log; kill $P; break; fi
  sleep 5
done
wait $P; echo "exit=$?" >> $O/watch.log; touch $O/done
