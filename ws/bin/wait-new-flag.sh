#!/bin/bash
# wait-new-flag.sh [MAX_SECONDS]: return as soon as a flag appears in ~/aklt/flags that is not listed in
# ~/aklt/state/flags-seen.txt; print the new flags (and mark them seen). Exit 1 on timeout.
A=$HOME/aklt; S=$A/state/flags-seen.txt; touch $S
for i in $(seq 1 $(( ${1:-3300} / 10 ))); do
  N=$(ls $A/flags | grep -vxFf $S || true)
  if [ -n "$N" ]; then echo "$N" | tee -a $S; echo "--- $(date -u +%H:%M:%S) running: $(tmux ls 2>/dev/null | cut -d: -f1 | tr '\n' ' ')"; exit 0; fi
  sleep 10
done
echo "timeout $(date -u +%H:%M:%S) running: $(tmux ls 2>/dev/null | cut -d: -f1 | tr '\n' ' ')"; exit 1
