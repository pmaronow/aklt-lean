#!/bin/bash
# launch-keys.sh EFFORT KEY...: launch report-dir-only Sol agents (brief briefs/KEY.md, cwd reports/KEY).
A=$HOME/aklt; E=$1; shift
for K in "$@"; do
  [ -e $A/flags/$K.done ] && continue; tmux has-session -t $K 2>/dev/null && continue
  until $A/bin/aklt-budget-check 1 >/dev/null 2>&1; do sleep 60; done
  mkdir -p $A/reports/$K
  tmux new-session -d -s $K "cd $A/reports/$K; export PATH=\$HOME/.elan/bin:\$PATH; python3 $A/bin/sol-retry.py $E 0 -- run -C $A/reports/$K --write -e $E --name $K -f $A/briefs/$K.md > $A/logs/$K.out 2>&1; touch $A/flags/$K.done"; sleep 2
done
