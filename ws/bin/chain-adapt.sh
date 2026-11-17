#!/bin/bash
set -uo pipefail
A=$HOME/aklt
until git -C $A/repo merge-base --is-ancestor 6d0bd35 main 2>/dev/null; do sleep 15; done
for K in BP_REC BP_H1M BP_H3M; do
  cd $A/wt/$K && git add -A >/dev/null 2>&1; git -c user.name=aklt-orchestrator -c user.email=noreply@anthropic.com commit -qm "wip $K before adaptation" >/dev/null 2>&1; git merge -q --no-edit main || { echo "$K merge conflict" > $A/flags/$K-adapt.attention; continue; }
  S=$(grep -l "\"name\": \"$K\"" ~/.cache/codex-sol/sessions/*.json | head -1 | xargs -n1 basename | sed "s/\.json//")
  until $A/bin/aklt-budget-check 1 >/dev/null 2>&1; do sleep 60; done
  tmux new-session -d -s ${K}_AD "cd $A/wt/$K; export PATH=\$HOME/.elan/bin:\$PATH; python3 $A/bin/sol-retry.py max 0 -- resume $S -f $A/briefs/BP-ADAPT.md -e max > $A/logs/$K-adapt.out 2>&1; touch $A/flags/$K-adapt.done"
done
