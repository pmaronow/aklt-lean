#!/bin/bash
A=$HOME/aklt; K=$1
while tmux has-session -t $K 2>/dev/null; do sleep 15; done
S=$(grep -l "\"name\": \"$K\"" ~/.cache/codex-sol/sessions/*.json | head -1 | xargs -n1 basename | sed "s/\.json//")
python3 - "$S" "$K" <<PY
import json,sys,os
s,k=sys.argv[1:3]; A=os.path.expanduser("~/aklt")
json.dump({"cwd":f"{A}/wt/{k}","sandbox":"workspace-write","name":k,"add_dirs":[f"{A}/reports/{k}",f"{A}/scratch/{k}"]},open(os.path.expanduser(f"~/.cache/codex-sol/sessions/{s}.json"),"w"))
PY
until $A/bin/aklt-budget-check 1 >/dev/null 2>&1; do sleep 60; done
cd $A/wt/$K; export PATH=$HOME/.elan/bin:$PATH
python3 $A/bin/sol-retry.py max 0 -- resume $S -f $A/briefs/CERT-PHASE2.md -e max > $A/logs/$K-p2.out 2>&1; touch $A/flags/$K-p2.done
