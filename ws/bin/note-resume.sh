#!/bin/bash
# note-resume.sh KEY CWD ADD_DIRS(comma) NOTEFILE: stop a running Sol task and resume the same session (max) with a note.
set -uo pipefail
K=$1; C=$2; ADD=$3; NOTE=$4; A=$HOME/aklt
R=$(grep -l -m1 "^.*# $K — " $(ls -t ~/.codex-yale/sessions/2026/11/16/rollout-*.jsonl | head -150) 2>/dev/null | head -1)
[ -n "$R" ] || { echo "$K: rollout not found"; exit 1; }
S=$(basename $R .jsonl | sed -E 's/^rollout-[0-9T:-]+-//' | grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$')
tmux kill-session -t $K 2>/dev/null; sleep 2
python3 - "$S" "$K" "$C" "$ADD" <<'PY'
import json,sys,os
s,k,c,add=sys.argv[1:5]
json.dump({"cwd":c,"sandbox":"workspace-write","name":k,"add_dirs":[d for d in add.split(",") if d]},open(os.path.expanduser(f"~/.cache/codex-sol/sessions/{s}.json"),"w"))
PY
tmux new-session -d -s $K "cd $C; export PATH=\$HOME/.elan/bin:\$PATH; python3 $A/bin/sol-retry.py max 0 -- resume $S -f $NOTE -e max > $A/logs/$K-note.out 2>&1; touch $A/flags/$K.done"
echo "$K resumed $S"
