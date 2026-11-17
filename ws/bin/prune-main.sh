#!/bin/bash
# prune-main.sh: under the merge lock, delete stray leaf files (outside Main's import closure) on main, commit, build.
set -uo pipefail
A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH; exec 9>$A/state/merge.lock; flock 9; cd $A/repo
KEYS=$(python3 -c "import json;d=json.load(open('$A/state/lw/leaves.json'));print(' '.join(k for k,x in d.items() if x['state']=='merged'))")
python3 $A/bin/prune_stray.py $A/repo $KEYS --delete > $A/logs/prune-main.list
wc -l < $A/logs/prune-main.list
if [ -s $A/logs/prune-main.list ]; then git add -A AKLT/W && git -c user.name=aklt-orchestrator -c user.email=noreply@anthropic.com commit -qm "Remove leaf files outside the proofs' import closure (scratch, audit and test files; some did not compile)

Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01DtFRS1A1TmhbdfqkiHSKuL"; fi
lake build 2>&1 | tail -4
git log --oneline -1
