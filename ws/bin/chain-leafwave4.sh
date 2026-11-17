#!/bin/bash
set -uo pipefail
A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH; export LAKE_ARTIFACT_CACHE=true
{
date -u
cd $A/scratch/CT1 && lake build 2>&1 | tail -1
du -sh $HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/lake/cache | cut -f1
cd $A/repo; git worktree prune
python3 $A/bin/register_leaves.py Q GAP WIN MOM REC H1M H3M | tail -3
date -u
tmux new-session -d -s aklt-queue "$A/bin/aklt-queue --loop"
tmux new-session -d -s aklt-integrator "export LAKE_ARTIFACT_CACHE=true; $A/bin/aklt-integrator --loop"
tmux new-session -d -s aklt-ladder "export LAKE_ARTIFACT_CACHE=true; $A/bin/aklt-ladder --loop"
tmux new-session -d -s aklt-cleaner "$A/bin/aklt-cleaner --loop"
$A/bin/aklt-digest --start
sleep 90; $A/bin/aklt-status | grep -v "^Stale" | sed -n 1,12p
touch $A/flags/LEAFWAVE4.done
} > $A/logs/chain-leafwave4.log 2>&1
