#!/bin/bash
set -uo pipefail
A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH
{
while [ ! -e $A/flags/PORT1-r6.done ]; do sleep 15; done
date -u; $A/bin/aklt-status | sed -n 1,10p
for s in aklt-queue aklt-integrator aklt-ladder aklt-cleaner aklt-digest; do tmux kill-session -t $s 2>/dev/null; done
cd $A/repo
for P in Rec H1 H3; do for f in AKLT/Blueprint/$P/*.lean; do case $(basename $f) in Assembly*.lean|Audit*.lean|All.lean|Counterexample.lean|LibraryChecks.lean) ;; *) $A/bin/aklt-freeze --blueprint $f >/dev/null || echo "freeze failed $f";; esac; done; done
wc -l < $A/state/frozen.sha256
python3 $A/bin/register_leaves.py Q GAP WIN MOM REC H1M H3M | tail -3
tmux new-session -d -s aklt-queue "$A/bin/aklt-queue --loop"
tmux new-session -d -s aklt-integrator "$A/bin/aklt-integrator --loop"
tmux new-session -d -s aklt-ladder "$A/bin/aklt-ladder --loop"
tmux new-session -d -s aklt-cleaner "$A/bin/aklt-cleaner --loop"
$A/bin/aklt-digest --start
sleep 60; $A/bin/aklt-status | sed -n 1,10p
touch $A/flags/LEAFWAVE3.done
} > $A/logs/chain-leafwave3.log 2>&1
