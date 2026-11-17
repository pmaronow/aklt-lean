#!/bin/bash
set -uo pipefail
A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH; L=$A/logs/chain-leafwave1.log
{
MV_MODE=fast $A/bin/merge-validate.sh ARCH_0 AKLT.Blueprint.Top.All "merge STMT_FIX" || { echo "STMT merge failed"; touch $A/flags/LEAFWAVE1.failed; exit 1; }
$A/bin/merge-validate.sh MAIN - - || { echo "MAIN validation failed"; touch $A/flags/LEAFWAVE1.failed; exit 1; }
cd $A/repo
for P in Q Gap Win Mom; do for f in AKLT/Blueprint/$P/*.lean; do case $(basename $f) in Assembly.lean|Audit.lean|All.lean|LibraryChecks.lean) ;; *) $A/bin/aklt-freeze --blueprint $f || echo "freeze failed $f";; esac; done; done
for f in AKLT/Blueprint/Top/*.lean; do case $(basename $f) in Assembly.lean|Audit.lean|All.lean) ;; *) $A/bin/aklt-freeze --blueprint $f || echo "freeze failed $f";; esac; done
python3 $A/bin/register_leaves.py Q GAP WIN MOM
tmux new-session -d -s aklt-queue "$A/bin/aklt-queue --loop"
tmux new-session -d -s aklt-integrator "$A/bin/aklt-integrator --loop"
tmux new-session -d -s aklt-ladder "$A/bin/aklt-ladder --loop"
$A/bin/aklt-digest --start
tmux new-session -d -s aklt-cleaner "$A/bin/aklt-cleaner --loop"
touch $A/flags/LEAFWAVE1.done
} > $L 2>&1
