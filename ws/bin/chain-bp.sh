#!/bin/bash
set -uo pipefail
A=$HOME/aklt
m() { if MV_MODE=fast $A/bin/merge-validate.sh "$1" "$2" "$3" > $A/logs/MV_$1.log 2>&1; then touch $A/flags/MV_$1.ok; else tail -3 $A/logs/MV_$1.log > $A/flags/MV_$1.failed; fi; }
m CERT_H2 AKLT.Cert.H2.Main "CERT_H2: (H2) input proved (memory-6 one-step certificate, kernel-checked); provisional pending validation"
m BP_Q AKLT.Blueprint.Q.Assembly "BP_Q: blueprint for frames and quantum-classical comparison (61 leaves)"
m BP_GAP AKLT.Blueprint.Gap.Assembly "BP_GAP: blueprint for the periodic block gap and main assembly (58 leaves)"
m BP_WIN AKLT.Blueprint.Win.Assembly "BP_WIN: blueprint for windows from the response property (74 leaves)"
m BP_MOM AKLT.Blueprint.Mom.Assembly "BP_MOM: blueprint for finite moments (33 leaves)"
m BP_REC AKLT.Blueprint.Rec.Assembly "BP_REC: blueprint for walk expansion and recursion (88 leaves)"
m BP_H3M AKLT.Blueprint.H3.Assembly "BP_H3M: blueprint for the stationary H3 mathematics (30 leaves)"
m BP_H1M AKLT.Blueprint.H1.Assembly "BP_H1M: blueprint for the operator-only H1 mathematics (55 leaves)"
touch $A/flags/BP_MERGED.done
KEYS=$(python3 $A/bin/truth_groups.py Q GAP WIN MOM REC H3M H1M)
$A/bin/launch-keys.sh max $KEYS
touch $A/flags/TRUTH_LAUNCHED.done
