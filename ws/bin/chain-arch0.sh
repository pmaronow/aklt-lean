#!/bin/bash
A=$HOME/aklt
while [ ! -e $A/flags/ARCH_0.done ]; do sleep 10; done
while tmux has-session -t MV_GEN_PACKED 2>/dev/null; do sleep 10; done
if ! head -1 $A/reports/ARCH_0/report.md | grep -q "STATUS: COMPLETE"; then head -1 $A/reports/ARCH_0/report.md > $A/flags/ARCH_0.attention; exit 0; fi
MV_MODE=fast $A/bin/merge-validate.sh ARCH_0 AKLT.Blueprint.Top.All "ARCH_0: statement layer (Challenge V2, Defs, Blueprint/Top interface Props, proved top assembly); under fidelity review" > $A/logs/MV_ARCH_0.log 2>&1 || { tail -3 $A/logs/MV_ARCH_0.log > $A/flags/ARCH_0.attention; exit 0; }
$A/bin/launch-wave2.sh > $A/logs/launch-wave2.log 2>&1
touch $A/flags/WAVE2_LAUNCHED.done
