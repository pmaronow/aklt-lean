#!/bin/bash
A=$HOME/aklt
$A/bin/merge-after2.sh ARCH_UNIQ.done ARCH_UNIQ AKLT.Uniq.Main "ARCH_UNIQ: uniqueness of the ground state for every L,N>=3 (22 nodes proved; provisional pending validation)" fast
[ -e $A/flags/MV_ARCH_UNIQ.ok ] || exit 0
$A/bin/aklt-mkwt UNIQ_TOP main >/dev/null; mkdir -p $A/reports/UNIQ_TOP
until $A/bin/aklt-budget-check 1 >/dev/null 2>&1; do sleep 60; done
cd $A/wt/UNIQ_TOP; export PATH=$HOME/.elan/bin:$PATH
python3 $A/bin/luna-retry.py xhigh 0 -- run -C $A/wt/UNIQ_TOP --write --add-dir $A/reports/UNIQ_TOP -e xhigh --name UNIQ_TOP -f $A/briefs/UNIQ_TOP.md > $A/logs/UNIQ_TOP.out 2>&1; touch $A/flags/UNIQ_TOP.done
