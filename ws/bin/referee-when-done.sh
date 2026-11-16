#!/bin/bash
# referee-when-done.sh LANE: wait for ~/aklt/flags/LANE.done; if its report says COMPLETE, snapshot the lane's .tex
# files (LaTeX comment lines stripped), check for review-history words, and launch a blind Sol max referee REF_LANE.
set -uo pipefail
L=$1; K=REF_$L; A=$HOME/aklt
while [ ! -e $A/flags/$L.done ]; do sleep 30; done
if ! head -1 $A/reports/$L/report.md 2>/dev/null | grep -q "STATUS: COMPLETE"; then echo "$L not COMPLETE" > $A/flags/$K.attention; exit 0; fi
R=$A/review/$K; mkdir -p $R/part $A/reports/$K
for f in $A/reports/$L/*.tex; do b=$(basename $f); case $b in wrapper*|test*|main*) continue;; esac; sed -e '/^[[:space:]]*%/d' -e 's/\([^\\]\)%.*$/\1/' $f > $R/part/$b; done
cp $A/reports/REV-PLAN/interfaces.tex $R/interfaces.tex
sed -i -e '/^[[:space:]]*%/d' $R/interfaces.tex
if grep -qiE "amended|adjudicat|ADJ-|REF-|refereed|corrected (manuscript|version)|baseline|deviation|REV-PLAN|STRENGTHEN|MOSPROOF|OPPORTUNIT|COMPFEAS" $R/part/* $R/interfaces.tex; then grep -niE "amended|adjudicat|ADJ-|REF-|refereed|corrected (manuscript|version)|baseline|deviation|REV-PLAN|STRENGTHEN|MOSPROOF|OPPORTUNIT|COMPFEAS" $R/part/* $R/interfaces.tex | head -40 > $A/flags/$K.attention; exit 0; fi
chmod -R a-w $R
sed "s/__KEY__/$K/g" $A/briefs/REFL-COMMON.md > $A/briefs/$K.md
while ! $A/bin/aklt-budget-check 1 >/dev/null 2>&1; do sleep 300; done
cd $A/reports/$K && python3 $A/bin/sol-retry.py max 1 -- run -C $A/reports/$K --write --search -e max --name $K -f $A/briefs/$K.md > $A/logs/$K.out 2>&1
touch $A/flags/$K.done
