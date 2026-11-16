#!/bin/bash
# resume-writer.sh LANE: resume the writer session of LANE with its referee report.
set -euo pipefail
L=$1; A=$HOME/aklt
S=$(grep -l "\"name\": \"$L\"" ~/.cache/codex-sol/sessions/*.json | head -1 | xargs -n1 basename | sed 's/\.json$//')
[ -n "$S" ] || { echo "no session for $L"; exit 1; }
cat > $A/briefs/$L-resume1.md <<MSG
Orchestrator message: an independent referee report on your text is at $A/reports/REF_$L/report.md. The referee
saw only your files plus the cross-lane interface statements, not the other files of the same lane, so some
findings may say that a statement you use is "not supplied" when the plan assigns it to another file
(e.g. another section of your lane). For EVERY finding: (a) if it is a genuine defect in your text (wrong step,
missing hypothesis, missing case, wrong constant, mismatch with the plan), fix your text; (b) if the statement is
supplied by another file according to $A/reports/REV-PLAN/PLAN.md, make the citation explicit by plan label in
your text and check that you use it within its exact hypotheses (fix if not). Update your section files in place
and add a section "Response to referee" to your report.md with one row per finding: id, genuine? (yes/no),
action taken (file:line), and for (b) the plan label and where it is proved. Same rules as before.
MSG
cd $A/reports/$L && tmux new-session -d -s $L "cd $A/reports/$L; python3 $A/bin/sol-retry.py max 0 -- resume $S -f $A/briefs/$L-resume1.md -e max > $A/logs/$L-r1.out 2>&1; touch $A/flags/$L-r1.done"
echo "$L resumed ($S)"
