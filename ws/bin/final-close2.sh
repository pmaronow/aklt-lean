#!/bin/bash
# Remaining closing checks after source-configuration (which reported only the two author-metadata findings).
A=$HOME/aklt; R=$A/reports/FINAL/close
export PATH=$HOME/.elan/bin:$PATH
V=$HOME/dbl/scratch/PAL-DRY/tools/PalomarSubmission
cd $A/final
step() { echo "=== $(date -u "+%F %T") $*" >> $R/status; }
run() { n=$1; shift; mkdir -p $R/stages/$n; /usr/bin/time -v -o $R/stages/$n/time.log "$@" > $R/stages/$n/stdout.log 2> $R/stages/$n/stderr.log; rc=$?; step "$n exit $rc"; [ $rc -eq 0 ] || exit 1; }
step "continue after source-configuration (2 author-metadata findings); HEAD $(git rev-parse HEAD)"
run module-headers python3 scripts/verify_headers.py --verifier $V --report $R/headers.json
run physical-statement-comparison-and-negative-control python3 scripts/compare_statement.py --verifier $V --report-dir $R/statement --bwrap $A/reports/PAL_FIT/release/trusted-tools/bwrap --memory-gb 160
touch $A/flags/FINAL_CLOSE2.ok
