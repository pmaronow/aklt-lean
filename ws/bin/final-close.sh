#!/bin/bash
# Closing compile, strict audits, and release checks in the final tree.
A=$HOME/aklt; R=$A/reports/FINAL/close; cd $A/final || exit 1
export PATH=$HOME/.elan/bin:$PATH
V=$HOME/dbl/scratch/PAL-DRY/tools/PalomarSubmission
F="-j1 -DElab.async=false -DautoImplicit=false -DrelaxedAutoImplicit=false -DwarningAsError=true"
mkdir -p $R/stages
S=$R/status
step() { echo "=== $(date -u +%F\ %T) $*" | tee -a $S; }
run() { n=$1; shift; mkdir -p $R/stages/$n; /usr/bin/time -v -o $R/stages/$n/time.log "$@" > $R/stages/$n/stdout.log 2> $R/stages/$n/stderr.log; rc=$?; step "$n exit $rc"; [ $rc -eq 0 ] || exit 1; }
step "start; HEAD $(git rev-parse HEAD); digest $(python3 scripts/source_digest.py | tail -1)"
run strict-handwritten-audit lake env lean $F AuditHandwritten.lean
run handwritten-axiom-transcript python3 scripts/check_axioms.py $R/stages/strict-handwritten-audit/stdout.log --mode handwritten
run input-pins python3 scripts/verify_inputs.py --input-dir $A/relin --report $R/input-pins.json
mkdir -p .lake/build/lib/lean/CertData/Close
run close-CertData.Close.All lake env lean $F -o .lake/build/lib/lean/CertData/Close/All.olean CertData/Close/All.lean
run close-Solution lake env lean $F -o .lake/build/lib/lean/Solution.olean Solution.lean
run close-Audit lake env lean $F -o .lake/build/lib/lean/Audit.olean Audit.lean
run strict-full-audit lake env lean $F Audit.lean
run full-axiom-transcript python3 scripts/check_axioms.py $R/stages/strict-full-audit/stdout.log --mode full
run statement-generation-check python3 scripts/make_challenge.py --check
run source-configuration python3 scripts/verify_sources.py --verifier $V --report $R/source-checks.json
run module-headers python3 scripts/verify_headers.py --verifier $V --report $R/headers.json
run physical-statement-comparison-and-negative-control python3 scripts/compare_statement.py --verifier $V --report-dir $R/statement --bwrap $A/reports/PAL_FIT/release/trusted-tools/bwrap --memory-gb 160
touch $A/flags/FINAL_CLOSE.ok
