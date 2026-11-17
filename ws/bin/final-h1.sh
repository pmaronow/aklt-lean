#!/bin/bash
# From-scratch H1 certificate build in the final release tree (from numeric inputs).
A=$HOME/aklt; R=$A/reports/FINAL; H=$R/H1; cd $A/final || exit 1
export PATH=$HOME/.elan/bin:$PATH
export H1_REGEN_REPORT=$H
T=AKLT/Cert/H1/tools
mkdir -p $H $R/logs
step() { echo "=== $(date -u +%F\ %T) $*" | tee -a $R/logs/final-h1.status; }
fail() { step "FAILED: $*"; exit 1; }
step "start; HEAD $(git rev-parse HEAD); digest $(python3 scripts/source_digest.py | tail -1)"
python3 $T/production_bootstrap.py > $R/logs/h1-bootstrap.log 2>&1 || fail bootstrap
step "bootstrap OK"
python3 $T/production_receipts.py inputs --output $H/data-input-receipt.json > $R/logs/h1-inputs.log 2>&1 || fail inputs
step "inputs OK"
python3 $T/production_reexport.py --scratch $A/scratch/FINAL_H1 --install --report-dir $H > $R/logs/h1-reexport.log 2>&1 || fail reexport
step "reexport+install OK"
python3 $T/production_build.py $H/data-only-production.json --jobs 35 --cap-gib 7 --report-dir $H --jobs-file $H/jobs > $R/logs/h1-build.log 2>&1 || fail build
step "build OK"
python3 $T/production_receipts.py verify $H/data-only-production.json --report-dir $H > $R/logs/h1-verify.log 2>&1 || fail verify
step "verify OK"
python3 $T/production_close.py --report-dir $H > $R/logs/h1-close.log 2>&1 || fail close
step "close OK"
touch $A/flags/FINAL_H1.ok
