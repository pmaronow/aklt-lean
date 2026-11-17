#!/bin/bash
# Final tree: cold hand-written build, then H3 regeneration + fresh kernel-checked build + closing + verify.
A=$HOME/aklt; R=$A/reports/FINAL; cd $A/final || exit 1
export PATH=$HOME/.elan/bin:$PATH
export H3_INPUT_DIR=$A/compfeas/data
export H3_REPORT_DIR=$R/H3
step() { echo "=== $(date -u +%F\ %T) $*" | tee -a $R/logs/final-h3.status; }
step "start; HEAD $(git rev-parse HEAD)"
step "hand-written cold build"
LEAN_NUM_THREADS=14 /usr/bin/time -v lake build Handwritten Challenge Regression.Solution Regression.Audit AuditHandwritten RegenSamples.H1Consumer RegenSamples.H3Consumer > $R/logs/handwritten-build.log 2>&1 || { step "FAIL handwritten build"; exit 1; }
step "hand-written build OK"
python3 AKLT/Cert/H3/regen.py generate > $R/logs/h3-generate.log 2>&1 || { step "FAIL h3 generate"; exit 1; }
step "h3 generate OK"
python3 AKLT/Cert/H3/regen.py build --jobs 16 --ram-gb 160 > $R/logs/h3-build.log 2>&1 || { step "FAIL h3 build"; exit 1; }
step "h3 build OK"
python3 AKLT/Cert/H3/regen.py close --stage closing --jobs 1 --ram-gb 160 > $R/logs/h3-close.log 2>&1 || { step "FAIL h3 close"; exit 1; }
step "h3 close OK"
python3 AKLT/Cert/H3/regen.py verify > $R/logs/h3-verify.log 2>&1 || { step "FAIL h3 verify"; exit 1; }
step "h3 verify OK"
touch $A/flags/FINAL_H3.ok
