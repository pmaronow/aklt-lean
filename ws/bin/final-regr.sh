#!/bin/bash
A=$HOME/aklt; cd $A/regr || exit 1
export PATH=$HOME/.elan/bin:$PATH
python3 scripts/release_verify.py --verifier $HOME/dbl/scratch/PAL-DRY/tools/PalomarSubmission --work $A/reports/FINAL/regression --existing-dependencies --regression-inputs --bwrap $A/reports/PAL_FIT/release/trusted-tools/bwrap --build-threads 14 > $A/reports/FINAL/logs/regression.log 2>&1
echo "exit $?" >> $A/reports/FINAL/logs/regression.log
