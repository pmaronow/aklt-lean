#!/bin/bash
# merge-after2.sh PREVFLAG KEY ROOT MSG [MODE]: wait for PREVFLAG; run merge-validate; write MV_KEY.ok only on success, MV_KEY.failed otherwise.
set -uo pipefail
A=$HOME/aklt; while [ ! -e $A/flags/$1 ]; do sleep 20; done
if MV_MODE=${5:-full} $A/bin/merge-validate.sh "$2" "$3" "$4" > $A/logs/MV_$2.log 2>&1; then touch $A/flags/MV_$2.ok; else tail -3 $A/logs/MV_$2.log > $A/flags/MV_$2.failed; fi
