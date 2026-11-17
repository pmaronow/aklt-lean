#!/bin/bash
set -euo pipefail
TC="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin"
export PATH="$TC:$PATH"
export LEAN_PATH=/home/ubuntu/aklt/reports/REL_FEAS/scratch/lib
cd /home/ubuntu/aklt/reports/REL_FEAS/scratch/lib
"$TC/lean" -c RELFEAS/FastExportV2.c RELFEAS/FastExportV2.lean
"$TC/lean" -c RELFEAS/FastMainV2.c RELFEAS/FastMainV2.lean
"$TC/leanc" -O3 -o /home/ubuntu/aklt/reports/REL_FEAS/fast-leanexport RELFEAS/FastExportV2.c RELFEAS/FastMainV2.c
