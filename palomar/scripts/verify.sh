#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  printf '%s\n' 'Usage: bash scripts/verify.sh /path/to/PalomarSubmission' >&2
  exit 2
fi
aklt_verifier_path=$(cd "$1" && pwd)
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS=1
python3 scripts/verify_sources.py --verifier "$aklt_verifier_path" --report verification/source-checks.json
lake build Solution
lake build Audit
lake env lean -j1 -DautoImplicit=false -DwarningAsError=true Audit.lean | tee verification/axioms.log
python3 scripts/check_axioms.py verification/axioms.log
# Local full Comparator uses its own sandbox. Protected production verification
# additionally substitutes a canonical Challenge and enforces NanoDa externally.
lake comparator --config comparator.json --paranoid
