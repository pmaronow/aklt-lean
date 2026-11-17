#!/usr/bin/env bash
set -euo pipefail
if [[ $# -lt 1 || $# -gt 2 ]]; then
  printf '%s\n' 'Usage: bash scripts/verify.sh /path/to/PalomarSubmission [/new/output/directory]' >&2
  exit 2
fi
aklt_verifier_path=$(cd "$1" && pwd)
aklt_package_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
aklt_output=${2:-$(mktemp -d /tmp/aklt-local-verification.XXXXXX)}
export PATH="$HOME/.elan/bin:$PATH"
exec python3 "$aklt_package_dir/scripts/release_verify.py" \
  --verifier "$aklt_verifier_path" --work "$aklt_output" --existing-dependencies
