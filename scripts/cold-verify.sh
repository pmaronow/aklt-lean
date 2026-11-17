#!/usr/bin/env bash
set -euo pipefail
aklt_script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec python3 "$aklt_script_dir/cold_verify.py" "$@"
