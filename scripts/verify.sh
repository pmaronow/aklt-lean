#!/usr/bin/env bash
set -euo pipefail
aklt_script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec bash "$aklt_script_dir/cold-verify.sh" "$@"
