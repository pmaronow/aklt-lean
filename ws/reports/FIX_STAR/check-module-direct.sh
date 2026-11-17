#!/bin/bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
Q=$1
OUT=$2
mkdir -p "$OUT"
python3 - "$Q" > "$OUT/roots.txt" <<'PY'
import re,sys
q=sys.argv[1]
s=open(f'AKLT/W/{q}/Main.lean').read()
for n in re.findall(r'^(?:theorem|def|abbrev) (\w+)',s,re.M): print(f'AKLT.W.{q}.{n}')
PY
lake env leanexport "AKLT.W.$Q.Main" -- $(cat "$OUT/roots.txt") > "$OUT/export.ndjson" 2> "$OUT/export.err"
python3 /home/ubuntu/aklt/reports/FIX_STAR/check-export.py "$OUT" "$OUT/export.ndjson"
python3 /home/ubuntu/aklt/reports/FIX_STAR/export-names.py "$OUT/export.ndjson" "AKLT.W.$Q" "$OUT/progress.log" > "$OUT/declarations.txt"
cat "$OUT/declarations.txt" | rg MISSING || true
