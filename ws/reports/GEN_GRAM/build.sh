#!/usr/bin/env bash
# Rebuild only this library, serially, against the linked prebuilt Mathlib.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd /home/ubuntu/aklt/wt/GEN_GRAM
compile() {
  local gram_module="$1"
  local gram_path="${gram_module//.//}"
  mkdir -p ".lake/build/lib/lean/$(dirname "$gram_path")"
  lake env lean -o ".lake/build/lib/lean/$gram_path.olean" "$gram_path.lean"
}
for gram_module in Theory Checker Basic Examples CoreAudit; do
  compile "AKLT.Gen.Gram.$gram_module"
done
for gram_family in Sample131 Random179; do
  compile "AKLT.Gen.Gram.$gram_family.Data"
  compile "AKLT.Gen.Gram.$gram_family.Header"
  for gram_source in AKLT/Gen/Gram/"$gram_family"/Rows*.lean; do
    gram_module="${gram_source%.lean}"
    compile "${gram_module//\//.}"
  done
  compile "AKLT.Gen.Gram.$gram_family.Certificate"
  compile "AKLT.Gen.Gram.$gram_family.Baseline"
done
compile AKLT.Gen.Gram.Audit
