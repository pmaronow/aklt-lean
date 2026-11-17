#!/bin/bash
# validate-main.sh: full validation (clean build, names, export, con-ron --verified, NanoDa) of the current main,
# WITHOUT holding state/merge.lock (merges continue meanwhile). Moves `validated` on success.
set -euo pipefail
A=$HOME/aklt; exec 8>$A/state/validate.lock; flock 8; export PATH=$HOME/.elan/bin:$PATH
exec 9>$A/state/merge.lock; flock 9; M=$(git -C $A/repo rev-parse main); V=$A/wt/VAL-MAIN; rm -rf $V; cd $A/repo; git worktree prune; git worktree add -q --detach $V $M; flock -u 9
mkdir -p $V/.lake; ln -s $A/repo/.lake/packages $V/.lake/packages; cp -a $A/seed/.lake/build $V/.lake/build; cd $V
lake build > $A/logs/mv-MAIN-fullbuild.log 2>&1 || { echo "FULL BUILD FAILED at $M"; exit 1; }
sha256sum -c $A/state/frozen.sha256 >/dev/null
if git ls-files AKLT | grep '\.lean$' | xargs grep -lE '\b(sorry|admit|native_decide|implemented_by|unsafe)\b|^axiom |debug\.skipKernelTC' 2>/dev/null | grep -v -F -f <(echo AKLT/__none__) | head -5 | grep . ; then echo "TOKEN HIT (inspect; may be in comments)"; fi
D=$A/val/$M; mkdir -p $D
{ find AKLT -name '*.lean' | sed -e 's#\.lean$##' -e 's#/#.#g' | LC_ALL=C sort | sed 's/^/import /'; cat <<LEAN
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    if (\`AKLT).isPrefixOf n && !n.isInternal then out := out.push n.toString
  IO.FS.writeFile "$D/names.txt" ((String.intercalate "\n" (out.qsort (· < ·)).toList) ++ "\n")
LEAN
} > $D/names.lean
lake env lean $D/names.lean
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin
find AKLT -name '*.lean' | sed -e 's#\.lean$##' -e 's#/#.#g' | LC_ALL=C sort | sed 's/^/import /' > AKLTValAll.lean
lake env lean -o AKLTValAll.olean AKLTValAll.lean
LEAN_PATH="$PWD:$(lake env printenv LEAN_PATH)" lake env leanexport AKLTValAll -- $(cat $D/names.txt) > $D/export.ndjson 2> $D/export.err
[ -s $D/export.err ] && { echo "EXPORT STDERR"; head $D/export.err; exit 1; }
$TC/con-ron --verified --jobs=16 $D/export.ndjson > $D/con-ron.log 2>&1; grep -q "accepted .* declarations (--verified)" $D/con-ron.log
sed "s#/home/ubuntu/aklt/val/baseline/export.ndjson#$D/export.ndjson#" $A/val/baseline/nanoda.json > $D/nanoda.json
$TC/nanoda_bin $D/nanoda.json > $D/nanoda.log 2>&1; grep -q "no typechecker errors" $D/nanoda.log
cd $A/repo; git merge-base --is-ancestor $M main && git branch -f validated $M
echo "VALIDATED $M names=$(grep -c . $D/names.txt) $(tail -1 $D/con-ron.log) | $(head -1 $D/nanoda.log | cut -c1-80)" | tee $D/RESULT
rm -f $D/export.ndjson
