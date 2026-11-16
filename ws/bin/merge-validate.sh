#!/bin/bash
# merge-validate.sh KEY ROOTMODULE MSG : commit worktree KEY, ff/merge into main, full validation, move validated.
set -euo pipefail
K=$1; ROOT=$2; MSG=$3; A=$HOME/aklt; W=$A/wt/$K; exec 9>$A/state/merge.lock; flock 9; export PATH=$HOME/.elan/bin:$PATH
if [ "$K" = MAIN ]; then cd $A/repo; M=$(git rev-parse HEAD); else
cd $W
lake build $ROOT > $A/logs/mv-$K-build.log 2>&1 || { echo "BUILD FAILED"; exit 1; }
if [ -n "$(git status --porcelain)" ]; then
  git add -A
  if git diff --cached --name-only | xargs -r grep -lE '\b(sorry|admit|native_decide|implemented_by|unsafe|opaque)\b|^axiom |debug\.skipKernelTC' 2>/dev/null; then echo "FORBIDDEN TOKEN"; exit 1; fi
  git -c user.name=aklt-orchestrator -c user.email=noreply@anthropic.com commit -qm "$MSG"
fi
C=$(git rev-parse HEAD)
[ "$C" = "$(git -C $A/repo rev-parse main)" ] || git -C $A/repo merge-base --is-ancestor $C main && { echo "NOTHING NEW TO MERGE from $K ($C)"; exit 1; }
cd $A/repo; git merge -q --no-edit task/$K -m "Merge $K" ; M=$(git rev-parse HEAD)
fi
V=$A/wt/VAL-$K; rm -rf $V; git worktree prune; git worktree add -q --detach $V $M; mkdir -p $V/.lake; ln -s $A/repo/.lake/packages $V/.lake/packages; [ -d $A/repo/.lake/build ] && cp -a $A/repo/.lake/build $V/.lake/build; cd $V
lake build > $A/logs/mv-$K-fullbuild.log 2>&1 || { echo "FULL BUILD FAILED at $M"; exit 1; }
sha256sum -c $A/state/frozen.sha256 >/dev/null
( cd $A/repo && nohup lake build > $A/logs/repo-warm-build.log 2>&1 & )
if [ "${MV_MODE:-full}" = fast ]; then echo "MERGED-FAST $M (build + token scan + frozen hashes; validated not moved)" | tee $A/logs/mv-$K-fast.result; exit 0; fi
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
$TC/con-ron --verified --jobs=8 $D/export.ndjson > $D/con-ron.log 2>&1; grep -q "accepted .* declarations (--verified)" $D/con-ron.log
sed "s#/home/ubuntu/aklt/val/baseline/export.ndjson#$D/export.ndjson#" $A/val/baseline/nanoda.json > $D/nanoda.json
$TC/nanoda_bin $D/nanoda.json > $D/nanoda.log 2>&1; grep -q "no typechecker errors" $D/nanoda.log
cd $A/repo; git branch -f validated $M
echo "VALIDATED $M names=$(grep -c . $D/names.txt) $(tail -1 $D/con-ron.log) | $(head -1 $D/nanoda.log | cut -c1-80)" | tee $D/RESULT
rm -f $D/export.ndjson
