#!/bin/bash
# conron-check.sh WT OUT MODULE... : export the public declarations of the given modules (with their dependency
# closure) from worktree WT and run con-ron --verified (progress on, killed above CAP_GB, default 24) and NanoDa.
set -uo pipefail
WT=$1; OUT=$2; shift 2; A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH; mkdir -p $OUT; cd $WT
TC=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin; CAP=$(( ${CAP_GB:-24} * 1048576 ))
lake build "$@" > $OUT/build.log 2>&1 || { echo "BUILD FAILED (see $OUT/build.log)"; exit 2; }
S=CrChk$$; { for m in "$@"; do echo "import $m"; done; echo "open Lean in"; echo "#eval show CoreM Unit from do"; echo "  let env ← getEnv"
  echo "  let mods : List String := [$(printf '"%s", ' "$@" | sed 's/, $//')]"
  cat <<LEAN
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some i => if mods.contains (env.header.moduleNames[i.toNat]!).toString && !n.isInternal then out := out.push n.toString
    | none => pure ()
  IO.FS.writeFile "$OUT/names.txt" ((String.intercalate "\n" (out.qsort (· < ·)).toList) ++ "\n")
LEAN
} > $OUT/$S.lean
cp $OUT/$S.lean $WT/$S.lean; lake env lean $WT/$S.lean; RCN=$?; rm -f $WT/$S.lean; [ $RCN = 0 ] || { echo "NAME LISTING FAILED"; exit 2; }
M=CrAll$$; trap 'rm -f $WT/$M.lean $WT/$M.olean' EXIT
for m in "$@"; do echo "import $m"; done > $WT/$M.lean
lake env lean -o $WT/$M.olean $WT/$M.lean
LEAN_PATH="$WT:$(lake env printenv LEAN_PATH)" lake env leanexport $M -- $(cat $OUT/names.txt) > $OUT/export.ndjson 2> $OUT/export.err
[ -s $OUT/export.err ] && { echo "EXPORT STDERR"; head -5 $OUT/export.err; exit 2; }
$TC/con-ron --verified --jobs=4 --progress=1 $OUT/export.ndjson > $OUT/con-ron.log 2> $OUT/progress.log &
P=$!; T0=$(date +%s); PEAK=0
while kill -0 $P 2>/dev/null; do
  R=$(awk '/VmRSS/{print $2}' /proc/$P/status 2>/dev/null || echo 0); [ "${R:-0}" -gt $PEAK ] && PEAK=$R
  if [ "${R:-0}" -gt $CAP ]; then kill $P; echo "CON-RON KILLED: resident memory above ${CAP_GB:-24} GB after $(( $(date +%s) - T0 )) s"; echo "last finished checks:"; tail -3 $OUT/progress.log | cut -c1-200; echo "(a declaration absent from progress.log's 'check' lines is one that did not finish)"; rm -f $OUT/export.ndjson; exit 1; fi
  sleep 1
done
wait $P; RC=$?
echo "con-ron exit=$RC peak_rss_gb=$(( PEAK / 1048576 )) time_s=$(( $(date +%s) - T0 )): $(tail -1 $OUT/con-ron.log | cut -c1-200)"
grep -q "accepted .* declarations (--verified)" $OUT/con-ron.log || { rm -f $OUT/export.ndjson; exit 1; }
sed "s#/home/ubuntu/aklt/val/baseline/export.ndjson#$OUT/export.ndjson#" $A/val/baseline/nanoda.json > $OUT/nanoda.json
/usr/bin/time -f "nanoda time_s=%e peak_rss_kb=%M" timeout 3600 $TC/nanoda_bin $OUT/nanoda.json > $OUT/nanoda.log 2> $OUT/nanoda.time; NR=$?
echo "nanoda exit=$NR $(head -1 $OUT/nanoda.log | cut -c1-120) $(tail -1 $OUT/nanoda.time)"
rm -f $OUT/export.ndjson
grep -q "no typechecker errors" $OUT/nanoda.log && echo "BOTH CHECKERS ACCEPT" || exit 1
