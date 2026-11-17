#!/bin/bash
# mergeset.sh CERTKEY PART ROOTMODULE: apply reports/CERTKEY/merge-set.txt (+ lakefile.toml) onto main, merge, build, plan leaves.
set -uo pipefail
C=$1; PART=$2; ROOT=$3; A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH; K=MS_$PART
{
while tmux has-session -t MV_FINAL 2>/dev/null; do sleep 10; done
cd $A/repo && git worktree add -q -b task/$K $A/wt/$K main && mkdir -p $A/wt/$K/.lake && ln -s $A/packages-store $A/wt/$K/.lake/packages && cp -a $A/repo/.lake/build $A/wt/$K/.lake/build
cd $A/wt/$C && while read -r f; do [ -n "$f" ] && mkdir -p "$A/wt/$K/$(dirname "$f")" && cp -a "$f" "$A/wt/$K/$f"; done < $A/reports/$C/merge-set.txt
grep -q 'name = "CertData"' $A/wt/$K/lakefile.toml || printf '\n# Generated certificate data and computations are opt-in.\n[[lean_lib]]\nname = "CertData"\nglobs = ["CertData"]\nleanOptions = { autoImplicit = false, relaxedAutoImplicit = false }\n' >> $A/wt/$K/lakefile.toml
cd $A/wt/$K && lake build $ROOT 2>&1 | tail -2
MV_MODE=fast $A/bin/merge-validate.sh $K $ROOT "$C merge set: hand-written certificate kernel, bridge statements and assemblies (no generated data)" || { echo MERGE-FAILED; touch $A/flags/$K.failed; exit 1; }
cd $A/repo && lake build $ROOT 2>&1 | tail -1
mkdir -p $A/reports/BP_$PART && cp $A/reports/$C/leaves-open.json $A/reports/BP_$PART/leaves.json
LW_BASE=main LW_SEED=$A/repo python3 $A/bin/lw5.py plan $PART
touch $A/flags/$K.done
} > $A/logs/$K.log 2>&1
