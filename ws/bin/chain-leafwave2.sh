#!/bin/bash
set -uo pipefail
A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH
{
date -u
for K in BP_REC BP_H1M BP_H3M; do
  D=$(case $K in BP_REC) echo Rec;; BP_H1M) echo H1;; BP_H3M) echo H3;; esac)
  MV_MODE=fast $A/bin/merge-validate.sh $K AKLT.Blueprint.$D.AssemblyV2 "$K: adaptation to the repaired statement layer (V2 targets, new V2 leaves)" && touch $A/flags/MV_$K-ad.ok || echo "merge $K failed"
done
MV_MODE=fast $A/bin/merge-validate.sh UNIQ_TOP AKLT.W.UNIQ_TOP.TorusKernel "UNIQ_TOP (Luna): TorusKernelStatement from the uniqueness development" && touch $A/flags/MV_UNIQ_TOP.ok || echo "merge UNIQ_TOP failed"
KEYS=$(python3 $A/bin/truth_groups2.py REC H1M H3M | tail -1); echo "truth2: $KEYS"
$A/bin/launch-keys.sh max $KEYS
for k in $KEYS; do while [ ! -e $A/flags/$k.done ]; do sleep 20; done; done
$A/bin/merge-validate.sh MAIN - - || { echo "MAIN validation failed"; touch $A/flags/LEAFWAVE2.failed; exit 1; }
while [ ! -e $A/flags/PORT1-r5.done ]; do sleep 20; done
python3 - <<'PY'
import json,os,time
A=os.path.expanduser('~/aklt'); p=A+'/state/config.json'; c=json.load(open(p)); c['disk_abort_gb']=60; c['campaign_budget_gb']=250; c['disk_alarm_gb']=min(c.get('disk_alarm_gb',120),80)
json.dump(c,open(p,'w'),indent=2)
json.dump({'disk_abort_gb':60,'campaign_budget_gb':250,'reason':'production phase: leaf worktree builds and certificate pilots; volume growth awaiting author approval','set_by':'orchestrator','time':time.time()},open(A+'/state/disk-policy.json','w'),indent=1)
PY
cd $A/repo
for P in Rec H1 H3; do for f in AKLT/Blueprint/$P/*.lean; do case $(basename $f) in Assembly*.lean|Audit*.lean|All.lean|Counterexample.lean|LibraryChecks.lean) ;; *) $A/bin/aklt-freeze --blueprint $f >/dev/null || echo "freeze failed $f";; esac; done; done
python3 $A/bin/register_leaves.py Q GAP WIN MOM REC H1M H3M
$A/bin/aklt-status | head -12
touch $A/flags/LEAFWAVE2.done
} > $A/logs/chain-leafwave2.log 2>&1
