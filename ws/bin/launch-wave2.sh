#!/bin/bash
# launch-wave2.sh: after ARCH_0 is committed and merged into main, create worktrees and launch the part
# architects, certificate engineers and the grouped fidelity reviews. Idempotent per key (skips existing sessions).
set -uo pipefail
A=$HOME/aklt; export PATH=$HOME/.elan/bin:$PATH
launch() { # KEY EFFORT SEARCH(0/1) CWD EXTRA_ADD_DIRS...
  local K=$1 E=$2 S=$3 C=$4; shift 4
  [ -e $A/flags/$K.done ] && return 0; tmux has-session -t $K 2>/dev/null && return 0
  until $A/bin/aklt-budget-check 1 >/dev/null 2>&1; do echo "budget hold for $K"; sleep 120; done
  local ADD=""; for d in "$@"; do ADD="$ADD --add-dir $d"; done
  local X=""; [ "$S" = 1 ] && X="--search"
  mkdir -p $A/reports/$K
  tmux new-session -d -s $K "cd $C; export PATH=\$HOME/.elan/bin:\$PATH; python3 $A/bin/sol-retry.py $E $S -- run -C $C --write $ADD $X -e $E --name $K -f $A/briefs/$K.md > $A/logs/$K.out 2>&1; touch $A/flags/$K.done"
  echo "launched $K"; sleep 2
}
for K in BP_Q BP_GAP BP_WIN BP_MOM BP_REC BP_H3M BP_H1M CERT_H2 CERT_H3 CERT_H1; do
  [ -d $A/wt/$K ] || $A/bin/aklt-mkwt $K main >/dev/null
  EXTRA="$A/reports/$K"; case $K in CERT_H3|CERT_H1) mkdir -p $A/scratch/$K; EXTRA="$EXTRA $A/scratch/$K";; esac
  launch $K max 0 $A/wt/$K $EXTRA
done
python3 $A/bin/fid_groups.py $A/repo Computation.lean Trails.lean Automaton.lean Stationary.lean Computational.lean | tee $A/logs/fid_groups.out
for K in $(tail -1 $A/logs/fid_groups.out); do launch $K xhigh 0 $A/reports/$K; done
echo WAVE2-LAUNCHED
