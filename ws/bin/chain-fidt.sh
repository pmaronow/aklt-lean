#!/bin/bash
A=$HOME/aklt
until git -C $A/repo merge-base --is-ancestor 6d0bd35 main 2>/dev/null; do sleep 15; done
KEYS=$(python3 $A/bin/fid_delta.py FID_T FID_T 7a33935 | tail -1); echo "$KEYS" > $A/logs/fid_t_keys.txt
$A/bin/launch-keys.sh xhigh $KEYS; touch $A/flags/FID_T_LAUNCHED.done
