#!/bin/bash
# merge-after.sh PREVFLAG KEY ROOT MSG: wait for PREVFLAG, then merge-validate KEY; touch flags/MV_KEY.done.
A=$HOME/aklt; while [ ! -e $A/flags/$1 ]; do sleep 20; done
$A/bin/merge-validate.sh "$2" "$3" "$4" > $A/logs/MV_$2.log 2>&1; touch $A/flags/MV_$2.done
