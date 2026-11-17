#!/bin/bash
# every 20 min: full validation of main if it moved; merges are NOT blocked meanwhile.
A=$HOME/aklt
while true; do
  if [ "$(git -C $A/repo rev-parse main)" != "$(git -C $A/repo rev-parse validated)" ]; then
    L=$A/logs/VALMAIN-$(date -u +%H%M).log
    if $A/bin/validate-main.sh > $L 2>&1; then echo "$(date -u +%FT%TZ) $(tail -1 $L | cut -c1-200)" >> $A/logs/validate-loop.log; else echo "$(date -u +%FT%TZ) VALIDATION FAILED see $L" >> $A/logs/validate-loop.log; touch $A/flags/VALIDATION.failed; fi
  fi
  sleep 1200
done
