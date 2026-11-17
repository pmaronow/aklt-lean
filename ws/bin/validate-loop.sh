#!/bin/bash
# every 30 min: full validation of main if it moved (flock inside merge-validate serializes with merges)
A=$HOME/aklt
while true; do
  sleep 1800
  [ "$(git -C $A/repo rev-parse main)" = "$(git -C $A/repo rev-parse validated)" ] && continue
  if $A/bin/merge-validate.sh MAIN - - > $A/logs/MV_MAIN-$(date -u +%H%M).log 2>&1; then echo "$(date -u +%FT%TZ) validated $(git -C $A/repo rev-parse --short validated)" >> $A/logs/validate-loop.log; else echo "$(date -u +%FT%TZ) VALIDATION FAILED" >> $A/logs/validate-loop.log; touch $A/flags/VALIDATION.failed; fi
done
