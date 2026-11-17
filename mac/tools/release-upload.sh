#!/bin/bash
# Route release assets workstation -> Mac -> GitHub, one file at a time (the Mac has little free disk).
# usage: release-upload.sh TAG file...
set -u
TAG=$1; shift
S=~/aklt-lean/release-stage
for f in "$@"; do
  if gh release view "$TAG" -R pmaronow/aklt-lean --json assets -q '.assets[].name' | grep -qx "$f"; then echo "$(date -u +%T) have $f"; continue; fi
  scp -q aklt-ws:aklt/release-final/"$f" "$S/$f" || { echo "scp failed $f"; exit 1; }
  gh release upload "$TAG" "$S/$f" -R pmaronow/aklt-lean || { echo "upload failed $f"; rm -f "$S/$f"; exit 1; }
  rm -f "$S/$f"; echo "$(date -u +%T) uploaded $f"
done
echo ALL-DONE
