#!/usr/bin/env bash
set -euo pipefail
cd /home/ubuntu/aklt/wt/CLOSE_H3
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake/build/lib/lean/CertData/Close
/usr/bin/time -v -o /home/ubuntu/aklt/reports/CLOSE_H3/final/build.time \
  lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false \
  -o .lake/build/lib/lean/CertData/Close/All.olean CertData/Close/All.lean \
  > /home/ubuntu/aklt/reports/CLOSE_H3/final/build.log 2>&1
