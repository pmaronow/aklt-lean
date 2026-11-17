#!/usr/bin/env bash
set -euo pipefail
cd /home/ubuntu/aklt/wt/CLOSE_H3
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake/build/lib/lean/CertData/H3/Close
for close_module in Leaves Main; do
  /usr/bin/time -v \
    -o "/home/ubuntu/aklt/reports/CLOSE_H3/build-${close_module}.time" \
    lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DElab.async=false \
    -o ".lake/build/lib/lean/CertData/H3/Close/${close_module}.olean" \
    "CertData/H3/Close/${close_module}.lean" \
    > "/home/ubuntu/aklt/reports/CLOSE_H3/build-${close_module}.log" 2>&1
done
