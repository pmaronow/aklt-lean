#!/usr/bin/env bash
set -euo pipefail
task_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
g++ -std=c++20 -O3 -Wall -Wextra "$task_dir/replay.cpp" -lz -o "$task_dir/replay"
cd "$task_dir"
exec "$task_dir/replay" "${1:-/home/ubuntu/aklt/reports/MATH_FIT/data}"
