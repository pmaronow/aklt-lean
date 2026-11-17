#!/usr/bin/env bash
# Run on a host shell that can contact the user systemd manager.
# This session cannot do so; this script never falls back to an unlimited run.
set -euo pipefail
if [[ $# -eq 0 ]]; then
  printf '%s\n' 'Usage: default_scope.sh COMMAND [ARG ...]' >&2
  exit 2
fi
exec systemd-run --user --scope --collect --expand-environment=no --unit="pal-fit-${RANDOM}" \
  -p CPUQuota=1600% -p MemoryMax=32G -p MemorySwapMax=0 \
  /bin/bash -euc '
    scope_path=$(awk -F: '\''$1 == "0" {print $3}'\'' /proc/self/cgroup)
    control="/sys/fs/cgroup${scope_path}"
    read -r quota period < "$control/cpu.max"
    test "$quota" != max
    test "$quota" -eq "$((16 * period))"
    test "$(cat "$control/memory.max")" = 34359738368
    test "$(cat "$control/memory.swap.max")" = 0
    printf "Enforced cgroup: %s\n" "$control" >&2
    cat "$control/cpu.max" "$control/memory.max" "$control/memory.swap.max" >&2
    exec taskset -c 0-15 "$@"
  ' bash "$@"
