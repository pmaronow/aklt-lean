# Source this file, then replay a command from report.md, e.g.:
# K FastPacked128 24 600 p
K() (
  local probe2_name="$1"
  local probe2_cap="$2"
  local probe2_seconds="$3"
  local probe2_flags="${4-}"
  local probe2_root=/home/ubuntu/aklt/wt/PROBE2
  local probe2_report=/home/ubuntu/aklt/reports/PROBE2
  local -a probe2_command=(lean -DElab.async=false)
  if [[ "$probe2_flags" == *c* ]]; then
    probe2_command=("$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/leanchecker"
                    --fresh "AKLT.Probe2.$probe2_name")
  else
    if [[ "$probe2_flags" == *p* ]]; then probe2_command+=(--profile); fi
    if [[ "$probe2_flags" != *n* ]]; then
      probe2_command+=(-o "$probe2_root/AKLT/Probe2/$probe2_name.olean")
    fi
    probe2_command+=("$probe2_root/AKLT/Probe2/$probe2_name.lean")
  fi
  export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
  export LEAN_PATH="$probe2_root${LEAN_PATH:+:$LEAN_PATH}"
  cd "$probe2_root" || exit
  PROBE2_IGNORE_INNER_LIMITS=1 /usr/bin/time -v lake env \
    timeout --signal=TERM --kill-after=5s "${probe2_seconds}s" \
    python3 "$probe2_report/limit_exec.py" "$probe2_cap" "${probe2_command[@]}"
)
