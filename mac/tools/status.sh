#!/bin/bash
# Mac-side status of the AKLT campaign.
echo "== $(date -u +%FT%TZ)"
echo "-- Mac agents (codex exec, by cwd):"
for p in $(pgrep -f 'codex exec' 2>/dev/null); do lsof -a -p $p -d cwd -Fn 2>/dev/null | grep ^n | cut -c2-; done | grep aklt-lean | sort | uniq -c
echo "-- Mac reports present:"; for d in ~/aklt-lean/reports/*/ ~/aklt-lean/orch-checks/CK-*/; do f=$(ls $d/report.md $d/donors.md 2>/dev/null | head -1); [ -n "$f" ] && echo "  $(basename $d): $(head -1 $f | cut -c1-90)"; done
python3 - <<'PY'
import json,glob,os
fs=sorted(glob.glob(os.path.expanduser('~/.codex/sessions/2026/11/*/rollout-*.jsonl')),key=os.path.getmtime)[-20:]
best=None
for f in fs:
    for line in open(f):
        if '"rate_limits"' in line:
            try:
                d=json.loads(line); p=d['payload']; rl=p.get('rate_limits') or p.get('info',{}).get('rate_limits')
                if rl and (best is None or d['timestamp']>best[0]): best=(d['timestamp'],rl)
            except Exception: pass
if best: print(f"-- Mac gmail quota: used {best[1]['primary']['used_percent']}% at {best[0]}, credits {best[1]['credits']['balance']}")
PY
echo "-- Workstation:"
ssh -o ConnectTimeout=15 aklt-ws 'tmux ls 2>/dev/null | cut -d: -f1 | tr "\n" " "; echo; echo "flags: $(ls ~/aklt/flags | tr "\n" " ")"; echo "agents: $(ps aux | grep -c "[c]odex exec")  load: $(cut -d" " -f1-3 /proc/loadavg)  mem used: $(free -g | awk "/Mem/{print \$3}") GB  disk free: $(df -h / | awk "NR==2{print \$4}")"; for f in ~/aklt/reports/*/report.md; do echo "  $(basename $(dirname $f)): $(head -1 $f | cut -c1-90)"; done 2>/dev/null; python3 ~/aklt/bin/yale_quota.py'
