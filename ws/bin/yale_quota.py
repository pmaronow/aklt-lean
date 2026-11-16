import json,glob,os
fs=sorted(glob.glob(os.path.expanduser("~/.codex-yale/sessions/2026/11/*/rollout-*.jsonl")),key=os.path.getmtime)[-20:]
best=None
for f in fs:
    for line in open(f):
        if '"rate_limits"' in line:
            try:
                d=json.loads(line); p=d["payload"]; rl=p.get("rate_limits") or p.get("info",{}).get("rate_limits")
                if rl and (best is None or d["timestamp"]>best[0]): best=(d["timestamp"],rl)
            except Exception: pass
if best: print("Yale quota: used %s%% at %s, credits %s" % (best[1]["primary"]["used_percent"], best[0], best[1]["credits"]["balance"]))
