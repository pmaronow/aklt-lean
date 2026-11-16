#!/usr/bin/env python3
"""sol-retry.py EFFORT SEARCH(0|1) -- <codex_sol.py run args...>: run a Sol agent; if its output reports
"at capacity" (or another transient model error) resume the same session with the SAME effort (and --search) up to
8 times with growing sleeps. Prints all output (the queue redirects it to ~/th/logs/q-NAME.out)."""
import subprocess, sys, re, time, os
eff, search = sys.argv[1], sys.argv[2] == "1"
args = sys.argv[sys.argv.index("--") + 1:]
H = os.path.expanduser("~")
def run(a):
    r = subprocess.run(a, capture_output=True, text=True)
    out = r.stdout + r.stderr
    print(out, flush=True)
    return r.returncode, out
rc, out = run(["python3", f"{H}/bin/codex_sol.py"] + args)
trans = re.compile(r"at capacity|Please try a different model|stream disconnected|Reconnecting|503|overloaded", re.I)
for k in range(8):
    m = re.search(r"session=([0-9a-f-]{20,})", out)
    if not trans.search(out) or not m:
        break
    time.sleep(60 * (k + 1))
    os.makedirs(f"{H}/aklt/scratch/retry", exist_ok=True); pf = f"{H}/aklt/scratch/retry/sol-{m.group(1)}-{k+1}.md"
    open(pf, "w").write("The previous turn was interrupted by a transient model error. Continue the task from where you stopped; the deliverable and all rules are unchanged.")
    a = ["python3", f"{H}/bin/codex_sol.py", "resume", m.group(1), "-f", pf, "-e", eff]
    if search: a.append("--search")
    print(f"=== sol-retry: resume {m.group(1)} attempt {k+1} ===", flush=True)
    rc, out2 = run(a)
    out = out2
sys.exit(rc)
