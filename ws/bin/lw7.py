#!/usr/bin/env python3
"""lw.py — lightweight leaf wave for the AKLT campaign.

  lw.py plan PART...        build state/lw/leaves.json from reports/BP_<PART>/leaves.json (non-superseded leaves)
  lw.py launch-loop [CAP]   keep up to CAP writer agents running (Luna xhigh first, Sol max on failure)
  lw.py integrate-loop      check finished attempts, merge passing ones into main in batches, escalate failures
  lw.py status              one-line counts

A leaf is proved when, in its worktree: only files under AKLT/W/<KEY>/ changed; the token/effect scan is clean;
`example : <node> := AKLT.W.<KEY>.main` compiles; and `#print axioms` shows only the three allowed axioms.
Soundness of the campaign does not rest on this script: the final assembly, clean build, con-ron/NanoDa and the
Comparator are run on the merged tree at milestones.
"""
import fcntl, json, os, re, subprocess, sys, time, glob

H = os.path.expanduser('~'); A = f'{H}/aklt'; S = f'{A}/state/lw'; REPO = f'{A}/repo'; SEED = f'{A}/seed'
ENV = dict(os.environ, PATH=f'{H}/.elan/bin:' + os.environ['PATH']); ENV.pop('LAKE_ARTIFACT_CACHE', None)
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBID = re.compile(r'\b(sorry|admit|native_decide|implemented_by|unsafe|opaque|extern)\b|^\s*axiom\s|debug\.skipKernelTC|maxHeartbeats\s+0\b|#eval|\bIO\b|run_cmd|run_elab|initialize\b|macro_rules', re.M)
BASELINE_CREDITS = '85075.0939670000'

def sh(cmd, cwd=None, timeout=None, check=False):
    return subprocess.run(cmd, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout, check=check)

class Lock:
    def __init__(self, name): self.p = f'{A}/state/merge.lock' if name == 'merge' else f'{S}/{name}.lock'
    def __enter__(self): self.f = open(self.p, 'w'); fcntl.flock(self.f, fcntl.LOCK_EX); return self
    def __exit__(self, *a): fcntl.flock(self.f, fcntl.LOCK_UN); self.f.close()

def load():
    return json.load(open(f'{S}/leaves.json'))

def save(d):
    tmp = f'{S}/leaves.json.tmp'; json.dump(d, open(tmp, 'w'), indent=1); os.replace(tmp, f'{S}/leaves.json')

def log(msg):
    open(f'{A}/logs/lw.log', 'a').write(time.strftime('%Y-%m-%dT%H:%M:%SZ ', time.gmtime()) + msg + '\n')

def strip_comments(t):
    t = re.sub(r'/-.*?-/', ' ', t, flags=re.S); return re.sub(r'--.*', ' ', t)

def plan(parts):
    os.makedirs(S, exist_ok=True); d = load() if os.path.exists(f'{S}/leaves.json') else {}
    known = {v['node'] for v in d.values()}
    for part in parts:
        L = json.load(open(f'{A}/reports/BP_{part}/leaves.json')); L = L if isinstance(L, list) else L.get('leaves', [])
        for i, x in enumerate(L, 1):
            if 'superseded' in json.dumps([x.get('status'), x.get('adaptation_status')]).lower(): continue
            if x['lean_name'] in known: continue
            key = f'{part}{i:03d}'
            d[key] = {'node': x['lean_name'], 'module': x['module'], 'part': part, 'stage': 'luna', 'state': 'pending', **({'base': os.environ['LW_BASE'], 'seed': os.environ['LW_SEED']} if os.environ.get('LW_BASE') else {}),
                      'label': x.get('paper_label', '?'), 'loc': str(x.get('paper_locator', x.get('paper_lines', ''))),
                      'route': x.get('suggested_proof_route', ''), 'trap': x.get('trap_note', ''), 'difficulty': x.get('difficulty', '?')}
    save(d); print(len(d), 'leaves planned')

def running():
    out = sh(['tmux', 'ls']).stdout
    return [l.split(':')[0] for l in out.splitlines() if l.startswith('LW_')]

def budget_ok(n_running):
    r = sh([f'{A}/bin/aklt-budget-check', '0'])
    try: j = json.loads(r.stdout)
    except Exception: return False
    if str(j.get('credits')) != BASELINE_CREDITS: return False
    if j.get('credit_only'): return False
    if j.get('age_seconds', 9999) > 900: return n_running == 0
    return j.get('remaining', 0) - 0.3 * (n_running + 1) - 1 > 0

def brief(key, x, prior=None):
    b = (f"# {key} — prove one blueprint leaf\n\n**Statement:** `{x['node']}` (a closed `def … : Prop` in module `{x['module']}`).\n"
         f"**Deliver:** file `AKLT/W/{key}/Main.lean` (plus helper files in the same directory if you like) containing\n"
         f"`theorem AKLT.W.{key}.main : {x['node']} := …` — exactly this name and type.\n"
         f"**Paper:** label {x['label']} {x['loc']}. **Estimated difficulty:** {x['difficulty']}.\n"
         f"**Suggested route:** {x['route']}\n**Trap notes:** {x['trap']}\n"
         f"Your worktree is `{A}/wt/LW_{key}` (already built: only your new files need compiling; build with "
         f"`lake build AKLT.W.{key}.Main`). Write your report to `{A}/reports/LW/{key}/report.md`.\n")
    if prior: b += f"\n**Earlier attempt.** {prior}\n"
    return b + open(f'{A}/briefs/LEAF-COMMON.md').read()

def launch(key, x):
    wt = f'{A}/wt/LW_{key}'; stage = x['stage']
    if not os.path.isdir(wt):
        with Lock('git'):
            r = sh(['git', 'worktree', 'add', '-q', '-b', f'lw/{key}', wt, x.get('base', 'validated')], cwd=REPO)
            if r.returncode: log(f'{key} worktree failed {r.stderr[-200:]}'); return False
        os.makedirs(f'{wt}/.lake', exist_ok=True)
        if not os.path.exists(f'{wt}/.lake/packages'): os.symlink(f'{A}/packages-store', f'{wt}/.lake/packages')
    if not os.path.isdir(f'{wt}/.lake/build'):
        sh(['cp', '-a', f"{x.get('seed', SEED)}/.lake/build", f'{wt}/.lake/build'])
    os.makedirs(f'{A}/reports/LW/{key}', exist_ok=True)
    prior = None
    if stage == 'sol':
        with Lock('git'):
            sh(['git', 'merge', '-q', '--no-edit', 'main'], cwd=wt)
        d0 = load()
        open(f'{S}/proved-index.tsv', 'w').write(''.join(f"{v['node']}\tAKLT.W.{k}.main\tAKLT.W.{k}.Main\n" for k, v in sorted(d0.items()) if v['state'] == 'merged'))
        prior = (f"Another model already attempted this leaf; its files are in `AKLT/W/{key}/` and its report is "
                 f"`{A}/reports/LW/{key}/report.md` (now copied to report.luna.md). The automatic check said: "
                 f"{x.get('fail', 'no passing proof')}. Reuse what is useful; you are free to start over. "
                 f"NEW: your worktree now contains every leaf proved so far; you MAY import and use them as lemmas "
                 f"(index: `{S}/proved-index.tsv`, columns statement / theorem / module; e.g. `import AKLT.W.Q001.Main` "
                 f"then `AKLT.W.Q001.main : <its statement>`). If your statement reduces to other blueprint leaves that are "
                 f"not yet in the index, prove the reduction and report STATUS: PARTIAL naming exactly those leaves.")
        rp = f'{A}/reports/LW/{key}/report.md'
        if os.path.exists(rp): os.replace(rp, f'{A}/reports/LW/{key}/report.luna.md' if not os.path.exists(f'{A}/reports/LW/{key}/report.luna.md') else f'{A}/reports/LW/{key}/report.sol{int(time.time())}.md')
    bp = f'{A}/briefs/LW/{key}.{stage}.md'; os.makedirs(os.path.dirname(bp), exist_ok=True); open(bp, 'w').write(brief(key, x, prior))
    drv, eff = ('luna-retry.py', 'xhigh') if stage == 'luna' else ('sol-retry.py', 'max')
    flag = f'{S}/done/{key}.{stage}'; os.makedirs(f'{S}/done', exist_ok=True)
    if os.path.exists(flag): os.remove(flag)
    cmd = (f"cd {wt}; export PATH=$HOME/.elan/bin:$PATH; python3 {A}/bin/{drv} {eff} 0 -- run -C {wt} --write "
           f"--add-dir {A}/reports/LW/{key} -e {eff} --name LW_{key} -f {bp} > {A}/logs/LW/{key}.{stage}.out 2>&1; touch {flag}")
    os.makedirs(f'{A}/logs/LW', exist_ok=True)
    r = sh(['tmux', 'new-session', '-d', '-s', f'LW_{key}', cmd])
    if r.returncode: log(f'{key} tmux failed {r.stderr[-200:]}'); return False
    log(f'{key} launched {stage}'); return True

def launch_loop(cap):
    while True:
        if os.path.exists(f'{S}/PAUSE'): time.sleep(30); continue
        run = running(); n = len(run)
        with Lock('state'):
            d = load()
            todo = [k for k, x in sorted(d.items(), key=lambda kv: (kv[1]['stage'] != 'sol', kv[0])) if x['state'] == 'pending' and all(d[a]['state'] == 'merged' for a in x.get('after', []))]
        for key in todo:
            if n >= cap: break
            if not budget_ok(n): log('budget hold'); time.sleep(120); break
            with Lock('state'):
                d = load(); x = d[key]
                if x['state'] != 'pending': continue
                if launch(key, x): x['state'] = 'running'; x['t_launch'] = time.time(); save(d); n += 1
            time.sleep(1.5)
        time.sleep(20)

def check(key, x):
    wt = f'{A}/wt/LW_{key}'; own = f'AKLT/W/{key}/'
    st = sh(['git', 'status', '--porcelain', '--untracked-files=all'], cwd=wt).stdout.splitlines()
    paths = [l[3:].strip().strip('"') for l in st]
    if not paths: return False, 'no files written'
    bad = [p for p in paths if not p.startswith(own)]
    if bad: return False, f'files outside {own}: {bad[:3]}'
    if not os.path.exists(f'{wt}/{own}Main.lean'): return False, 'Main.lean missing'
    for p in paths:
        if p.endswith('.lean'):
            t = strip_comments(open(f'{wt}/{p}', errors='replace').read()); t = re.sub(r'"(?:[^"\\]|\\.)*"', '""', t)
            m = FORBID.search(t)
            if m: return False, f'forbidden token {m.group(0).strip()!r} in {p}'
    try:
        r = sh(['lake', 'build', f'AKLT.W.{key}.Main'], cwd=wt, timeout=2400)
    except subprocess.TimeoutExpired: return False, 'build timeout (2400 s)'
    if r.returncode: return False, 'build failed: ' + (r.stdout + r.stderr)[-400:].replace('\n', ' ')
    os.makedirs(f'{wt}/.lwcheck', exist_ok=True); cf = f'{wt}/.lwcheck/Check.lean'
    open(cf, 'w').write(f"import AKLT.W.{key}.Main\nimport {x['module']}\nexample : {x['node']} := AKLT.W.{key}.main\n#print axioms AKLT.W.{key}.main\n")
    try: r = sh(['lake', 'env', 'lean', cf], cwd=wt, timeout=900)
    except subprocess.TimeoutExpired: return False, 'exact check timeout'
    out = r.stdout + r.stderr
    sh(['rm', '-rf', f'{wt}/.lwcheck'])
    if r.returncode: return False, 'exact-type check failed: ' + out[-400:].replace('\n', ' ')
    m = re.search(r"depends on axioms: \[([^\]]*)\]", out)
    ax = {a.strip() for a in m.group(1).split(',')} if m else (set() if 'does not depend on any axioms' in out else {'?'})
    if not ax <= ALLOWED: return False, f'axioms {sorted(ax)}'
    return True, 'ok'

def integrate_loop():
    while True:
        with Lock('state'): d = load()
        fin = [(k, x) for k, x in d.items() if x['state'] == 'running' and os.path.exists(f"{S}/done/{k}.{x['stage']}")]
        passed = []
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(8) as ex: results = list(ex.map(lambda kx: (kx[0], check(*kx)), fin[:48]))
        for key, (ok, why) in results:
            with Lock('state'):
                d = load(); x = d[key]
                if ok:
                    wt = f'{A}/wt/LW_{key}'
                    sh(['git', 'add', '-A', f'AKLT/W/{key}'], cwd=wt)
                    sh(['git', '-c', 'user.name=aklt-orchestrator', '-c', 'user.email=noreply@anthropic.com', 'commit', '-qm',
                        f"{key}: {x['node']} proved ({x['stage']})\n\nCo-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01DtFRS1A1TmhbdfqkiHSKuL"], cwd=wt)
                    x['state'] = 'proved'; x['by'] = x['stage']; passed.append(key); log(f'{key} PROVED by {x["stage"]}')
                else:
                    x['fail'] = why; log(f'{key} FAILED {x["stage"]}: {why[:200]}')
                    if x['stage'] == 'luna': x['stage'] = 'sol'; x['state'] = 'pending'
                    else: x['state'] = 'exhausted'; open(f'{S}/opus-queue.txt', 'a').write(f"{key}\t{x['node']}\t{why[:200]}\n")
                save(d)
        with Lock('state'): passed = [k for k, x in load().items() if x['state'] == 'proved']
        if passed:
            with Lock('merge'):
                merged = []
                for key in passed:
                    r = sh(['git', 'merge', '-q', '--no-edit', f'lw/{key}'], cwd=REPO)
                    if r.returncode: sh(['git', 'merge', '--abort'], cwd=REPO); log(f'{key} MERGE CONFLICT'); continue
                    merged.append(key)
            with Lock('state'):
                d = load()
                for key in merged: d[key]['state'] = 'merged'
                save(d)
            for key in merged: sh(['rm', '-rf', f'{A}/wt/LW_{key}/.lake/build'])
            log(f'merged {len(merged)}: {" ".join(merged)}')
        time.sleep(30)

def status():
    d = load(); c = {}
    for x in d.values(): c[(x['state'], x['stage'])] = c.get((x['state'], x['stage']), 0) + 1
    print(time.strftime('%H:%M', time.gmtime()), {f'{a}/{b}': n for (a, b), n in sorted(c.items())}, 'running sessions', len(running()))

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'plan': plan(sys.argv[2:])
    elif cmd == 'launch-loop': launch_loop(int(sys.argv[2]) if len(sys.argv) > 2 else 80)
    elif cmd == 'integrate-loop': integrate_loop()
    elif cmd == 'status': status()
