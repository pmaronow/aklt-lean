"""Fresh, timed Lean invocations. Never builds dependencies."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import time

ROOT = Path('/home/ubuntu/aklt/wt/PROBE2')
REPORT = Path('/home/ubuntu/aklt/reports/PROBE2')
parser = argparse.ArgumentParser()
parser.add_argument('names', nargs='+')
parser.add_argument('--seconds', type=int, default=600)
parser.add_argument('--gib', type=int, default=24)
parser.add_argument('--tag', default='')
parser.add_argument('--import-only', action='store_true')
parser.add_argument('--profile', action='store_true')
parser.add_argument('--checker', choices=['leanchecker', 'leanchecker-paranoid'])
args = parser.parse_args()
env = dict(os.environ)
env['PATH'] = str(Path.home()/'.elan/bin') + ':' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
env['LEAN_PATH'] = str(ROOT) + (':' + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')

for name in args.names:
    ident = name + args.tag
    source = ROOT / 'AKLT/Probe2' / (name + '.lean')
    output = source.with_suffix('.olean')
    log = REPORT / 'logs' / (ident + '.log')
    timing = REPORT / 'logs' / (ident + '.time')
    lean = ['lean', '-DElab.async=false']
    if args.profile:
        lean += ['--profile']
    if not args.import_only:
        lean += ['-o', str(output)]
    lean += [str(source)]
    if args.checker:
        lean = [str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin'/args.checker),
                '--fresh', 'AKLT.Probe2.'+name]
    cmd = ['/usr/bin/time', '-v', '-o', str(timing), 'lake', 'env',
           'timeout', '--signal=TERM', '--kill-after=5s', str(args.seconds)+'s',
           'python3', str(REPORT/'limit_exec.py'), str(args.gib)] + lean
    start = time.monotonic()
    source_sha256 = hashlib.sha256(source.read_bytes()).hexdigest()
    print(datetime.datetime.now(datetime.timezone.utc).isoformat(), 'START', ident,
          f'{args.gib} GiB / {args.seconds}s', flush=True)
    with log.open('w') as f:
        result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    contents = log.read_text(errors='replace')
    stats = timing.read_text() if timing.exists() else ''
    def metric(pattern, convert=float):
        m = re.search(pattern, stats)
        return convert(m.group(1)) if m else None
    axioms = re.findall(r"^.*(?:depends on axioms|does not depend on any axioms).*$", contents, re.M)
    outcome = 'PASS' if result.returncode == 0 else 'FAIL'
    if result.returncode == 124:
        outcome = 'TIMEOUT'
    elif 'out of memory' in contents.lower() or 'bad_alloc' in contents:
        outcome = 'MEMORY LIMIT'
    elif 'stack overflow' in contents.lower():
        outcome = 'STACK OVERFLOW'
    row = dict(id=ident, name=name, command=shlex.join(cmd),
               timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               wall_s=round(elapsed, 3), time_wall=metric(r'Elapsed \(wall clock\) time .*: ([\d:.]+)', str),
               rss_kib=metric(r'Maximum resident set size \(kbytes\): (\d+)', int),
               user_s=metric(r'User time \(seconds\): ([\d.]+)'),
               sys_s=metric(r'System time \(seconds\): ([\d.]+)'),
               exit=result.returncode, outcome=outcome, axioms=axioms,
               limit_gib=args.gib, timeout_s=args.seconds,
               source_bytes=source.stat().st_size,
               source_sha256=source_sha256,
               olean_bytes=output.stat().st_size if result.returncode == 0 and output.exists() else None)
    with (REPORT/'measurements.jsonl').open('a') as f:
        f.write(json.dumps(row)+'\n')
    print(ident, row['wall_s'], 's', row['rss_kib'], 'KiB',
          row['exit'], row['outcome'], '; '.join(axioms), flush=True)
    if result.returncode:
        print(contents[-2500:], flush=True)
