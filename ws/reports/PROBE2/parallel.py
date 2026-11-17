import concurrent.futures
import json
from pathlib import Path
import subprocess
import time

report = Path('/home/ubuntu/aklt/reports/PROBE2')
root = Path('/home/ubuntu/aklt/wt/PROBE2/AKLT/Probe2')
required = {'PrefixLeaves14Geometry48', 'PrefixLeaves14Early', 'PrefixLeaves14',
            'BellmanGuard1Fixed', 'BellmanGuard16Fixed'}
while True:
    rows = [json.loads(s) for s in (report/'measurements.jsonl').read_text().splitlines()]
    if required <= {r['id'] for r in rows}:
        break
    time.sleep(1)
names = [f'Parallel{i}' for i in range(1,7)]
for name in names:
    (root/(name+'.lean')).write_text((root/'FastBellmanGuard1024.lean').read_text())

def run_one(name, tag):
    return subprocess.run(['python3', str(report/'run.py'), name, '--tag', tag,
                           '--gib', '16', '--seconds', '120', '--profile'],
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

groups = []
for tag in ['Sequential', 'Concurrent']:
    start = time.monotonic()
    if tag == 'Sequential':
        results = [run_one(n, tag) for n in names]
    else:
        with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
            results = list(pool.map(lambda n: run_one(n, tag), names))
    elapsed = time.monotonic() - start
    for result in results:
        print(result.stdout, flush=True)
    row = dict(tag=tag, wall_s=elapsed, exits=[r.returncode for r in results])
    groups.append(row)
    (report/'parallel_groups.json').write_text(json.dumps(groups, indent=2)+'\n')
    print(row, flush=True)
