"""Inspect existing compiled definitions without building or modifying the repository."""

import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = Path('/home/ubuntu/aklt/repo')
paths = [REPO / '.lake/build/lib/lean']
paths.extend(sorted((HERE / '.lake/packages').glob('*/.lake/build/lib/lean')))
env = dict(os.environ)
env['LEAN_PATH'] = ':'.join(str(path) for path in paths)
result = subprocess.run(
    ['/home/ubuntu/.elan/bin/lean', str(HERE / 'Inspect.lean')],
    cwd=HERE,
    env=env,
    text=True,
    stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT,
    check=False,
)
(HERE / 'lean_inspection.txt').write_text(result.stdout)
print(f'Lean inspection exited {result.returncode}; output: {HERE / "lean_inspection.txt"}')
if result.returncode:
    print(result.stdout)
raise SystemExit(result.returncode)
