"""Inspect declarations using existing read-only AKLT and Mathlib build products."""
import os
from pathlib import Path
import subprocess

repo = Path('/home/ubuntu/aklt/repo')
scratch = Path(__file__).resolve().parent
paths = [repo / '.lake/build/lib/lean']
paths.extend(
    p / '.lake/build/lib/lean'
    for p in sorted((repo / '.lake/packages').iterdir())
    if (p / '.lake/build/lib/lean').is_dir()
)
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, paths))
result = subprocess.run(
    ['/home/ubuntu/.elan/bin/lean', 'Inspect.lean'],
    cwd=scratch, env=env, text=True, capture_output=True,
)
(scratch / 'Inspect.log').write_text(result.stdout + result.stderr)
print('Lean exit code:', result.returncode)
print('Declaration inspections:', result.stdout.count('\ndef ') + int(result.stdout.startswith('def ')))
if result.returncode:
    print(result.stdout)
    print(result.stderr)
raise SystemExit(result.returncode)
