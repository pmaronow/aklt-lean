"""Elaborate one inspection module, using only existing read-only build artifacts."""
from pathlib import Path
import os
import subprocess

workspace = Path(__file__).resolve().parent.parent
repo = Path('/home/ubuntu/aklt/repo')
lake = workspace / '.lake'
lake.mkdir(exist_ok=True)
packages = lake / 'packages'
if not packages.exists():
    packages.symlink_to(repo / '.lake/packages', target_is_directory=True)
paths = [repo / '.lake/build/lib/lean']
paths.extend(p / '.lake/build/lib/lean' for p in packages.iterdir()
             if (p / '.lake/build/lib/lean').is_dir())
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, paths))
lean = '/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean'
result = subprocess.run([lean, str(workspace / 'scratch/Inspect.lean')],
                        cwd=workspace, env=env, text=True, capture_output=True)
log = workspace / 'scratch/lean-inspection.log'
log.write_text(result.stdout + result.stderr)
print(f'Lean inspection exit status: {result.returncode}; output: {log}')
print(result.stdout[-2400:])
if result.stderr:
    print(result.stderr)
raise SystemExit(result.returncode)
