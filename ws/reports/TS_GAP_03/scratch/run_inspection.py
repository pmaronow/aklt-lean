"""Inspect existing declarations without writing repository build artifacts."""
from pathlib import Path
import os
import subprocess

root = Path(__file__).resolve().parent.parent
repo = Path('/home/ubuntu/aklt/repo')
lake = root / 'scratch/.lake'
lake.mkdir(exist_ok=True)
packages = lake / 'packages'
if not packages.exists():
    packages.symlink_to(repo / '.lake/packages', target_is_directory=True)
search = [repo / '.lake/build/lib/lean'] + sorted((repo / '.lake/packages').glob('*/.lake/build/lib/lean'))
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, search))
command = ['/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean',
           str(root / 'scratch/Inspect.lean')]
with (root / 'scratch/inspect.log').open('w') as log:
    result = subprocess.run(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
print(f'Lean inspection exit code: {result.returncode}')
raise SystemExit(result.returncode)
