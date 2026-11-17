import os
import json
from pathlib import Path
import resource
import sys

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
cap = int(sys.argv[1]) * 1024**3
resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
policy_path = Path('/home/ubuntu/aklt/reports/PROBE2/inner_limits.json')
policy = (json.loads(policy_path.read_text()) if policy_path.exists() and
          not os.environ.get('PROBE2_IGNORE_INNER_LIMITS') else {})
name = Path(sys.argv[-1]).stem
if name in policy:
    seconds = policy[name]
    print(f'INNER_WALL_SECONDS={seconds}', flush=True)
    os.execvp('timeout', ['timeout', '--signal=TERM', '--kill-after=5s',
                         str(seconds)+'s'] + sys.argv[2:])
os.execvp(sys.argv[2], sys.argv[2:])
