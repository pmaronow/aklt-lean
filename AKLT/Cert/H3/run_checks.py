#!/usr/bin/env python3
"""Run selected H3 module checks in fresh processes, reusing verified dependencies."""
import argparse
import sys
from regen import main

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    parser.add_argument('--timeout', type=int, default=3600)
    parser.add_argument('--memory-gib', type=int, default=64)
    args = parser.parse_args()
    sys.argv = [sys.argv[0], 'build', '--stage', 'selected-checks', '--jobs', '1',
                '--force', '--timeout', str(args.timeout), '--process-gib', str(args.memory_gib),
                '--module', *args.modules]
    raise SystemExit(main())
