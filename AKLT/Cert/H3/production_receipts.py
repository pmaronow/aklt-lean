#!/usr/bin/env python3
"""Verify module-system H3 sources, compiled artifacts, and axiom receipts."""
import sys
from regen import main

if __name__ == '__main__':
    sys.argv.insert(1, 'verify')
    raise SystemExit(main())
