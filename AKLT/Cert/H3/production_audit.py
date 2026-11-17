#!/usr/bin/env python3
"""Audit every regenerated H3 theorem using its module-system build receipt.

The original obligation inventory is retained in the historical verification records;
this release uses the proved library modules and the unconditional closing module.
"""
import sys
from regen import main

if __name__ == '__main__':
    sys.argv.insert(1, 'verify')
    raise SystemExit(main())
