#!/usr/bin/env python3
"""Audit every regenerated H3 theorem using its module-system build receipt.

The original open-leaf inventory is retained in the legacy campaign reports;
this release uses the proved leaf modules and the unconditional closing module.
"""
import sys
from regen import main

if __name__ == '__main__':
    sys.argv.insert(1, 'verify')
    raise SystemExit(main())
