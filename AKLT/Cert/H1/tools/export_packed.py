#!/usr/bin/env python3
"""Generate local tensor data and packed-constructor row checks for a pattern."""
import argparse,json
from pathlib import Path
from math import prod
from export import records,write,lean_list,validate,disk_guard,NS
from packed import sites


def tree(xs):
    if not any(z != (0,0) for z in xs): return '.empty'
    if len(xs) == 1:
        a,b=xs[0];return f'(.leaf ⟨{a}, {b}⟩)'
    mid=len(xs)//2
    return f'(.node {mid} {tree(xs[:mid])} {tree(xs[mid:])})'



def main():
    from production_export import main as production_main
    production_main()


if __name__ == "__main__":
    main()
