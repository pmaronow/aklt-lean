#!/usr/bin/env python3
"""prune_stray.py ROOT KEY... : list .lean files under ROOT/AKLT/W/KEY not in the import closure of Main.lean.
With --delete, remove them (plain unlink; caller commits)."""
import os, re, sys
def closure(root, key):
    base = f'{root}/AKLT/W/{key}'; seen = set(); todo = [f'AKLT.W.{key}.Main']
    while todo:
        m = todo.pop()
        if m in seen: continue
        p = f'{root}/' + m.replace('.', '/') + '.lean'
        if not os.path.exists(p): continue
        seen.add(m)
        for imp in re.findall(r'^\s*(?:public\s+)?import\s+(?:all\s+)?([\w.«»\']+)', open(p, errors='replace').read(), re.M):
            if imp.startswith(f'AKLT.W.{key}.'): todo.append(imp)
    return {f'{root}/' + m.replace('.', '/') + '.lean' for m in seen}
def stray(root, key):
    keep = closure(root, key); out = []
    for dp, _, fs in os.walk(f'{root}/AKLT/W/{key}'):
        for f in fs:
            p = os.path.join(dp, f)
            if f.endswith('.lean') and p not in keep: out.append(p)
    return sorted(out)
if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if a != '--delete']; root = args[0]
    for key in args[1:]:
        for p in stray(root, key):
            print(os.path.relpath(p, root))
            if '--delete' in sys.argv: os.remove(p)
