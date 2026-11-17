#!/usr/bin/env python3
"""fid_delta.py SNAP PREFIX BASE_COMMIT: blind review groups (<=5 decls) for every declaration of AKLT/Defs and
AKLT/Blueprint/Top files that were added or changed since BASE_COMMIT in ~/aklt/repo (main). Paper = manuscript-v2."""
import os, re, sys, json, shutil, glob, subprocess
A = os.path.expanduser('~/aklt'); snap, prefix, base = sys.argv[1:4]; R = f'{A}/review/{snap}'; src = f'{A}/repo'
if os.path.exists(R): subprocess.run(['chmod', '-R', 'u+w', R]); shutil.rmtree(R)
os.makedirs(f'{R}/lean'); os.makedirs(f'{R}/paper')
for f in glob.glob(f'{src}/AKLT/Defs/*.lean') + glob.glob(f'{src}/AKLT/Blueprint/Top/*.lean') + glob.glob(f'{src}/AKLT/Challenge/*.lean'):
    d = f'{R}/lean/' + os.path.relpath(f, src); os.makedirs(os.path.dirname(d), exist_ok=True); shutil.copy(f, d)
for t in glob.glob(f'{A}/manuscript-v2/*.tex'):
    txt = '\n'.join(l for l in open(t, errors='replace').read().split('\n') if not l.lstrip().startswith('%'))
    open(f'{R}/paper/' + os.path.basename(t), 'w').write(txt)
changed = subprocess.run(['git', '-C', src, 'diff', '--name-only', base, 'main', '--', 'AKLT/Defs', 'AKLT/Blueprint/Top'], capture_output=True, text=True).stdout.split()
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(def|abbrev|structure|inductive|instance|theorem|lemma|class)\s+([^\s:({\[]+)')
common = open(f'{A}/briefs/FID_S-COMMON.md').read().replace('/review/FID_S/', f'/review/{snap}/')
keys = []; groups = []
for rel in sorted(changed):
    if os.path.basename(rel) in ('All.lean', 'Audit.lean', 'Assembly.lean'): continue
    old = subprocess.run(['git', '-C', src, 'show', f'{base}:{rel}'], capture_output=True, text=True).stdout
    names = []
    cur = open(f'{src}/{rel}', errors='replace').read()
    blocks = re.split(r'\n(?=(?:/--|@\[|noncomputable |private |protected |def |abbrev |structure |inductive |instance |theorem |lemma |class ))', cur)
    for b in blocks:
        m = None
        for line in b.split('\n'):
            m = decl.match(line)
            if m: break
        if m and b.strip() not in old: names.append(m.group(2))
    names = list(dict.fromkeys(names))
    for i in range(0, len(names), 5):
        key = f'{prefix}{len(keys)+1:03d}'; os.makedirs(f'{A}/reports/{key}', exist_ok=True)
        open(f'{A}/briefs/{key}.md', 'w').write(f"# {key} — fidelity review of Lean statements (blind)\n\n**Your declarations:** in `{R}/lean/{rel}`: " + ', '.join(f'`{d}`' for d in names[i:i+5]) + f".\nYour working directory is `{A}/reports/{key}/`.\n" + common)
        keys.append(key); groups.append({'key': key, 'file': rel, 'decls': names[i:i+5]})
json.dump(groups, open(f'{A}/state/{snap}_groups.json', 'w'), indent=1); subprocess.run(['chmod', '-R', 'a-w', R])
print(' '.join(keys))
