#!/usr/bin/env python3
"""fid_groups.py SRC_WORKTREE: build the blind review snapshot ~/aklt/review/FID_S and one brief per group of
<= 5 declarations of AKLT/Defs/*.lean and AKLT/Blueprint/Top/*.lean. Prints group keys; writes groups.json."""
import os, re, sys, json, shutil, glob, subprocess
A = os.path.expanduser('~/aklt'); src = sys.argv[1]; R = f'{A}/review/FID_S'
hold = set(sys.argv[2:])  # file basenames to hold back (e.g. Computation.lean)
if os.path.exists(R): subprocess.run(['chmod', '-R', 'u+w', R]); shutil.rmtree(R)
os.makedirs(f'{R}/lean'); os.makedirs(f'{R}/paper')
files = sorted(glob.glob(f'{src}/AKLT/Defs/*.lean') + glob.glob(f'{src}/AKLT/Blueprint/Top/*.lean') + glob.glob(f'{src}/AKLT/Challenge/*.lean'))
for f in files:
    d = f'{R}/lean/' + os.path.relpath(f, src); os.makedirs(os.path.dirname(d), exist_ok=True); shutil.copy(f, d)
for lane in ['REV_A1', 'REV_A2', 'REV_B', 'REV_C1a', 'REV_C1b', 'REV_C2', 'REV_C3']:
    for t in glob.glob(f'{A}/reports/{lane}/*.tex'):
        b = os.path.basename(t)
        if not (b.startswith('sec') or b.startswith('app-')): continue
        txt = open(t, errors='replace').read()
        txt = '\n'.join(l for l in txt.split('\n') if not l.lstrip().startswith('%'))
        txt = re.sub(r'(?<!\\)%.*', '', txt)
        open(f'{R}/paper/{b}', 'w').write(txt)
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(def|abbrev|structure|inductive|instance|theorem|lemma|class)\s+([^\s:({\[]+)')
groups = []; held = []
for f in files:
    rel = os.path.relpath(f, src)
    if rel.startswith('AKLT/Challenge') or os.path.basename(f) in ('All.lean', 'Audit.lean'): continue
    names = []
    for line in open(f, errors='replace'):
        m = decl.match(line)
        if m: names.append(m.group(2))
    for i in range(0, len(names), 5):
        g = {'file': rel, 'decls': names[i:i+5]}
        (held if os.path.basename(f) in hold else groups).append(g)
words = re.compile(r'amended|adjudicat|ADJ-|REF-|refereed|corrected (manuscript|version)|baseline|deviation|REV-PLAN|STRENGTHEN|MOSPROOF|OPPORTUNIT|COMPFEAS', re.I)
flag = [(p, i+1, l.strip()[:120]) for p in glob.glob(f'{R}/**/*', recursive=True) if os.path.isfile(p) for i, l in enumerate(open(p, errors='replace')) if words.search(l)]
common = open(f'{A}/briefs/FID_S-COMMON.md').read()
out = []
for n, g in enumerate(groups, 1):
    key = f'FID_S{n:03d}'; g['key'] = key
    os.makedirs(f'{A}/reports/{key}', exist_ok=True)
    brief = (f"# {key} — fidelity review of Lean statements (blind)\n\n**Your declarations:** in `{R}/lean/{g['file']}`: "
             + ', '.join(f'`{d}`' for d in g['decls']) + f".\nYour working directory is `{A}/reports/{key}/`.\n" + common)
    open(f'{A}/briefs/{key}.md', 'w').write(brief); out.append(key)
json.dump({'groups': groups, 'held': held, 'flagged': flag[:200]}, open(f'{A}/state/fid_s_groups.json', 'w'), indent=1)
subprocess.run(['chmod', '-R', 'a-w', R])
print(len(groups), 'groups;', len(held), 'held;', len(flag), 'flagged lines'); print(' '.join(out))
