"""Assemble the certificate file of a production run: one JSON line per pattern (7,962 lines).
Usage: collect.py model ps/qs pt/qt out.jsonl prod_part0.jsonl prod_part1.jsonl ...
closed-form certificates (decoupled patterns) are re-derived here in exact arithmetic; operator certificates are
taken from the production records (status CERTIFIED)."""
import sys, json
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load, TIPRAD
from closed_exact import certify_decoupled

model, cs, ct, out = sys.argv[1], Fr(sys.argv[2]), Fr(sys.argv[3]), sys.argv[4]
refined = (model == 'refined')
prod = {}
for fn in sys.argv[5:]:
    for l in open(fn):
        r = json.loads(l); prod[r['pid']] = r
P = load()
n = dict(closed=0, operator=0, missing=0)
missing = []
with open(out, 'w') as f:
    for r in P:
        p = Pattern(r, refined=refined)
        c = cs if p.out == (0, 1) else ct
        tgt = '%d/%d' % (c.numerator, c.denominator)
        app, ok, rad = certify_decoupled(p, c)
        if app and ok:
            rec = dict(pid=r['pid'], model=model, tiprad=str(TIPRAD), kind='closed', target=tgt, out=r['out'],
                       radii={str(k): str(v) for k, v in rad.items()})
            n['closed'] += 1
        elif r['pid'] in prod and prod[r['pid']]['status'] == 'CERTIFIED' and prod[r['pid']]['target'] == tgt:
            q = prod[r['pid']]
            rec = dict(pid=r['pid'], model=model, tiprad=str(TIPRAD), kind='operator', target=tgt, out=r['out'],
                       leafred=q['leafred'], S=q['S'], n=q['n'], float_bound=q['cS'], num_min=q['val'], sectors=q['sectors'])
            n['operator'] += 1
        else:
            n['missing'] += 1; missing.append(r['pid'])
            continue
        f.write(json.dumps(rec) + '\n')
print(model, 'tip radius', TIPRAD, 'targets', cs, ct, n, 'missing', missing[:20])
