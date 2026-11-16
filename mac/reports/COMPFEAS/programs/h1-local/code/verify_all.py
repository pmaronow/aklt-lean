"""Independent re-check of the stored certificates (no optimisation, deterministic, exact arithmetic).

Usage: verify_all.py certificates.jsonl [part nparts]
Each line: {"pid", "model" (covered|refined), "kind": "closed" | "operator", "target": "p/q", and for operator
certificates "leafred" and "S"}.  closed: exact rational check of Prop. 1.4 (closed_exact.certify_decoupled);
operator: exact integer tensors, inversion set S, Bareiss positive-definiteness on the sector of least |S^z|
(cert.Certificate.exact).  Prints the number of certificates verified and any failure."""
import sys, json, time
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/otis-claude/research/aklt-gap/agents/70-local-bounds/code')
from ring import Pattern, load
from cert import Certificate
from closed_exact import certify_decoupled

P = load()
recs = [json.loads(l) for l in open(sys.argv[1])]
if len(sys.argv) > 3:
    recs = recs[int(sys.argv[2])::int(sys.argv[3])]
t0 = time.time(); ok = 0; bad = []
for r in recs:
    refined = (r['model'] == 'refined')
    p_, q_ = map(int, r['target'].split('/'))
    if r['kind'] == 'closed':
        app, good, rad = certify_decoupled(Pattern(P[r['pid']], refined=refined), Fr(p_, q_))
        good = app and good
    else:
        c = Certificate(P[r['pid']], refined=refined, leafred=r['leafred'])
        good = c.exact(tuple(r['S']), p_, q_, least_only=True)['ok']
    if good:
        ok += 1
    else:
        bad.append(r['pid'])
print('certificates', len(recs), 'verified', ok, 'failed', bad, 'time %.0fs' % (time.time() - t0))
