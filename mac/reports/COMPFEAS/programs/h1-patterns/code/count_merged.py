from realizable import *
R = enumerate_realizable()
TSET = set([V] + D1 + CORN + TIPS)
def merged_key(kinds, absent, out):
    # drop absent bonds that are legs leaving the template (treated as slots) and tip-side info
    a = frozenset(b for b in absent if b[0] in TSET and b[1] in TSET and b[0] not in TIPS and b[1] not in TIPS)
    # d1-tip bonds: keep (they matter on the d1 side)
    a2 = frozenset(b for b in absent if (b[0] in TIPS or b[1] in TIPS))
    k = dict(kinds)
    # a corner passed once that keeps no d1 bond is decoupled: same as 'c'
    for c in CORN:
        if k[c] == 'd':
            kept = [y for y in nbrs(c) if y in D1 and bkey(c, y) not in absent]
            if not kept:
                k[c] = 'c'
    return canon(k, a | a2, out)
for out in [(0, 1), (1, 0)]:
    keys = set(merged_key(k, a, out) for k, a in R)
    print(out, len(keys))
