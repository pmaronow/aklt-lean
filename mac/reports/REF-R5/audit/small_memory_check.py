"""Exact-rational, independent check of a small tailmem5 instance.

Uses dual coordinates for the quotient and direct per-response products for
the prefix, rather than the C recurrence. This is a finite numerical check.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import cache
from math import prod
import sys

D = ((1, 0), (0, 1), (-1, 0), (0, -1))
ROW = sys.argv[1] if len(sys.argv) > 1 else 'B'
FIRST = int(sys.argv[2]) if len(sys.argv) > 2 else 1
CS = sys.argv[3] if len(sys.argv) > 3 else '.961'
CT = sys.argv[4] if len(sys.argv) > 4 else '.935'
MODE = sys.argv[5] if len(sys.argv) > 5 else 'A'
INFILE = sys.argv[6] if len(sys.argv) > 6 else 'audit/tailmem5_B_N_small.txt'
XS, XT = 1/F(CS), 1/F(CT)
CA, CB, HC = F('0.18094'), F('0.36751'), F.from_float(1.23)
K, M, L = 9, 4, 8
STOP, TSTAR = (12, 33) if MODE == 'A' else (18, 15)
U, C, TARGET = (-1, 0), (0, 0), ((1, 0) if ROW == 'B' else (0, 1))

def add(a, b):
    return (a[0] + b[0], a[1] + b[1])

def cls(a):
    return ((a[0] + a[1]) % (2*K), (a[0] - a[1]) % (2*K))

def move(q, d):
    x, y = D[d]
    return ((q[0]+x+y) % (2*K), (q[1]+x-y) % (2*K))

def pairs(site, arrival, out):
    back = (arrival+2) % 4
    other = [add(site, D[d]) for d in range(4) if d not in (back, out)]
    dest = add(site, D[out])
    return ((other[0], other[1], CA), (other[0], dest, CB), (other[1], dest, CB))

def kap(site, arrival, out, dead):
    return sum((coef*(1 if a[0] == b[0] or a[1] == b[1] else HC)
                for a, b, coef in pairs(site, arrival, out)
                if not dead(a) and not dead(b)), F(0))

def basic(phase, kind):
    if kind == 'r':
        return F(1, 5)
    if kind == 's':
        return (XS if phase != 3 else 1) / 3
    return (XT if phase == 0 else 1) / 3

def prefix_weights(passages):
    a = prod((basic(0, kind) for kind, _ in passages), start=F(1))
    b = prod((basic(1, kind) for kind, _ in passages), start=F(1))
    c, d = F(0), F(0)
    for j, (kind, coefficient) in enumerate(passages):
        if kind == 'r':
            continue
        before, after = (0, 2) if kind == 't' else (1, 3)
        term = (XT if kind == 't' else XS) * coefficient / 3
        term *= prod((basic(before, kind0) for kind0, _ in passages[:j]), start=F(1))
        term *= prod((basic(after, kind0) for kind0, _ in passages[j+1:]), start=F(1))
        if kind == 't': c += term
        else: d += term
    return (a, b, c, d)

def optimal_value(passages):
    nonrev = [(XS if kind == 's' else XT, coefficient)
              for kind, coefficient in passages if kind != 'r']
    nonrev.sort(key=lambda item: (item[0]-1)/(item[0]*item[1]) if item[1] else F(10**9))
    p, total = F(1), F(0)
    for x, coefficient in nonrev:
        p *= x
        total += p*coefficient
    return total * F(1, 3)**len(passages) * F(3, 5)**sum(kind == 'r' for kind, _ in passages)

V = defaultdict(lambda: [F(0)]*4)
E = defaultdict(F)
counts = Counter()

def prefix(site, directions, passages, departures, bonds):
    n = len(directions)
    if site == TARGET:
        E[n] += optimal_value(passages)
        counts[n] += 1
        return
    if n == L:
        weights = prefix_weights(passages)
        state = (directions[-M:], cls(site))
        for phase in range(4): V[state][phase] += weights[phase]
        return
    for d in range(4):
        if n == 0 and FIRST >= 0 and d != FIRST:
            continue
        dest = add(site, D[d])
        bond = frozenset((site, dest))
        if dest == C or bond in bonds:
            continue
        arrival = directions[-1] if directions else 2
        kind = 'r' if departures[site] else ('s' if d == arrival else 't')
        coefficient = F(0) if kind == 'r' else kap(site, arrival, d, lambda z: z == C or departures[z] >= 2)
        departures[site] += 1
        prefix(dest, directions+(d,), passages+((kind, coefficient),), departures, bonds | {bond})
        departures[site] -= 1

prefix(U, (), (), Counter(), set())

@cache
def window_moves(omega):
    pos = [(0, 0)]
    for d in omega: pos.append(add(pos[-1], D[d]))
    bonds = {frozenset((a, b)) for a, b in zip(pos, pos[1:])}
    answer = []
    for d in range(4):
        dest = add(pos[-1], D[d])
        if frozenset((pos[-1], dest)) in bonds:
            continue
        kind = 'r' if pos[-1] in pos[:-1] else ('s' if d == omega[-1] else 't')
        answer.append((d, omega[1:]+(d,), kind))
    return answer

results = {('E', n): value for n, value in E.items()}
for n in range(L+1, STOP+1):
    exact = n <= TSTAR
    nextV = defaultdict(lambda: [F(0)]*4)
    for (omega, q), mass in V.items():
        for d, omega2, kind in window_moves(omega):
            q2 = move(q, d)
            marked = (cls(U), cls(add(U, D[FIRST]))) if FIRST >= 0 else (cls(U),)
            if exact and q in marked:
                if FIRST >= 0 and (kind == 'r' or (q == cls(U) and d == FIRST) or (q == cls(add(U, D[FIRST])) and d == (FIRST+2)%4)):
                    continue
                contribution = [x/5 for x in mass]
            else:
                contribution = [x*basic(p, kind) for p, x in enumerate(mass)]
                if kind != 'r':
                    # Recover a representative from dual quotient coordinates.
                    site = ((q[0]+q[1])//2, (q[0]-q[1])//2)
                    coefficient = kap(site, omega[-1], d, lambda z: exact and cls(z) == cls(C))
                    if kind == 't': contribution[2] += mass[0]*XT*coefficient/3
                    else: contribution[3] += mass[1]*XS*coefficient/3
            target = nextV[(omega2, q2)]
            for phase in range(4): target[phase] += contribution[phase]
    results[('D' if exact else 'F', n)] = sum((mass[2]+mass[3] for (omega, q), mass in nextV.items() if q == cls(TARGET)), F(0))
    V = {key: mass for key, mass in nextV.items() if not exact or key[1] not in (cls(C), cls(TARGET))}

printed = {}
with open(INFILE) as stream:
    for line in stream:
        fields = line.split()
        if len(fields) == 3 and fields[0] in ('E', 'D', 'F'):
            printed[(fields[0], int(fields[1]))] = F(fields[2])

print(f'Parameters: row {ROW}, first={FIRST}, m=4, L=8, K=9, mode={MODE}, cs={CS}, ct={CT}, coefficients as in the paper.')
print(f'Exact-rational checks of each E output through n=8 and each D/F output through n={STOP}:')
for key, exact in sorted(results.items(), key=lambda item: (item[0][1], item[0][0])):
    if not exact:
        continue
    bound = printed[key]
    print(*key, 'exact displayed numerically:', f'{float(exact):.15g}', 'C output:', float(bound), 'upper:', bound >= exact)
    assert bound >= exact
print('Closed-trail counts through L:', dict(sorted(counts.items())))
print('All checked upper bounds passed.')
