"""Small independent exact operator replay, without NumPy.

Uses sparse site-moment factors, variable elimination, and a Walsh transform
of Pauli coefficients; then integer congruence and Bareiss with divmod checks.
This does not import the bundled coefficient or matrix implementations.
"""
import collections
from fractions import Fraction as F
import itertools
import json
from math import gcd, lcm
import sys
import time
from audit_stdlib import B, P, V, E, N, W, S, D1, CORN, TIPS, RING, edge, unpack

def groups_for(rec):
    kinds,bonds,out = unpack(P[rec['pid']])
    groups = []
    for x in RING:
        if x in D1:
            count = int(edge(x,TIPS[x]) in bonds)
        else:
            degree = sum(x in b for b in bonds)
            count = (1 if degree == 1 and rec['leafred'] else 2) if degree else 0
        if count:
            groups.append((x,count,kinds[x]))
    return groups

def dfact(n):
    answer = 1
    for i in range(n,1,-2):
        answer *= i
    return answer

def moment(kind, columns):
    counts = [columns.count(c) for c in (1,2,3)]
    if any(e % 2 for e in counts):
        return F(0)
    degree = sum(counts)
    if degree == 0:
        return F(1)
    result = F(dfact(counts[0]-1)*dfact(counts[1]-1)*dfact(counts[2]-1), dfact(degree+1))
    return result if kind == 'u' else result * F(3,5)

def join(a, b):
    av,ad = a; bv,bd = b
    common = [v for v in av if v in bv]
    ai = [av.index(v) for v in common]
    bi = [bv.index(v) for v in common]
    ar = [i for i,v in enumerate(av) if v not in common]
    br = [i for i,v in enumerate(bv) if v not in common]
    indexed = collections.defaultdict(list)
    for row,value in bd.items():
        indexed[tuple(row[i] for i in bi)].append((tuple(row[i] for i in br),value))
    out = collections.defaultdict(int)
    for row,value in ad.items():
        left = tuple(row[i] for i in ar)
        for right,value2 in indexed.get(tuple(row[i] for i in ai), ()):
            out[left+right] += value*value2
    return [av[i] for i in ar]+[bv[i] for i in br], dict(out)

def integral(rec, pair=None):
    kinds,bonds,out = unpack(P[rec['pid']])
    groups = groups_for(rec)
    external = {}
    pos = 0
    for x,count,kind in groups:
        external[x] = list(range(pos,pos+count)); pos += count
    ring_edges = {edge(RING[i],RING[(i+1)%8]): 100+i for i in range(8)
                  if edge(RING[i],RING[(i+1)%8]) in bonds}
    factors = []
    for x in RING:
        iv = sorted(v for b,v in ring_edges.items() if x in b)
        if pair is not None and x in pair:
            iv.append(200)
        ev = external.get(x,[])
        kind = kinds.get(x,'u')
        if not iv and not ev and x not in kinds:
            continue
        vars_ = iv+ev
        leaf = x in CORN and rec['leafred'] and sum(x in b for b in bonds) == 1
        if leaf:
            assert len(iv) == len(ev) == 1
            radius = F(1,2) if kind == 'u' else F(1,3)
            data = {(i,i): radius.denominator if i == 0 else radius.numerator for i in range(4)}
        else:
            denominator = 15 if kind == 'u' else 25
            data = {}
            for row in itertools.product(*(range(1,4) if v == 200 else range(4) for v in vars_)):
                value = denominator * moment(kind,list(row))
                if ev and x in D1:
                    assert len(ev) == 1
                    value *= 5 if row[-1] == 0 else 3
                assert value.denominator == 1
                if value:
                    data[row] = value.numerator
        factors.append((vars_,data))
    accumulator = ([],{():1})
    for factor in factors:
        accumulator = join(accumulator, factor)
    order,data = accumulator
    assert sorted(order) == list(range(pos))
    indices = [order.index(i) for i in range(pos)]
    return {tuple(row[i] for i in indices): val for row,val in data.items()}

def coefficients(rec):
    # Every integral uses the same deliberately generous product denominator.
    kinds,bonds,out = unpack(P[rec['pid']])
    live = [x for x in (E,N,W) if edge(V,x) in bonds]
    z = integral(rec)
    cur = collections.defaultdict(int, {a:3*v for a,v in z.items()})
    nxt = collections.defaultdict(int, {a:5*v for a,v in z.items()})
    fg = [x for x in live if x != out]
    for x,y in itertools.combinations(live,2):
        c = integral(rec,(x,y))
        for a,v in c.items():
            cur[a] += v
            if set((x,y)) == set(fg):
                nxt[a] += v
    threshold = F(rec['target'])
    answer = {a:5*threshold.denominator*cur[a]-3*threshold.numerator*nxt[a] for a in set(cur)|set(nxt)}
    answer = {a:v for a,v in answer.items() if v}
    divisor = 0
    for v in answer.values():
        divisor = gcd(divisor,v)
    assert divisor > 0
    return {a:v//divisor for a,v in answer.items()}

def central_matrix(coeff, inverted, n):
    size = 1 << n
    data = collections.defaultdict(dict)
    for a,value in coeff.items():
        flip = sign = ys = inv = 0
        for i,c in enumerate(a):
            bit = 1 << (n-1-i)
            if c in (1,2): flip |= bit
            if c in (2,3): sign |= bit
            ys += c == 2
            inv += i in inverted and c != 0
        assert ys % 2 == 0
        value *= -1 if (ys//2+inv) % 2 else 1
        data[flip][sign] = value
    middle = n//2
    states = [s for s in range(size) if s.bit_count() == middle]
    matrix = {}
    for flip,entries in data.items():
        values = [0]*size
        for sign,value in entries.items():
            values[sign] = value
        half = 1
        while half < size:
            for base in range(0,size,2*half):
                for j in range(base,base+half):
                    a,b = values[j],values[j+half]
                    values[j],values[j+half] = a+b,a-b
            half *= 2
        assert all(value == 0 or col.bit_count() == (col^flip).bit_count() for col,value in enumerate(values))
        for col in states:
            value = values[col]
            if value:
                matrix[col^flip,col] = value
    assert all(matrix.get((c,r),0) == v for (r,c),v in matrix.items())
    return matrix

def supports(groups, antisymmetric):
    options = []
    singles = 0; dpos = 0
    for site,count,kind in groups:
        if count == 1:
            options.append([(1,[(0,1)]),(-1,[(1,1)])]); singles += 1
        else:
            anti = False
            if kind == 'd':
                anti = antisymmetric[dpos]; dpos += 1
            if anti:
                options.append([(0,[(1,1),(2,-1)])])
            else:
                options.append([(2,[(0,1)]),(0,[(1,1),(2,1)]),(-2,[(3,1)])])
    result = {}; dimension = 0
    for choice in itertools.product(*options):
        if sum(c[0] for c in choice) != singles % 2:
            continue
        terms = [(0,1)]
        for (_,count,_),(_,terms2) in zip(groups,choice):
            terms = [((a << count)|b, x*y) for a,x in terms for b,y in terms2]
        for state,value in terms:
            assert state not in result
            result[state] = dimension,value
        dimension += 1
    return dimension,result

def positive_definite(matrix):
    # Bareiss, with explicit divisibility checks at every update.
    a = [row[:] for row in matrix]
    previous = 1
    for k in range(len(a)):
        pivot = a[k][k]
        if pivot <= 0:
            return False,k
        for i in range(k+1,len(a)):
            for j in range(i,len(a)):
                value,remainder = divmod(a[i][j]*pivot-a[k][i]*a[k][j], previous)
                assert remainder == 0
                a[i][j] = value
        previous = pivot
    return True,None

def verify(rec):
    start = time.monotonic()
    coeff = coefficients(rec)
    print('COEFFICIENTS',rec['pid'],'n',rec['n'],'terms',len(coeff),'seconds',round(time.monotonic()-start,2),flush=True)
    original = central_matrix(coeff,set(rec['S']),rec['n'])
    groups = groups_for(rec)
    dcount = sum(count == 2 and kind == 'd' for _,count,kind in groups)
    sizes = []
    for eps in itertools.product((False,True),repeat=dcount):
        dim,support = supports(groups,eps)
        a = [[0]*dim for _ in range(dim)]
        for (r,c),value in original.items():
            if r in support and c in support:
                i,si = support[r]; j,sj = support[c]
                a[i][j] += si*sj*value
        assert all(a[i][j] == a[j][i] for i in range(dim) for j in range(dim))
        good,where = positive_definite(a)
        assert good, (rec['pid'],eps,where)
        sizes.append(dim)
    print('EXACT OPERATOR PASS',rec['pid'],'sizes',sizes,'seconds',round(time.monotonic()-start,2),flush=True)

if __name__ == '__main__':
    records = {r['pid']:r for r in map(json.loads,(B/'programs/h1-local/out/certificates_covered_operator_only.jsonl').read_text().splitlines())}
    if len(sys.argv) > 1 and sys.argv[1] == '--all':
        part,parts = map(int,sys.argv[2:4])
        selected = sorted(records)[part::parts]
    else:
        selected = [int(x) for x in sys.argv[1:]] or [0,113,640,1382,2180,3596,3626,5420,5469,7645,7697,7725]
    start_all = time.monotonic()
    for pid in selected:
        verify(records[pid])
    print('COMPLETE',len(selected),'certificates; elapsed seconds',round(time.monotonic()-start_all,2),flush=True)
