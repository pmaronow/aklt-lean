from pathlib import Path
import re
from collections import Counter

source = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean').read_text()
values = {m[1]: int(m[2], 16) for m in re.finditer(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', source)}

def expression(text):
    tokens = re.findall(r'\w+|<<<|[()+]', text)
    i = 0
    def atom():
        nonlocal i
        t = tokens[i]; i += 1
        if t == '(':
            v = add()
            assert tokens[i] == ')'
            i += 1
            return v
        return int(t) if t.isdecimal() else values[t]
    def shift():
        nonlocal i
        v = atom()
        while i < len(tokens) and tokens[i] == '<<<':
            i += 1
            v <<= atom()
        return v
    def add():
        nonlocal i
        v = shift()
        while i < len(tokens) and tokens[i] == '+':
            i += 1
            v += shift()
        return v
    value = add()
    assert i == len(tokens)
    return value

for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']:
    expr = re.search(r'noncomputable def ' + name + r' : ℕ := (.*)', source)[1]
    values[name] = expression(expr)

def lanes(name, width, count):
    packed = values[name]
    mask = (1 << width) - 1
    assert packed.bit_length() <= width * count
    data = packed.to_bytes((width * count + 7) // 8, 'little') + b'\0\0\0'
    return [(int.from_bytes(data[(width*i)//8:(width*i)//8+4], 'little') >> ((width*i)%8)) & mask
            for i in range(count)]

raw = lanes('rawClass', 12, 4**10)
reps = lanes('representatives', 20, 3741)
dest = lanes('destinations', 12, 3741*4)
kind = lanes('edgeKinds', 2, 3741*4)
steps = [(1,0),(0,1),(-1,0),(0,-1)]

def path(word):
    p = [(0,0)]; bonds = set()
    for d in word:
        x,y = p[-1]; dx,dy = steps[d]
        z = x+dx,y+dy
        edge = frozenset((p[-1],z))
        if edge in bonds:
            return None
        bonds.add(edge); p.append(z)
    return p,bonds

def decode(code):
    return tuple((code >> (2*i)) & 3 for i in range(9,-1,-1))

raw_codes = set()
counts = []
def visit(word, p, bonds, code):
    n = len(word)
    if len(counts) <= n: counts.append(0)
    counts[n] += 1
    if n == 10:
        raw_codes.add(code)
        a = raw[code]
        assert a < 3741, ('raw class',code,a)
        x,y = p[-1]
        for d,(dx,dy) in enumerate(steps):
            z = x+dx,y+dy
            allowed = d != (word[-1]+2)%4 and frozenset((p[-1],z)) not in bonds
            lane = a*4+d
            assert (dest[lane] != 0) == allowed, ('allowed',code,a,d)
            if allowed:
                k = 2 if p[-1] in p[:-1] else (0 if d == word[-1] else 1)
                assert kind[lane] == k, ('kind',code,a,d)
                successor_code = ((code % (4**9))*4+d)
                assert dest[lane]-1 == raw[successor_code], ('successor',code,a,d)
                assert successor_code in raw_codes or raw[successor_code] < 3741
                if k != 2: assert reps[a]%4 == word[-1], ('arrival',code,a,d)
        return
    x,y = p[-1]
    for d,(dx,dy) in enumerate(steps):
        z = x+dx,y+dy; edge = frozenset((p[-1],z))
        if edge not in bonds:
            visit(word+(d,),p+[z],bonds|{edge},code*4+d)

visit((),[(0,0)],set(),0)
assert len(raw_codes) == 60092
for code,a in enumerate(raw):
    assert a <= 3741
    assert (a < 3741) == (code in raw_codes), ('raw coverage',code,a)
for a,c in enumerate(reps):
    assert c < 4**10 and c in raw_codes and raw[c] == a, ('rep',a,c)
for t,k in zip(dest,kind):
    assert t <= 3741 and (t == 0) == (k == 3) and (t == 0 or k < 3)
print('All literal expressions parsed; packed lengths and every table lane checked.')
print('Raw window counts by length:', counts[1:])
print('All 4^10 raw-code sentinel/coverage checks passed.')
print('All 3741 representatives, all admissibility/kind/successor/arrival comparisons passed.')
print('Admitted edge counts:', dict(Counter(k for t,k in zip(dest,kind) if t)))
