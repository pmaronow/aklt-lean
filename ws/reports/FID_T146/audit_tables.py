from pathlib import Path
import ast
import re
import json
from collections import Counter

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
s = SOURCE.read_text()
# Read all literal declarations and all four complete packing expressions.
values = {}
hexes = {}
for m in re.finditer(r'(?:private )?noncomputable def (\w+) : ℕ := (.*)', s):
    name, expr = m.groups()
    if expr.startswith('0x'):
        values[name] = int(expr, 16)
        hexes[name] = expr[2:]

def parse(expr):
    return ast.parse(expr.replace('<<<', '<<'), mode='eval').body

def evaluate(node):
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    a, b = evaluate(node.left), evaluate(node.right)
    if isinstance(node.op, ast.Add):
        return a + b
    assert isinstance(node.op, ast.LShift)
    return a << b

expressions = {}
for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']:
    expr = re.search(rf'^noncomputable def {name} : ℕ := (.*)$', s, re.M)[1]
    node = parse(expr)
    expressions[name] = node
    values[name] = evaluate(node)

def offsets(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node.op, ast.Add):
        return offsets(node.left, offset) + offsets(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    assert isinstance(node.right, ast.Constant)
    return offsets(node.left, offset + node.right.value)

raw_offsets = offsets(expressions['rawClass'])
assert [name for name, _ in raw_offsets] == [f'rawClass_{i}' for i in range(768)]
assert [off for _, off in raw_offsets] == [16384 * (767-i) - 4 if i < 767 else 0 for i in range(768)]
# Addition is concatenation: all chunks fit their declared slots, with no overlap.
for i, (name, off) in enumerate(raw_offsets):
    width = 16384 if i < 767 else 16380
    assert values[name] < 2**width

N = 4**10
rawhex = f'{values["rawClass"]:0{3*N}x}'
assert len(rawhex) == 3*N
raw = [int(rawhex[j:j+3], 16) for j in range(len(rawhex)-3, -1, -3)]

def lanes(name, width, count):
    n = values[name]
    # Small tables only; exact Nat.div/pow/mod interpretation.
    return [(n >> (width*i)) & ((1 << width)-1) for i in range(count)]

reps = lanes('representatives', 20, 3741)
dest = lanes('destinations', 12, 3741*4)
kinds = lanes('edgeKinds', 2, 3741*4)
steps = ((1,0), (0,1), (-1,0), (0,-1))
def decode(code):
    return tuple((code >> (2*(9-i))) & 3 for i in range(10))
def bond(p, q):
    return tuple(sorted((p, q)))
def geometry(word):
    p = (0,0)
    vertices = [p]
    bonds = []
    for d in word:
        dx,dy = steps[d]
        q = (p[0]+dx,p[1]+dy)
        bonds.append(bond(p,q))
        vertices.append(q)
        p=q
    return vertices, bonds

def israw(code):
    _, bonds = geometry(decode(code))
    return len(set(bonds)) == 10

def row(code):
    word = decode(code)
    vertices, bonds = geometry(word)
    used = set(bonds)
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    result = []
    for d,(dx,dy) in enumerate(steps):
        q = (endpoint[0]+dx, endpoint[1]+dy)
        allowed = d != (word[-1]+2)%4 and bond(endpoint,q) not in used
        kind = 2 if revisit else (0 if d==word[-1] else 1)
        successor = ((code % 4**9)*4 + d)
        result.append((allowed,kind,successor,word[-1]))
    return result

# Independent bond-distinct recursion, starting with all four absolute directions.
rawcodes = []
counts = Counter()
def generate(depth, p, used, code):
    counts[depth] += 1
    if depth == 10:
        rawcodes.append(code)
        return
    for d,(dx,dy) in enumerate(steps):
        q=(p[0]+dx,p[1]+dy)
        b=bond(p,q)
        if b not in used:
            generate(depth+1,q,used|{b},4*code+d)
generate(0,(0,0),set(),0)
rawset=set(rawcodes)
covered={code for code,a in enumerate(raw) if a<3741}
coverage_errors = list(sorted(rawset ^ covered))
range_errors=[(code,a) for code,a in enumerate(raw) if a>3741]
rep_errors=[]
for a,code in enumerate(reps):
    if not (code<N and code in rawset and raw[code]==a):
        rep_errors.append((a,code,raw[code] if code<N else None))

# Check compatibility and stored transitions for all raw states, while retaining
# separate counts for lanes intersecting each assigned chunk.
all_errors=[]
errors_by_code={}
for code in rawcodes:
    a=raw[code]
    errors=[]
    if a>=3741:
        errors.append(('invalid class',a))
    else:
        rep_row=row(reps[a])
        for d,(allowed,kind,succ,arrival) in enumerate(row(code)):
            ra,rk,rs,rarr=rep_row[d]
            dst=dest[4*a+d]
            k=kinds[4*a+d]
            if allowed != ra or kind != rk:
                errors.append(('representative compatibility',d,allowed,kind,ra,rk))
            if allowed != (dst!=0):
                errors.append(('admissibility',d,allowed,dst))
            if allowed:
                if k!=kind:
                    errors.append(('kind',d,kind,k))
                if dst-1 != raw[succ]:
                    errors.append(('successor',d,dst-1,raw[succ]))
                if kind!=2 and arrival!=rarr:
                    errors.append(('arrival',d,arrival,rarr))
    if errors:
        errors_by_code[code]=errors
        all_errors.append((code,errors))

summaries=[]
for k in range(695,700):
    name=f'rawClass_{k}'
    off=dict(raw_offsets)[name]
    low=off//12
    high=(off+16384-1)//12
    valid=[c for c in range(low,high+1) if c in rawset]
    bad=[c for c in range(low,high+1) if c in errors_by_code or ((raw[c]<3741)!=(c in rawset)) or raw[c]>3741]
    sentinel_piece=0
    for c in range(low,high+1):
        sentinel_piece |= 3741 << (12*c-low*12)
    sentinel_piece=(sentinel_piece >> (off-low*12)) & ((1<<16384)-1)
    summaries.append(dict(name=name, line=15+2*k, bit_low=off, bit_high=off+16383,
        code_low=low,code_high=high,entry_count=high-low+1,
        raw_count=len(valid),invalid_count=high-low+1-len(valid),
        class_range=[min((raw[c] for c in valid),default=None),max((raw[c] for c in valid),default=None)],
        error_count=len(bad), first_raw=valid[:6],last_raw=valid[-6:],
        equals_pure_sentinel=values[name]==sentinel_piece))

output=dict(counts=dict(sorted(counts.items())),packed_bit_length=values['rawClass'].bit_length(),
    coverage_error_count=len(coverage_errors),coverage_errors=coverage_errors[:10],
    range_error_count=len(range_errors),range_errors=range_errors[:10],
    representative_error_count=len(rep_errors),representative_errors=rep_errors[:10],
    transition_error_count=len(all_errors),transition_errors=all_errors[:10],
    row_encoding_errors=sum(not (0<=d<=3741 and ((d==0)==(k==3)) and (d==0 or k<3)) for d,k in zip(dest,kinds)),
    edge_counts=dict(Counter(k for d,k in zip(dest,kinds) if d!=0)),assigned=summaries)
Path('audit_results.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
assert not coverage_errors and not range_errors and not rep_errors and not all_errors
assert output['row_encoding_errors'] == 0
assert [counts[i] for i in range(1,11)] == [4,12,36,108,316,916,2628,7500,21268,60092]
assert output['edge_counts'] == {0:2516,1:5032,2:1872}
assert all(item['error_count'] == 0 for item in summaries)
