"""Independently check the literal data against the paper's raw-window contract.
Reads only the supplied Lean source; writes results in this report directory.
"""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
values = {}
nodes = {}
line_numbers = {}
literal_hex = {}

def interpret(node):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.Name):
        return values[node.id]
    if isinstance(node, ast.BinOp):
        a, b = interpret(node.left), interpret(node.right)
        if isinstance(node.op, ast.Add):
            return a + b
        if isinstance(node.op, ast.LShift):
            return a << b
    raise ValueError(ast.dump(node))

for line_no, line in enumerate(text.splitlines(), 1):
    m = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if m:
        name, expression = m.groups()
        node = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
        values[name] = interpret(node)
        nodes[name] = node
        line_numbers[name] = line_no
        if expression.startswith('0x'):
            literal_hex[name] = expression[2:]
assert len(literal_hex) == 786

def leaves(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return leaves(node.left, offset) + leaves(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return leaves(node.left, offset + interpret(node.right))
    raise ValueError(ast.dump(node))

layout = {}
for table in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    table_layout = sorted(leaves(nodes[table]), key=lambda p:p[1])
    current = 0
    for name, offset in table_layout:
        assert offset == current, (table, name, offset, current)
        width = 4 * len(literal_hex[name])
        assert values[name] < 2**width
        layout[name] = (offset, width)
        current += width
    assert len(set(n for n, _ in table_layout)) == len(table_layout)
    reconstructed_hex = ''.join(literal_hex[n] for n, _ in reversed(table_layout))
    assert values[table] == int(reconstructed_hex, 16)

# Byte extraction implements floor division by 2^(width*index), then remainder.
def unpack(table, width, count):
    bs = values[table].to_bytes((width*count + 7)//8, 'little') + b'\0'*4
    mask = (1 << width) - 1
    return [(int.from_bytes(bs[(width*i)//8:(width*i)//8+4], 'little') >> ((width*i)%8)) & mask
            for i in range(count)]

N = 4**10
classes = unpack('rawClass', 12, N)
reps = unpack('representatives', 20, 3741)
dest = unpack('destinations', 12, 3741*4)
kinds = unpack('edgeKinds', 2, 3741*4)
assert all(c <= 3741 for c in classes)
assert all(c < N for c in reps)
assert all(0 <= c <= 3741 for c in dest)
assert all((c == 0) == (k == 3) for c,k in zip(dest,kinds))

steps = [(1,0),(0,1),(-1,0),(0,-1)]
raw = {}
counts = [0]*11

def bond(a, b):
    return (a,b) if a < b else (b,a)

def generate(code=0, path=((0,0),), used=frozenset()):
    depth = len(path)-1
    counts[depth] += 1
    x,y = path[-1]
    if depth == 10:
        arrival = code % 4
        revisit = path[-1] in path[:-1]
        row = []
        for d,(dx,dy) in enumerate(steps):
            allowed = d != (arrival+2)%4 and bond((x,y),(x+dx,y+dy)) not in used
            kind = 2 if revisit else (0 if d == arrival else 1)
            successor = (code % (4**9))*4 + d
            row.append((allowed,kind,successor))
        raw[code] = (arrival,tuple(row))
        return
    for d,(dx,dy) in enumerate(steps):
        nxt = (x+dx,y+dy)
        edge = bond((x,y),nxt)
        if edge not in used:
            generate(4*code+d,path+(nxt,),used|{edge})

generate()
assert counts == [1,4,12,36,108,316,916,2628,7500,21268,60092]
coverage_errors = [code for code,a in enumerate(classes) if (a < 3741) != (code in raw)]
assert not coverage_errors, coverage_errors[:10]
rep_errors = [a for a,code in enumerate(reps) if code not in raw or classes[code] != a]
assert not rep_errors, rep_errors[:10]
errors = Counter()
error_examples = {}
for code,(arrival,row) in raw.items():
    a = classes[code]
    rep_arrival,rep_row = raw[reps[a]]
    for d,(allowed,kind,successor) in enumerate(row):
        i = 4*a+d
        checks = {
            'admissibility': (dest[i] != 0) == allowed,
            'representative_admissibility': rep_row[d][0] == allowed,
            'representative_kind_all_directions': rep_row[d][1] == kind,
            'kind_on_allowed': not allowed or kinds[i] == kind,
            'successor_on_allowed': not allowed or dest[i]-1 == classes[successor],
            'successor_is_raw': not allowed or successor in raw,
            'arrival_on_nonrevisit': not (allowed and kind != 2) or rep_arrival == arrival,
        }
        for check,passed in checks.items():
            if not passed:
                errors[check] += 1
                error_examples.setdefault(check,(code,a,d))
assert not errors, (dict(errors),error_examples)
edge_counts = Counter(k for c,k in zip(dest,kinds) if c)
assert edge_counts == {0:2516,1:5032,2:1872}, edge_counts

# Reverse the internal sentinels/offsets to the paper's text-file format.
archive_lines = ['60092 3741']
archive_lines += [f'{code} {classes[code]}' for code in sorted(raw)]
for a, rep in enumerate(reps):
    successors = [dest[4*a+d]-1 for d in range(4)]
    archived_kinds = [-1 if kinds[4*a+d] == 3 else kinds[4*a+d] for d in range(4)]
    archive_lines.append(' '.join(map(str, [rep] + successors + archived_kinds)))
archive_digest = hashlib.sha256(('\n'.join(archive_lines)+'\n').encode()).hexdigest()
assert archive_digest == '671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785'

summary = {
    'input_sha256': hashlib.sha256(text.encode()).hexdigest(),
    'reconstructed_archive_sha256': archive_digest,
    'reconstructed_archive_matches_recorded_digest': True,
    'parsed_literal_count':len(literal_hex),
    'packing_layouts_contiguous_and_nonoverlapping': True,
    'raw_counts_depth_0_to_10':counts,
    'raw_code_count':N,
    'valid_raw_codes':len(raw),
    'invalid_codes_with_sentinel_3741':classes.count(3741),
    'representative_count_checked':len(reps),
    'labelled_raw_directions_checked':4*len(raw),
    'edge_counts_straight_turn_revisit':[edge_counts[i] for i in range(3)],
    'errors':dict(errors),
    'targets':{},
}
for n in range(55,60):
    name = f'rawClass_{n}'
    offset,width = layout[name]
    lo,hi = offset//12,(offset+width-1)//12
    full_lo,full_hi = (offset+11)//12,(offset+width)//12-1
    codes = range(lo,hi+1)
    valid = [c for c in codes if c in raw]
    summary['targets'][name] = {
        'source_line':line_numbers[name],
        'hex_digits':len(literal_hex[name]),
        'sha256_of_hex_digits':hashlib.sha256(literal_hex[name].encode()).hexdigest(),
        'bit_offset':offset,'bit_width':width,
        'intersected_code_range_inclusive':[lo,hi],
        'fully_contained_code_range_inclusive':[full_lo,full_hi],
        'intersected_valid_raw_codes':len(valid),
        'intersected_invalid_codes':hi-lo+1-len(valid),
        'distinct_classes_on_intersected_valid_codes':len({classes[c] for c in valid}),
        'first_valid_examples':[(c,classes[c],reps[classes[c]]) for c in valid[:3]],
        'last_valid_examples':[(c,classes[c],reps[classes[c]]) for c in valid[-3:]],
    }
Path('check_results.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
