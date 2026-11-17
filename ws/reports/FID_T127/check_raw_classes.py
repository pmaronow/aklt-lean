"""Read-only audit of the five assigned packed-table chunks."""
from pathlib import Path
import ast
import hashlib
import json
import re
from collections import Counter

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
text = SOURCE.read_text()
literals = {name: int(value, 16) for name, value in re.findall(
    r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)$', text, re.M)}
raw_line = re.search(r'^noncomputable def rawClass : ℕ := (.+)$', text, re.M).group(1)

# The source puts parentheses around every addition and shift. Parse the actual
# expression instead of assuming equal-sized chunks or a chunk ordering.
tree = ast.parse(raw_line.replace('<<<', '<<'), mode='eval').body

def evaluate(node):
    if isinstance(node, ast.Name): return literals[node.id]
    if isinstance(node, ast.Constant): return node.value
    if isinstance(node, ast.BinOp):
        a, b = evaluate(node.left), evaluate(node.right)
        if isinstance(node.op, ast.Add): return a + b
        if isinstance(node.op, ast.LShift): return a << b
    raise ValueError(ast.dump(node))

def offsets(node, offset=0):
    if isinstance(node, ast.Name): return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return offsets(node.left, offset) + offsets(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return offsets(node.left, offset + evaluate(node.right))
    raise ValueError(ast.dump(node))

packed = evaluate(tree)
positions = dict(offsets(tree))
assert len(positions) == 768
intervals = sorted((o, o + 4 * len(re.search(
    rf'^private noncomputable def {name} : ℕ := 0x([0-9a-f]+)$', text, re.M).group(1)), name)
    for name, o in positions.items())
assert intervals[0][0] == 0
assert all(a[1] == b[0] for a,b in zip(intervals, intervals[1:]))
assert all(literals[name] < 1 << (end-start) for start,end,name in intervals)

STEPS = ((1,0), (0,1), (-1,0), (0,-1))
LABELS = 'ENWS'
def decode(code): return tuple((code >> (2 * (9-i))) & 3 for i in range(10))
def first_repeat(code):
    w = decode(code)
    x = y = 0
    seen = {}
    for i, d in enumerate(w):
        dx,dy = STEPS[d]
        xx,yy = x+dx,y+dy
        bond = tuple(sorted(((x,y),(xx,yy))))
        if bond in seen: return (seen[bond]+1, i+1)
        seen[bond] = i
        x,y = xx,yy
    return None

def lane(code): return (packed >> (12 * code)) & 4095

result = {'source': str(SOURCE), 'source_sha256': hashlib.sha256(text.encode()).hexdigest(),
          'packing': {'leaves': len(positions), 'allocated_bits': intervals[-1][1],
                      'integer_bit_length': packed.bit_length(), 'gaps_or_overlaps': False},
          'chunks': []}
for n in range(600,605):
    name = f'rawClass_{n}'
    start = positions[name]
    width = 4*len(re.search(rf'^private noncomputable def {name} : ℕ := 0x([0-9a-f]+)$', text, re.M).group(1))
    end = start+width
    touched = range(start//12, (end-1)//12+1)
    complete = range((start+11)//12, end//12)
    invalid = [code for code in touched if first_repeat(code) is not None]
    assert len(invalid) == len(touched)
    assert all(lane(code) == 3741 for code in touched)
    expected = sum(((3741 >> (j % 12)) & 1) << (j-start) for j in range(start,end))
    assert expected == literals[name]
    words = [''.join(LABELS[d] for d in decode(c)) for c in touched]
    common = ''
    for i in range(10):
        if len({w[i] for w in words}) != 1: break
        common += words[0][i]
    result['chunks'].append({'name': name, 'bits_inclusive': [start,end-1],
        'touched_codes_inclusive': [touched.start,touched.stop-1],
        'touched_lanes': len(touched), 'complete_codes_inclusive': [complete.start,complete.stop-1],
        'complete_lanes': len(complete), 'invalid_words': len(invalid),
        'values': dict(Counter(lane(c) for c in touched)),
        'common_word_prefix': common, 'first_word': words[0], 'last_word': words[-1],
        'first_repeated_bonds': {str(k): v for k,v in Counter(first_repeat(c) for c in touched).items()},
        'matches_sentinel_bit_slice': True})
print(json.dumps(result, indent=2, default=str))
