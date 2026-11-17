"""Read-only reconstruction of the five assigned packed-table chunks."""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^(?:private )?noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)$',
        source, re.M,
    )
}

def expression(name):
    line = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)[1]
    return ast.parse(line.replace('<<<', '<<'), mode='eval').body


def value(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return value(node.left) + value(node.right)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return value(node.left) << value(node.right)
    raise ValueError(ast.dump(node))


def contributions(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return contributions(node.left, offset) + contributions(node.right, offset)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return contributions(node.left, offset + value(node.right))
    raise ValueError(ast.dump(node))

raw_expr = expression('rawClass')
positions = dict(contributions(raw_expr))
assert len(positions) == 768
assert positions['rawClass_767'] == 0
assert all(positions[f'rawClass_{i}'] == (767-i)*16384-4 for i in range(767))
assert literals['rawClass_767'] < 1 << 16380
assert all(literals[f'rawClass_{i}'] < 1 << 16384 for i in range(768))
raw = value(raw_expr)
raw_bytes = raw.to_bytes(12 * 4**10 // 8, 'little')


def lane(code):
    bit = 12 * code
    byte, shift = divmod(bit, 8)
    return (int.from_bytes(raw_bytes[byte:byte+3], 'little') >> shift) & 4095


def directions(code):
    return [(code >> (2*(9-i))) & 3 for i in range(10)]


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def first_repeat(code):
    x, y = 0, 0
    bonds = {}
    for i, d in enumerate(directions(code)):
        dx, dy = STEPS[d]
        endpoint = (x+dx, y+dy)
        bond = tuple(sorted(((x, y), endpoint)))
        if bond in bonds:
            return bonds[bond], i
        bonds[bond] = i
        x, y = endpoint
    return None


print('All 768 chunks occur once, in order; the final chunk has width 16380, all other slots 16384; no chunk overflows.')
print('Assigned literal coverage (inclusive code ranges, bit ranges half-open):')
for i in range(365, 370):
    name = f'rawClass_{i}'
    low = positions[name]
    high = low+16384
    first, last = low//12, (high-1)//12
    residual = low % 12
    copies = (residual+16384+11)//12
    expected = (3741*((1 << (12*copies))-1)//4095 >> residual) & ((1 << 16384)-1)
    assert literals[name] == expected, name
    repeats = Counter(first_repeat(code) for code in range(first,last+1))
    assert None not in repeats, (name, repeats)
    decoded = Counter(lane(code) for code in range(first,last+1))
    assert decoded == Counter({3741:last-first+1}), (name, decoded)
    words = [''.join(map(str,directions(code))) for code in (first,last)]
    prefix=''
    for a,b in zip(*words):
        if a!=b: break
        prefix+=a
    print(f'{name}: source line {15+2*i}; bits [{low},{high}); codes {first}..{last}; '
          f'{last-first+1} touched words; offset mod 12={residual}; '
          f'exact sentinel slice=True; lane values={dict(decoded)}; '
          f'common prefix={prefix}; first repeated bonds (0-based)={dict(repeats)}')
    print(f'  literal SHA-256 (lowercase hex digits): '
          f'{hashlib.sha256(format(literals[name],"x").encode()).hexdigest()}')

# Independent enumeration from the paper's extend-by-unused-bond recursion.
counts = [0]*11
valid_codes = []

def generate(depth, code, point, used):
    counts[depth] += 1
    if depth == 10:
        valid_codes.append(code)
        return
    x,y = point
    for d,(dx,dy) in enumerate(STEPS):
        endpoint = (x+dx,y+dy)
        bond = tuple(sorted((point,endpoint)))
        if bond not in used:
            used.add(bond)
            generate(depth+1,code*4+d,endpoint,used)
            used.remove(bond)

generate(0,0,(0,0),set())
assert counts == [1,4,12,36,108,316,916,2628,7500,21268,60092], counts
valid_set = set(valid_codes)
coverage = Counter()
for code in range(4**10):
    entry = lane(code)
    assert entry <= 3741
    assert (entry < 3741) == (code in valid_set), (code,entry)
    coverage['raw' if entry < 3741 else 'invalid'] += 1
print('Independent raw-window recursion counts:',counts)
print('Exhaustive rawClassAt coverage over all 4^10 words:',dict(coverage))
print('PASS: five exact sentinel slices; every touched word is outside the raw-window domain.')
