"""Independent finite checks for the five assigned Automaton10Data chunks."""
from pathlib import Path
import ast
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
chunks = {}
lines = {}
for number, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)', line)
    if match:
        chunks[match[1]] = int(match[2], 16)
        lines[match[1]] = number

assemblies = {}
for name in ['rawClass', 'representatives', 'destinations', 'edgeKinds']:
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    assemblies[name] = ast.parse(expression.replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return chunks[node.id]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return evaluate(node.left) + evaluate(node.right)
    assert isinstance(node.op, ast.LShift) and isinstance(node.right, ast.Constant)
    return evaluate(node.left) << node.right.value


def leaves(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    if isinstance(node.op, ast.Add):
        return leaves(node.left, offset) + leaves(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    return leaves(node.left, offset + node.right.value)


# Check the entire assembly so the five chunks' offsets follow the actual source.
raw_leaves = leaves(assemblies['rawClass'])
assert len(raw_leaves) == 768
assert len(set(name for name, _ in raw_leaves)) == 768
ordered = sorted(raw_leaves, key=lambda pair: pair[1])
for i, (name, offset) in enumerate(ordered):
    end = ordered[i + 1][1] if i + 1 < len(ordered) else 12 * 4**10
    assert chunks[name].bit_length() <= end - offset
    if i:
        assert offset == ordered[i-1][1] + (16380 if i == 1 else 16384)
assert ordered[0] == ('rawClass_767', 0)
raw_packed = evaluate(assemblies['rawClass'])
raw_bytes = raw_packed.to_bytes((12 * 4**10 + 7) // 8, 'little')


def raw_class_at(code):
    byte, bit = divmod(12 * code, 8)
    return (int.from_bytes(raw_bytes[byte:byte+2], 'little') >> bit) & 4095


def word(code):
    return [(code >> (2 * (9-i))) & 3 for i in range(10)]


def first_repeated_bond(code):
    directions = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    x, y = 0, 0
    used = {}
    for i, d in enumerate(word(code)):
        dx, dy = directions[d]
        new = (x+dx, y+dy)
        bond = tuple(sorted(((x, y), new)))
        if bond in used:
            return (used[bond], i)
        used[bond] = i
        x, y = new
    return None


def sentinel_slice(offset, width):
    start_lane, residue = divmod(offset, 12)
    count = (residue + width + 11) // 12
    repeated = sum(3741 << (12 * i) for i in range(count))
    return (repeated >> residue) & ((1 << width) - 1)


for j in range(540, 545):
    name = f'rawClass_{j}'
    offset = dict(raw_leaves)[name]
    width = 16384
    assert chunks[name] == sentinel_slice(offset, width)
    first = offset // 12
    last = (offset + width - 1) // 12
    invalid = [code for code in range(first, last+1) if first_repeated_bond(code) is not None]
    assert len(invalid) == last - first + 1
    assert all(raw_class_at(code) == 3741 for code in range(first, last+1))
    print(f'{name} line={lines[name]} bits=[{offset},{offset+width}) '
          f'phase={offset%12} codes=[{first},{last}] count={len(invalid)} '
          f'base4_endpoints={"".join(map(str,word(first)))}..{"".join(map(str,word(last)))} '
          f'exact_sentinel_bits=True all_words_repeat_bonds=True all_full_lanes_3741=True')

# Independently regenerate the raw set by the paper's recursion.
raw_codes = set()
counts = [0] * 11
DIRECTIONS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
def generate(x, y, depth, code, used):
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        return
    for d, (dx, dy) in enumerate(DIRECTIONS):
        nx, ny = x+dx, y+dy
        bond = tuple(sorted(((x, y), (nx, ny))))
        if bond not in used:
            used.add(bond)
            generate(nx, ny, depth+1, 4*code+d, used)
            used.remove(bond)
generate(0, 0, 0, 0, set())
assert counts[1:] == [4,12,36,108,316,916,2628,7500,21268,60092]
valid_classes = set()
for code in range(4**10):
    value = raw_class_at(code)
    assert value <= 3741
    assert (value < 3741) == (code in raw_codes)
    if code in raw_codes:
        valid_classes.add(value)
assert valid_classes == set(range(3741))
print('Context check: raw cardinalities match paper; all 1048576 raw-code lanes have correct validity; all 3741 classes occur.')
print('Assigned constants are exact 16384-bit portions of the invalid-word sentinel 0xE9D=3741.')
