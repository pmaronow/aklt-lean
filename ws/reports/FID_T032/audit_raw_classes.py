"""Read-only arithmetic/geometry audit of the five assigned packed fragments."""
import ast
import json
import re
from pathlib import Path

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {}
expressions = {}
for line in source.splitlines():
    match = re.fullmatch(r'(?:private )?(?:noncomputable )?def (\w+) : ℕ := (.*)', line)
    if match:
        name, body = match.groups()
        if re.fullmatch(r'0x[0-9a-f]+', body):
            literals[name] = int(body, 16)
        else:
            expressions[name] = ast.parse(body.replace('<<<', '<<'), mode='eval').body


def value(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    if isinstance(node, ast.BinOp):
        left, right = value(node.left), value(node.right)
        if isinstance(node.op, ast.Add):
            return left + right
        if isinstance(node.op, ast.LShift):
            return left << right
    raise ValueError(ast.dump(node))


def fragments(node, offset=0):
    if isinstance(node, ast.Name):
        return [(node.id, offset)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Add):
        return fragments(node.left, offset) + fragments(node.right, offset)
    assert isinstance(node.op, ast.LShift)
    return fragments(node.left, offset + value(node.right))


# Read and validate every generated literal and each concatenation, including
# non-assigned data, so offsets are established from the entire source expression.
inventory = {}
packed = {}
for name, expr in expressions.items():
    parts = fragments(expr)
    assert len({part for part, _ in parts}) == len(parts)
    assert all(offset >= 0 for _, offset in parts)
    ordered = sorted(parts, key=lambda item: item[1])
    for (part, offset), (_, next_offset) in zip(ordered, ordered[1:]):
        assert literals[part].bit_length() <= next_offset - offset
    packed[name] = value(expr)
    inventory[name] = {'fragments': len(parts), 'bits': packed[name].bit_length()}

raw_parts = fragments(expressions['rawClass'])
assert [name for name, _ in raw_parts] == [f'rawClass_{i}' for i in range(768)]
offsets = dict(raw_parts)
assert offsets['rawClass_767'] == 0
assert offsets['rawClass_766'] == 16380
assert all(offsets[f'rawClass_{i}'] == 16380 + (766-i)*16384 for i in range(767))


def word(code):
    return [(code >> (2*(9-i))) & 3 for i in range(10)]


def is_raw(directions):
    point = (0, 0)
    used = set()
    for direction in directions:
        dx, dy = [(1, 0), (0, 1), (-1, 0), (0, -1)][direction]
        successor = (point[0] + dx, point[1] + dy)
        bond = frozenset((point, successor))
        if bond in used:
            return False
        used.add(bond)
        point = successor
    return True


sentinel = 3741
results = []
all_codes = set()
for i in range(125, 130):
    name = f'rawClass_{i}'
    offset = offsets[name]
    width = 16384
    first_code, last_code = offset // 12, (offset + width - 1) // 12
    phase = offset % 12
    count = (width + phase + 11) // 12
    repeated = sentinel * ((1 << (12*count)) - 1) // ((1 << 12) - 1)
    expected = (repeated >> phase) & ((1 << width) - 1)
    assert literals[name] == expected
    codes = range(first_code, last_code + 1)
    assert all(word(code)[:2] == [3, 1] for code in codes)
    assert all(not is_raw(word(code)) for code in codes)
    assert all((packed['rawClass'] >> (12*code)) & 4095 == sentinel for code in codes)
    all_codes.update(codes)
    results.append({
        'declaration': name,
        'line': source[:source.index(f'private noncomputable def {name} :')].count('\n') + 1,
        'low_bit': offset,
        'high_bit_inclusive': offset + width - 1,
        'touched_codes_inclusive': [first_code, last_code],
        'touched_codes_count': len(codes),
        'low_bit_mod_12': phase,
        'exact_sentinel_fragment': True,
        'all_touched_words_begin_south_north': True,
        'raw_word_count_in_interval': 0,
        'all_decoded_class_lanes_are_3741': True,
    })

output = {'inventory': inventory, 'results': results, 'distinct_touched_codes': len(all_codes)}
Path('audit_results.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output, indent=2))
