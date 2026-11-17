"""Read-only reconstruction of the assigned packed Lean data from paper rules."""
from array import array
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(hexadecimal, 16)
    for name, hexadecimal in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', source, re.M
    )
}


def expression(name):
    text = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', source, re.M)[1]
    return ast.parse(text.replace('<<<', '<<'), mode='eval').body


def evaluate(node):
    if isinstance(node, ast.Name):
        return literals[node.id]
    if isinstance(node, ast.Constant):
        return node.value
    assert isinstance(node, ast.BinOp)
    a, b = evaluate(node.left), evaluate(node.right)
    if isinstance(node.op, ast.LShift):
        return a << b
    assert isinstance(node.op, ast.Add)
    return a + b


def offsets(node, shift=0):
    if isinstance(node, ast.Name):
        return [(node.id, shift)]
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.LShift):
        return offsets(node.left, shift + evaluate(node.right))
    assert isinstance(node.op, ast.Add)
    return offsets(node.left, shift) + offsets(node.right, shift)


def unpack(name, width, length):
    packed = evaluate(expression(name))
    data = packed.to_bytes((width * length + 7) // 8, 'little') + b'\0\0\0\0'
    mask = (1 << width) - 1
    return array('I', (
        (int.from_bytes(data[(width * i) // 8:(width * i) // 8 + 4], 'little')
         >> ((width * i) % 8)) & mask
        for i in range(length)
    ))


raw = unpack('rawClass', 12, 4**10)
representatives = unpack('representatives', 20, 3741)
destinations = unpack('destinations', 12, 3741 * 4)
kinds = unpack('edgeKinds', 2, 3741 * 4)
raw_offsets = dict(offsets(expression('rawClass')))
assert len(raw_offsets) == 768
ordered_offsets = sorted((offset, name) for name, offset in raw_offsets.items())
assert ordered_offsets[0][0] == 0
for (offset, name), (following, _) in zip(ordered_offsets, ordered_offsets[1:]):
    assert literals[name].bit_length() <= following - offset, name

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
counts = [0] * 11
raw_codes = set()
failures = Counter()
examples = {}


def check(condition, label, example):
    if not condition:
        failures[label] += 1
        examples.setdefault(label, example)


def generate(word=(), vertices=((0, 0),), bonds=frozenset(), code=0):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        raw_codes.add(code)
        a = raw[code]
        check(a < 3741, 'valid_window_class_out_of_range', code)
        if a >= 3741:
            return
        revisited = vertices[-1] in vertices[:-1]
        for d, (dx, dy) in enumerate(steps):
            x, y = vertices[-1]
            target = (x + dx, y + dy)
            allowed = d != (word[-1] + 2) % 4 and frozenset((vertices[-1], target)) not in bonds
            index = a * 4 + d
            check((destinations[index] != 0) == allowed, 'allowed_mismatch', [code, a, d])
            if allowed:
                kind = 2 if revisited else (0 if d == word[-1] else 1)
                check(kinds[index] == kind, 'kind_mismatch', [code, a, d])
                successor = (code % 4**9) * 4 + d
                check(destinations[index] - 1 == raw[successor], 'successor_mismatch', [code, a, d])
                if kind != 2:
                    check(representatives[a] % 4 == word[-1], 'arrival_mismatch', [code, a, d])
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        target = (x + dx, y + dy)
        bond = frozenset((vertices[-1], target))
        if bond not in bonds:
            generate(word + (d,), vertices + (target,), bonds | {bond}, 4 * code + d)


generate()
for code, a in enumerate(raw):
    check(a <= 3741 and ((a < 3741) == (code in raw_codes)), 'coverage_mismatch', [code, a])
for a, code in enumerate(representatives):
    check(code < 4**10 and code in raw_codes and raw[code] == a, 'representative_mismatch', [a, code])
for i, destination in enumerate(destinations):
    check(destination <= 3741 and ((destination == 0) == (kinds[i] == 3)), 'edge_encoding_mismatch', i)

assigned = []
all_sentinels = 3741 * ((1 << (12 * 4**10)) - 1) // ((1 << 12) - 1)
for i in range(130, 135):
    name = f'rawClass_{i}'
    low = raw_offsets[name]
    high = low + 16384 - 1
    first, last = low // 12, high // 12
    assert first // 4**8 == last // 4**8 == 13  # base-four prefix 31 = S,N
    assert literals[name] == ((all_sentinels >> low) & ((1 << 16384) - 1))
    assigned.append({
        'name': name,
        'line': next(j for j, line in enumerate(source.splitlines(), 1)
                     if line.startswith('private noncomputable def ' + name + ' ')),
        'global_bit_interval_inclusive': [low, high],
        'affected_code_interval_inclusive': [first, last],
        'affected_lanes': last - first + 1,
        'lane_values': dict(Counter(raw[first:last + 1])),
        'generated_raw_codes_in_interval': sum(code in raw_codes for code in range(first, last + 1)),
        'common_initial_directions': ['S', 'N'],
        'literal_equals_corresponding_sentinel_bits': True,
        'literal_sha256_hex': hashlib.sha256(format(literals[name], 'x').encode()).hexdigest(),
    })

result = {
    'generated_counts_depth_0_to_10': counts,
    'raw_code_count': len(raw_codes),
    'class_count': len(set(raw[code] for code in raw_codes)),
    'admitted_edges_by_kind': dict(Counter(kinds[i] for i, d in enumerate(destinations) if d)),
    'failures': dict(failures),
    'first_failure_examples': examples,
    'assigned': assigned,
}
print(json.dumps(result, indent=2))
assert not failures
