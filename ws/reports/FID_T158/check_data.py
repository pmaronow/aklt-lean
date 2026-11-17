"""Read-only finite reconstruction of the paper's memory-ten data contract."""

import ast
import collections
import json
import re
from pathlib import Path

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = SOURCE.read_text()
literals = {
    name: int(value, 16)
    for name, value in re.findall(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-fA-F]+)', source
    )
}


def parse_packed(name):
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', source, re.M
    )[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

    def evaluate(node):
        if isinstance(node, ast.Name):
            return literals[node.id], {node.id: 0}
        assert isinstance(node, ast.BinOp)
        left, offsets = evaluate(node.left)
        if isinstance(node.op, ast.LShift):
            assert isinstance(node.right, ast.Constant)
            shift = node.right.value
            assert isinstance(shift, int) and shift >= 0
            return left << shift, {key: value + shift for key, value in offsets.items()}
        assert isinstance(node.op, ast.Add)
        right, right_offsets = evaluate(node.right)
        assert not offsets.keys() & right_offsets.keys()
        offsets.update(right_offsets)
        return left + right, offsets

    packed, offsets = evaluate(tree)
    # Check the full expression, including the chunks that meet inside a lane.
    ordered = sorted(offsets, key=offsets.get)
    assert offsets[ordered[0]] == 0
    for i, chunk in enumerate(ordered):
        upper = offsets[ordered[i + 1]] if i + 1 < len(ordered) else packed.bit_length()
        assert literals[chunk].bit_length() <= upper - offsets[chunk]
    return packed, offsets


def lanes(packed, width, count):
    # Byte extraction avoids repeatedly shifting the entire 12-million-bit table.
    data = packed.to_bytes((width * count + 7) // 8, 'little')
    mask = (1 << width) - 1
    return [
        (int.from_bytes(data[(width * i) // 8:(width * i + width + 7) // 8], 'little')
         >> ((width * i) % 8)) & mask
        for i in range(count)
    ]


raw_packed, offsets = parse_packed('rawClass')
raw = lanes(raw_packed, 12, 4**10)
reps = lanes(parse_packed('representatives')[0], 20, 3741)
dest = lanes(parse_packed('destinations')[0], 12, 3741 * 4)
kinds = lanes(parse_packed('edgeKinds')[0], 2, 3741 * 4)

STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def add(x, d):
    return x[0] + STEPS[d][0], x[1] + STEPS[d][1]


def bond(x, y):
    return tuple(sorted((x, y)))


# Independent lexicographic trail recursion from the paper: only actual used
# unoriented bonds are forbidden, with no virtual incoming bond.
levels = collections.Counter()
models = {}


def generate(code=0, word=(), vertices=((0, 0),), used=frozenset()):
    n = len(word)
    levels[n] += 1
    x = vertices[-1]
    if n == 10:
        allowed = tuple(
            d != (word[-1] + 2) % 4 and bond(x, add(x, d)) not in used
            for d in range(4)
        )
        revisit = x in vertices[:-1]
        step_kinds = tuple(2 if revisit else 0 if d == word[-1] else 1 for d in range(4))
        models[code] = allowed, step_kinds, word[-1]
        return
    for d in range(4):
        y = add(x, d)
        edge = bond(x, y)
        if edge not in used:
            generate(code * 4 + d, word + (d,), vertices + (y,), used | {edge})


generate()
assert [levels[j] for j in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert len(raw) == 4**10
assert all(0 <= a <= 3741 for a in raw)
assert all((a < 3741) == (code in models) for code, a in enumerate(raw))
assert all(code < 4**10 and code in models and raw[code] == a for a, code in enumerate(reps))
assert {raw[code] for code in models} == set(range(3741))
assert all(0 <= d <= 3741 for d in dest)
assert all((dest[i] == 0) == (kinds[i] == 3) for i in range(len(dest)))

edge_counts = collections.Counter()
for a, code in enumerate(reps):
    allowed, step_kinds, arrival = models[code]
    for d in range(4):
        index = 4 * a + d
        assert bool(dest[index]) == allowed[d]
        if allowed[d]:
            assert kinds[index] == step_kinds[d]
            assert dest[index] - 1 == raw[(code % 4**9) * 4 + d]
            edge_counts[step_kinds[d]] += 1
assert [edge_counts[k] for k in range(3)] == [2516, 5032, 1872]

for code, (allowed, step_kinds, arrival) in models.items():
    a = raw[code]
    rep_allowed, rep_kinds, rep_arrival = models[reps[a]]
    assert allowed == rep_allowed
    assert step_kinds == rep_kinds  # Even for the inadmissible directions.
    for d in range(4):
        if allowed[d]:
            assert kinds[4 * a + d] == step_kinds[d]
            assert dest[4 * a + d] - 1 == raw[(code % 4**9) * 4 + d]
            if step_kinds[d] != 2:
                assert arrival == rep_arrival

summary = {
    'raw_cardinality_by_length': {j: levels[j] for j in range(1, 11)},
    'quotient_classes': 3741,
    'labelled_edges_by_kind': dict(edge_counts),
    'raw_table_lane_count': len(raw),
    'invalid_sentinel_entries': raw.count(3741),
    'target_chunks': {},
}
for number in range(755, 760):
    name = f'rawClass_{number}'
    low_bit = offsets[name]
    high_bit = low_bit + 16384 - 1
    low_code, high_code = low_bit // 12, high_bit // 12
    codes = range(low_code, high_code + 1)
    valid = [code for code in codes if code in models]
    summary['target_chunks'][name] = {
        'source_line': next(i for i, line in enumerate(source.splitlines(), 1)
                            if line.startswith(f'private noncomputable def {name} :')),
        'bit_offset': low_bit,
        'bit_width': 16384,
        'overlapping_code_interval_inclusive': [low_code, high_code],
        'overlapping_valid_words': len(valid),
        'overlapping_invalid_words': len(codes) - len(valid),
        'classes_of_valid_words': len({raw[c] for c in valid}),
        'example_code_and_class': [valid[0], raw[valid[0]]] if valid else None,
        'all_coverage_and_quotient_comparisons_pass': True,
    }
print(json.dumps(summary, indent=2))
