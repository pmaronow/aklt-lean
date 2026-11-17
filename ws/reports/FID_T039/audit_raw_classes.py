"""Read-only reconstruction of the reviewed Lean table and its raw trail contract."""
from pathlib import Path
from collections import Counter
import ast
import json
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
TEXT = SOURCE.read_text()
LITERALS = {
    name: int(value, 16)
    for name, value in re.findall(
        r'^private noncomputable def (\w+) : ℕ := (0x[0-9a-f]+)$', TEXT, re.M
    )
}


def unpack_expression(name):
    expression = re.search(
        r'^noncomputable def ' + name + r' : ℕ := (.+)$', TEXT, re.M
    ).group(1)
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

    def evaluate(node):
        if isinstance(node, ast.Name):
            return LITERALS[node.id]
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.BinOp):
            left, right = evaluate(node.left), evaluate(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.LShift):
                return left << right
        raise ValueError(ast.dump(node))

    offsets = {}

    def locate(node, offset=0):
        if isinstance(node, ast.Name):
            offsets[node.id] = offset
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            locate(node.left, offset)
            locate(node.right, offset)
        elif isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            locate(node.left, offset + evaluate(node.right))
        else:
            raise ValueError(ast.dump(node))

    locate(tree)
    return evaluate(tree), offsets


def lanes(packed, width, count):
    # Hex slicing avoids repeatedly copying a twelve-million-bit integer.
    if width % 4 == 0:
        digits = width // 4
        encoded = format(packed, 'x').zfill(digits * count)
        assert len(encoded) == digits * count
        return [int(encoded[i:i + digits], 16)
                for i in range(0, len(encoded), digits)][::-1]
    return [(packed >> (width * i)) & ((1 << width) - 1) for i in range(count)]


RAW_PACKED, RAW_OFFSETS = unpack_expression('rawClass')
REP_PACKED, _ = unpack_expression('representatives')
DEST_PACKED, _ = unpack_expression('destinations')
KIND_PACKED, _ = unpack_expression('edgeKinds')
RAW = lanes(RAW_PACKED, 12, 4**10)
REPS = lanes(REP_PACKED, 20, 3741)
DEST = lanes(DEST_PACKED, 12, 3741 * 4)
KIND = lanes(KIND_PACKED, 2, 3741 * 4)
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def word(code):
    return tuple((code >> (2 * (9 - i))) & 3 for i in range(10))


def raw_geometry(code):
    vertices = [(0, 0)]
    bonds = set()
    for d in word(code):
        x, y = vertices[-1]
        dx, dy = STEPS[d]
        end = (x + dx, y + dy)
        edge = tuple(sorted((vertices[-1], end)))
        if edge in bonds:
            return None
        bonds.add(edge)
        vertices.append(end)
    return vertices, bonds


COUNTS = Counter()
VALID = {}


def generate(code=0, depth=0, endpoint=(0, 0), vertices=((0, 0),), bonds=frozenset()):
    COUNTS[depth] += 1
    if depth == 10:
        VALID[code] = (vertices, bonds)
        return
    for d, (dx, dy) in enumerate(STEPS):
        new = (endpoint[0] + dx, endpoint[1] + dy)
        edge = tuple(sorted((endpoint, new)))
        if edge not in bonds:
            generate(4 * code + d, depth + 1, new,
                     vertices + (new,), bonds | {edge})


generate()
FAILURES = Counter()
EXAMPLES = {}


def check(condition, key, example):
    if not condition:
        FAILURES[key] += 1
        EXAMPLES.setdefault(key, example)


for code, value in enumerate(RAW):
    check(value <= 3741, 'raw_range', [code, value])
    check((value < 3741) == (code in VALID), 'raw_coverage', [code, value, code in VALID])

for a, code in enumerate(REPS):
    check(code < 4**10, 'representative_range', [a, code])
    check(code in VALID, 'representative_raw', [a, code])
    check(RAW[code] == a, 'representative_project', [a, code, RAW[code]])

for a in range(3741):
    for d in range(4):
        idx = 4 * a + d
        check(DEST[idx] <= 3741, 'destination_range', [a, d, DEST[idx]])
        check((DEST[idx] == 0) == (KIND[idx] == 3), 'edge_sentinel', [a, d])

for code, (vertices, bonds) in VALID.items():
    a = RAW[code] % 3741
    end = vertices[-1]
    arrival = code % 4
    revisit = end in vertices[:-1]
    for d, (dx, dy) in enumerate(STEPS):
        new = (end[0] + dx, end[1] + dy)
        edge = tuple(sorted((end, new)))
        allowed = d != ((arrival + 2) % 4) and edge not in bonds
        idx = a * 4 + d
        check((DEST[idx] != 0) == allowed, 'allowed', [code, a, d, allowed, DEST[idx]])
        if allowed:
            kind = 2 if revisit else (0 if d == arrival else 1)
            check(KIND[idx] == kind, 'kind', [code, a, d, kind, KIND[idx]])
            successor = ((code % (4**9)) * 4) + d
            check((DEST[idx] - 1) % 3741 == RAW[successor] % 3741,
                  'successor', [code, a, d, successor, RAW[successor], DEST[idx]])
            if kind != 2:
                check(REPS[a] % 4 == arrival, 'arrival', [code, a, arrival, REPS[a] % 4])

TARGETS = []
for i in range(160, 165):
    name = f'rawClass_{i}'
    offset = RAW_OFFSETS[name]
    width = 16384
    first, last = offset // 12, (offset + width - 1) // 12
    codes = list(range(first, last + 1))
    valid_codes = [c for c in codes if c in VALID]
    alignment = offset % 12
    sentinel_lanes = (alignment + width + 11) // 12
    sentinel_slice = ((3741 * ((2**(12 * sentinel_lanes) - 1) // (2**12 - 1)))
                      >> alignment) & (2**width - 1)
    targets = {
        'name': name,
        'bit_offset': offset,
        'width': width,
        'code_interval': [first, last],
        'boundary_offsets_mod_12': [offset % 12, (offset + width) % 12],
        'exact_sentinel_slice': LITERALS[name] == sentinel_slice,
        'common_direction_prefixes': sorted({
            ''.join('ENWS'[d] for d in word(c)[:3]) for c in codes
        }),
        'valid_words': len(valid_codes),
        'invalid_words': len(codes) - len(valid_codes),
        'values': dict(Counter(RAW[c] for c in codes)),
        'coverage_failures': [[c, RAW[c], c in VALID] for c in codes
                              if (RAW[c] < 3741) != (c in VALID)],
        'valid_examples': [[c, ''.join('ENWS'[d] for d in word(c)), RAW[c]]
                           for c in valid_codes[:5]],
        'local_representative_failures': [[a, c, RAW[c]] for a, c in enumerate(REPS)
                                          if c in codes and RAW[c] != a],
    }
    TARGETS.append(targets)

result = {
    'raw_bit_length': RAW_PACKED.bit_length(),
    'expected_raw_bits': 12 * 4**10,
    'generated_counts': dict(sorted(COUNTS.items())),
    'failures': dict(FAILURES),
    'first_failure_examples': EXAMPLES,
    'edge_kind_counts': dict(Counter(k for d, k in zip(DEST, KIND) if d != 0)),
    'targets': TARGETS,
}
Path('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
