"""Read-only reconstruction of the Lean literal data and the paper's raw model."""
from pathlib import Path
from collections import Counter
import ast
import hashlib
import json
import re

INPUT = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
source = INPUT.read_text()
declarations = {}
positions = {}
for line_number, line in enumerate(source.splitlines(), 1):
    match = re.fullmatch(r'(?:private )?noncomputable def (\w+) : ℕ := (.+)', line)
    if match:
        name, expression = match.groups()
        # All inputs are literal integers or sums of explicitly bracketed shifts.
        tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body
        declarations[name] = tree
        positions[name] = line_number

def evaluate(tree, offset=0):
    if isinstance(tree, ast.Constant):
        return tree.value, []
    if isinstance(tree, ast.Name):
        value, _ = evaluate(declarations[tree.id])
        return value, [(tree.id, offset)]
    if isinstance(tree, ast.BinOp) and isinstance(tree.op, ast.LShift):
        assert isinstance(tree.right, ast.Constant)
        shift = tree.right.value
        value, leaves = evaluate(tree.left, offset + shift)
        return value << shift, leaves
    if isinstance(tree, ast.BinOp) and isinstance(tree.op, ast.Add):
        left, left_leaves = evaluate(tree.left, offset)
        right, right_leaves = evaluate(tree.right, offset)
        assert left & right == 0, 'Concatenation overlaps nonzero bits'
        return left + right, left_leaves + right_leaves
    raise ValueError(ast.dump(tree))

tables, offsets = {}, {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    value, leaves = evaluate(declarations[name])
    tables[name] = value.to_bytes((value.bit_length() + 7) // 8, 'little')
    offsets.update(leaves)
    print('TABLE', name, 'bits', value.bit_length(), 'pieces', len(leaves),
          'sha256', hashlib.sha256(tables[name]).hexdigest())

def lane(table, width, index):
    start = width * index
    byte, bit = divmod(start, 8)
    size = (bit + width + 7) // 8
    return (int.from_bytes(tables[table][byte:byte + size], 'little') >> bit) & ((1 << width) - 1)

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw = {}
counts = Counter()

def generate(depth, code, endpoint, used):
    counts[depth] += 1
    if depth == 10:
        raw[code] = lane('rawClass', 12, code)
        return
    x, y = endpoint
    for d, (dx, dy) in enumerate(steps):
        target = (x + dx, y + dy)
        bond = tuple(sorted((endpoint, target)))
        if bond not in used:
            used.add(bond)
            generate(depth + 1, code * 4 + d, target, used)
            used.remove(bond)

generate(0, 0, (0, 0), set())
print('RAW_COUNTS', [counts[j] for j in range(1, 11)])

def model(code):
    directions = tuple((code >> (2 * (9 - i))) & 3 for i in range(10))
    endpoint = (0, 0)
    departures = set()
    used = set()
    for d in directions:
        departures.add(endpoint)
        dx, dy = steps[d]
        target = (endpoint[0] + dx, endpoint[1] + dy)
        used.add(tuple(sorted((endpoint, target))))
        endpoint = target
    arrival = directions[-1]
    revisit = endpoint in departures
    edges = []
    for d, (dx, dy) in enumerate(steps):
        target = (endpoint[0] + dx, endpoint[1] + dy)
        allowed = d != (arrival + 2) % 4 and tuple(sorted((endpoint, target))) not in used
        kind = 2 if revisit else (0 if d == arrival else 1)
        successor_code = (code % (4 ** 9)) * 4 + d
        edges.append((allowed, kind, successor_code))
    return arrival, edges

errors = Counter()
examples = {}

def check(condition, category, context):
    if not condition:
        errors[category] += 1
        examples.setdefault(category, context)

classes = Counter(raw.values())
for code in range(4 ** 10):
    value = lane('rawClass', 12, code)
    check(value <= 3741, 'lane_bound', (code, value))
    check((value < 3741) == (code in raw), 'raw_coverage', (code, value))

representatives = [lane('representatives', 20, a) for a in range(3741)]
representative_models = [model(code) for code in representatives]
for a, code in enumerate(representatives):
    check(code < 4 ** 10, 'representative_bound', (a, code))
    check(code in raw, 'representative_raw', (a, code))
    check(raw.get(code) == a, 'representative_maps_back', (a, code, raw.get(code)))

edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        dest = lane('destinations', 12, 4 * a + d)
        kind = lane('edgeKinds', 2, 4 * a + d)
        check(dest <= 3741, 'destination_bound', (a, d, dest))
        check((dest == 0) == (kind == 3), 'destination_kind_sentinel', (a, d, dest, kind))
        if dest:
            edge_counts[kind] += 1

for code, a in raw.items():
    if a >= 3741:
        check(False, 'raw_class_bound', (code, a))
        continue
    arrival, edges = model(code)
    rep_arrival, rep_edges = representative_models[a]
    for d, (allowed, kind, successor) in enumerate(edges):
        dest = lane('destinations', 12, 4 * a + d)
        stored_kind = lane('edgeKinds', 2, 4 * a + d)
        rep_allowed, rep_kind, _ = rep_edges[d]
        check(allowed == bool(dest), 'allowed', (code, a, d))
        check(allowed == rep_allowed, 'representative_allowed', (code, a, d))
        # The paper's reconstruction compares kind with the representative
        # in each direction, even where the stored row uses an invalid sentinel.
        check(kind == rep_kind, 'representative_kind', (code, a, d, kind, rep_kind))
        if allowed:
            check(kind == stored_kind, 'kind', (code, a, d, kind, stored_kind))
            check(successor in raw, 'successor_raw', (code, a, d, successor))
            check(raw.get(successor) == dest - 1, 'successor_class',
                  (code, a, d, successor, raw.get(successor), dest - 1))
            if kind != 2:
                check(arrival == rep_arrival, 'nonrevisit_arrival', (code, a, d))

print('CLASS_COUNT', len(classes), 'EDGE_COUNTS', dict(edge_counts))
print('ERRORS', dict(errors), 'EXAMPLES', examples)

# Recover the text format described at paper app-input-contracts.tex:382-388.
# The packed successor is the original successor plus one; kind 3 stores -1.
archive_lines = ['60092 3741']
archive_lines += [f'{code} {a}' for code, a in raw.items()]
for a, rep in enumerate(representatives):
    destinations = [lane('destinations', 12, 4 * a + d) - 1 for d in range(4)]
    kinds = [lane('edgeKinds', 2, 4 * a + d) for d in range(4)]
    archive_lines.append(' '.join(map(str, [rep] + destinations +
                                      [-1 if k == 3 else k for k in kinds])))
archive_digest = hashlib.sha256(('\n'.join(archive_lines) + '\n').encode()).hexdigest()
documented_digest = re.search(r'Archive SHA-256: ([0-9a-f]{64})', source)[1]
print('RECONSTRUCTED_ARCHIVE_SHA256', archive_digest,
      'MATCHES_SOURCE_DOCUMENTATION', archive_digest == documented_digest)

target_summary = []
for n in range(510, 515):
    name = f'rawClass_{n}'
    value, _ = evaluate(declarations[name])
    offset = offsets[name]
    width = 16384
    lo, hi = offset // 12, (offset + width - 1) // 12
    valid_codes = [code for code in range(lo, hi + 1) if code in raw]
    record = dict(name=name, line=positions[name], offset=offset,
                  last_bit=offset + width - 1, first_code=lo, last_code=hi,
                  first_lane_bits=12 - offset % 12,
                  last_lane_bits=(offset + width - 1) % 12 + 1,
                  raw_words=len(valid_codes), invalid_words=hi - lo + 1 - len(valid_codes),
                  represented_classes=len({raw[c] for c in valid_codes}),
                  sample=[(c, raw[c], ''.join('ENWS'[(c >> (2 * (9 - i))) & 3]
                                             for i in range(10))) for c in valid_codes[:3]],
                  hex_digits=len(re.search(rf'def {name} : ℕ := 0x([0-9a-f]+)', source)[1]))
    # Re-extract the full assigned bit interval; this includes partial lanes.
    packed = int.from_bytes(tables['rawClass'], 'little')
    check(((packed >> offset) & ((1 << width) - 1)) == value,
          'target_piece_roundtrip', name)
    target_summary.append(record)
    print('TARGET', json.dumps(record))

result = dict(raw_counts=[counts[j] for j in range(1, 11)],
              class_count=len(classes), edge_counts=dict(edge_counts),
              errors=dict(errors), examples=examples, targets=target_summary,
              archive_digest=archive_digest,
              archive_digest_matches_documentation=archive_digest == documented_digest)
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
assert not errors, errors
