"""Read-only audit of the supplied Lean literals against the paper's trail rules."""
from collections import Counter
from pathlib import Path
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {
    m[1]: int(m[2], 16)
    for m in re.finditer(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', text)
}


def parse_table(name):
    """Parse the exact parenthesized addition/left-shift expression, tracking offsets."""
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', text, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expr)
    assert ''.join(tokens) == re.sub(r'\s+', '', expr)
    pos = 0

    def atom():
        nonlocal pos
        t = tokens[pos]
        pos += 1
        if t == '(':
            val, refs = addition()
            assert tokens[pos] == ')'
            pos += 1
            return val, refs
        if t.isdigit():
            return int(t), {}
        return literals[t], {t: 0}

    def shift():
        nonlocal pos
        val, refs = atom()
        while pos < len(tokens) and tokens[pos] == '<<<':
            pos += 1
            amount, empty = atom()
            assert not empty
            val <<= amount
            refs = {k: v + amount for k, v in refs.items()}
        return val, refs

    def addition():
        nonlocal pos
        val, refs = shift()
        while pos < len(tokens) and tokens[pos] == '+':
            pos += 1
            other, more = shift()
            assert not (refs.keys() & more.keys())
            assert val & other == 0, 'Overlapping nonzero bits in concatenation'
            val += other
            refs.update(more)
        return val, refs

    val, refs = addition()
    assert pos == len(tokens)
    ordered = sorted((offset, literals[k].bit_length(), k) for k, offset in refs.items())
    for (lo, bits, _), (next_lo, _, _) in zip(ordered, ordered[1:]):
        assert lo + bits <= next_lo, 'Literal exceeds its slot'
    return val, refs


tables = {name: parse_table(name) for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds')}
raw = tables['rawClass'][0].to_bytes(12 * 4**10 // 8, 'little')


def project(code):
    # Twelve bits per code; each consecutive pair takes exactly three bytes.
    byte = code * 12 // 8
    return ((raw[byte] | raw[byte + 1] << 8) >> (4 * (code % 2))) & 4095


def lane(table, width, index):
    return (tables[table][0] >> (width * index)) & ((1 << width) - 1)


def decode(code):
    return tuple((code >> (2 * (9 - j))) & 3 for j in range(10))


STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def walk(word):
    position = (0, 0)
    vertices = []
    bonds = set()
    distinct = True
    for direction in word:
        vertices.append(position)
        dx, dy = STEPS[direction]
        nxt = (position[0] + dx, position[1] + dy)
        bond = tuple(sorted((position, nxt)))
        distinct &= bond not in bonds
        bonds.add(bond)
        position = nxt
    return distinct, position, vertices, bonds


def transition(word, direction, info):
    distinct, endpoint, departures, bonds = info
    assert distinct
    dx, dy = STEPS[direction]
    nxt = (endpoint[0] + dx, endpoint[1] + dy)
    allowed = direction != (word[-1] + 2) % 4 and tuple(sorted((endpoint, nxt))) not in bonds
    kind = 2 if endpoint in departures else (0 if direction == word[-1] else 1)
    return allowed, kind


def generate():
    """Lexicographic recursion adding precisely the currently unused bonds."""
    counts = Counter()
    valid = set()

    def visit(code, depth, endpoint, bonds):
        counts[depth] += 1
        if depth == 10:
            valid.add(code)
            return
        for direction, (dx, dy) in enumerate(STEPS):
            nxt = (endpoint[0] + dx, endpoint[1] + dy)
            bond = tuple(sorted((endpoint, nxt)))
            if bond not in bonds:
                visit(code * 4 + direction, depth + 1, nxt, bonds | {bond})

    visit(0, 0, (0, 0), set())
    return valid, [counts[j] for j in range(11)]


valid, counts = generate()
assert counts == [1, 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
coverage_errors = [code for code in range(4**10) if
                   project(code) > 3741 or ((project(code) < 3741) != (code in valid))]
assert not coverage_errors, coverage_errors[:10]
representatives = [lane('representatives', 20, a) for a in range(3741)]
assert all(code < 4**10 and code in valid and project(code) == a
           for a, code in enumerate(representatives))
stored = [[(lane('destinations', 12, a * 4 + d), lane('edgeKinds', 2, a * 4 + d))
           for d in range(4)] for a in range(3741)]
assert all(0 <= dest <= 3741 and ((dest == 0) == (kind == 3)) and
           (dest == 0 or kind < 3) for row in stored for dest, kind in row)

target_ranges = {}
for n in range(490, 495):
    key = f'rawClass_{n}'
    offset = tables['rawClass'][1][key]
    next_offset = tables['rawClass'][1][f'rawClass_{n-1}']
    assert next_offset - offset == 16384
    codes = range(offset // 12, (next_offset - 1) // 12 + 1)
    valid_here = [c for c in codes if c in valid]
    target_ranges[n] = {
        'source_line': next(i for i, line in enumerate(text.splitlines(), 1)
                            if line.startswith(f'private noncomputable def {key} :')),
        'bit_offset': offset,
        'bit_end_exclusive': next_offset,
        'codes_inclusive': [codes.start, codes.stop - 1],
        'lane_start_bit': offset % 12,
        'lane_end_bit_exclusive': next_offset % 12,
        'touched_lanes': len(codes),
        'valid_lanes': len(valid_here),
        'invalid_lanes': len(codes) - len(valid_here),
        'classes': len({project(c) for c in valid_here}),
        'coverage_errors': 0,
    }

errors = []
for code in sorted(valid):
    word = decode(code)
    info = walk(word)
    a = project(code)
    representative = decode(representatives[a])
    rep_info = walk(representative)
    for d in range(4):
        allowed, kind = transition(word, d, info)
        rep_allowed, rep_kind = transition(representative, d, rep_info)
        dest, stored_kind = stored[a][d]
        if allowed != (dest != 0) or allowed != rep_allowed:
            errors.append((code, d, 'admissibility'))
        # The paper's lemma also requires equality of kind on forbidden directions.
        if kind != rep_kind:
            errors.append((code, d, 'kind between raw members'))
        if allowed:
            successor_code = (code % 4**9) * 4 + d
            if stored_kind != kind or dest - 1 != project(successor_code):
                errors.append((code, d, 'kind or successor'))
            if kind != 2 and word[-1] != representative[-1]:
                errors.append((code, d, 'arrival'))
assert not errors, errors[:10]
edge_counts = Counter(kind for row in stored for dest, kind in row if dest != 0)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

result = {
    'scope': 'Independent exact-integer reconstruction, not a Lean proof; inputs read only.',
    'raw_window_counts_by_length': counts,
    'class_map_coverage_errors_all_1048576_codes': len(coverage_errors),
    'quotient_regeneration_errors_all_60092_raw_words': len(errors),
    'surjective_classes': len(representatives),
    'labelled_edge_counts': dict(edge_counts),
    'target_chunks': target_ranges,
}
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
