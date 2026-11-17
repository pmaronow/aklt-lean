"""Independent finite checks using only the supplied Lean literals and paper rules."""
from pathlib import Path
from array import array
from collections import Counter
import json
import re

ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = (ROOT / 'AKLT/Defs/Automaton10Data.lean').read_text()
LITERALS = {
    name: digits for name, digits in re.findall(
        r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', SOURCE)
}


def assembled(name):
    """Parse the actual Lean expression; retain each literal's bit offset."""
    expr = re.search(r'^noncomputable def ' + name + r' : ℕ := (.*)$', SOURCE, re.M)[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expr)
    assert ''.join(tokens) == ''.join(expr.split())
    pos = 0

    def parse(min_precedence=0):
        nonlocal pos
        t = tokens[pos]
        pos += 1
        if t == '(':
            result = parse()
            assert tokens[pos] == ')'
            pos += 1
        elif t.isdigit():
            result = (int(t), {})
        else:
            result = (int(LITERALS[t], 16), {t: 0})
        # Every addition and shifted left operand is explicitly parenthesized.
        while pos < len(tokens) and tokens[pos] in ('+', '<<<'):
            op = tokens[pos]
            precedence = {'+': 65, '<<<': 75}[op]
            if precedence < min_precedence:
                break
            pos += 1
            rhs = parse(precedence + 1)
            value, offsets = result
            if op == '+':
                assert not offsets.keys() & rhs[1].keys()
                result = (value + rhs[0], offsets | rhs[1])
            else:
                assert not rhs[1]
                result = (value << rhs[0], {k: v + rhs[0] for k, v in offsets.items()})
        return result

    value, offsets = parse()
    assert pos == len(tokens)
    keys = sorted(offsets, key=lambda k: int(k.rsplit('_', 1)[1]))
    joined = ''.join(LITERALS[k] for k in keys)
    assert value == int(joined, 16), name
    end = 0
    for k in reversed(keys):
        assert offsets[k] == end, (name, k, offsets[k], end)
        end += 4 * len(LITERALS[k])
    return value, offsets


raw_packed, raw_offsets = assembled('rawClass')
rep_packed, _ = assembled('representatives')
dst_packed, _ = assembled('destinations')
kind_packed, _ = assembled('edgeKinds')


def lanes(value, width, count):
    digits = f'{value:0{(width * count + 3) // 4}x}'
    # All widths used here divide four or are multiples of four.
    if width % 4 == 0:
        step = width // 4
        return [int(digits[len(digits)-step*(i+1):len(digits)-step*i], 16)
                for i in range(count)]
    return [(value >> (width * i)) & ((1 << width) - 1) for i in range(count)]


raw = array('H', lanes(raw_packed, 12, 4**10))
representatives = lanes(rep_packed, 20, 3741)
destinations = lanes(dst_packed, 12, 3741 * 4)
kinds = lanes(kind_packed, 2, 3741 * 4)
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))
valid = {}
depth_counts = [0] * 11


def generate(code=0, directions=(), vertices=((0, 0),), bonds=frozenset()):
    depth = len(directions)
    depth_counts[depth] += 1
    if depth == 10:
        valid[code] = directions
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(STEPS):
        new = (x + dx, y + dy)
        bond = frozenset(((x, y), new))
        if bond not in bonds:
            generate(code * 4 + d, directions + (d,), vertices + (new,), bonds | {bond})


generate()
assert depth_counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((a < 3741) == (code in valid) and a <= 3741 for code, a in enumerate(raw))
assert all(c < 4**10 and c in valid and raw[c] == a for a, c in enumerate(representatives))
assert set(raw[c] for c in valid) == set(range(3741))
assert all(dst <= 3741 and ((dst == 0) == (k == 3))
           and (dst == 0 or k < 3) for dst, k in zip(destinations, kinds))


def geometry(directions):
    vertices = [(0, 0)]
    for d in directions:
        dx, dy = STEPS[d]
        x, y = vertices[-1]
        vertices.append((x + dx, y + dy))
    return vertices, {frozenset((u, v)) for u, v in zip(vertices, vertices[1:])}


representative_geometry = [geometry(valid[c]) for c in representatives]
for code, directions in valid.items():
    a = raw[code]
    vertices, bonds = geometry(directions)
    x, y = vertices[-1]
    revisit = (x, y) in vertices[:-1]
    rep_directions = valid[representatives[a]]
    rep_vertices, _ = representative_geometry[a]
    rep_revisit = rep_vertices[-1] in rep_vertices[:-1]
    for d, (dx, dy) in enumerate(STEPS):
        kind = 2 if revisit else (0 if d == directions[-1] else 1)
        rep_kind = 2 if rep_revisit else (0 if d == rep_directions[-1] else 1)
        # The paper's projection hypothesis compares kinds even for forbidden d.
        assert kind == rep_kind, (code, a, d, 'representative kind')
        admitted = (d != (directions[-1] + 2) % 4
                    and frozenset(((x, y), (x + dx, y + dy))) not in bonds)
        index = a * 4 + d
        assert (destinations[index] != 0) == admitted, (code, a, d, 'admissibility')
        if admitted:
            successor = (code % (4**9)) * 4 + d
            assert successor in valid
            assert kinds[index] == kind, (code, a, d, 'kind')
            assert destinations[index] - 1 == raw[successor], (code, a, d, 'successor')
            if kind != 2:
                assert representatives[a] % 4 == directions[-1], (code, a, d, 'arrival')

edge_counts = Counter(k for dst, k in zip(destinations, kinds) if dst)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

chunks = []
for i in range(615, 620):
    key = f'rawClass_{i}'
    offset = raw_offsets[key]
    width = len(LITERALS[key]) * 4
    first, last = offset // 12, (offset + width - 1) // 12
    good = [c for c in range(first, last + 1) if c in valid]
    # Independently reconstruct the chunk from all complete/partial lanes.
    expected = sum((raw[c] if c in valid else 3741) << (12 * (c-first))
                   for c in range(first, last + 1))
    expected = (expected >> (offset - 12 * first)) & ((1 << width) - 1)
    assert expected == int(LITERALS[key], 16)
    chunks.append({
        'declaration': key, 'bit_offset': offset, 'bit_width': width,
        'codes_intersected': [first, last], 'number_of_codes': last-first+1,
        'valid_codes': len(good), 'invalid_codes': last-first+1-len(good),
        'classes_of_valid_codes': sorted({raw[c] for c in good}),
        'valid_examples': [{'code': c, 'directions': ''.join('ENWS'[d] for d in valid[c]),
                            'class': raw[c]} for c in good[:8]],
    })

print(json.dumps({
    'generation_counts': depth_counts[1:], 'coverage': 'all 4^10 codes pass',
    'representatives': 'all 3741 pass',
    'raw_transition_checks': 'all 60092 words and four absolute directions pass',
    'edge_counts': dict(edge_counts), 'chunks': chunks,
}, indent=2))
