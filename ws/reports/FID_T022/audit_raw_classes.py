"""Read-only reconstruction of Automaton10Data and the paper's finite checks.

Uses only the supplied Lean literals as data; raw windows and transitions are
regenerated from app-input-contracts.tex, d:memory-automaton/p:automaton10.
"""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re


ROOT = Path('/home/ubuntu/aklt/review/FID_T/lean')
SOURCE = ROOT / 'AKLT/Defs/Automaton10Data.lean'
TEXT = SOURCE.read_text()
LITERALS = {
    name: int(digits, 16)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', TEXT, re.M
    )
}
WIDTHS = {
    name: 4 * len(digits)
    for name, digits in re.findall(
        r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', TEXT, re.M
    )
}


def parse_packed(name):
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', TEXT, re.M
    )[1]
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert ''.join(tokens) == ''.join(expression.split())
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == '(':
            result = expr()
            assert tokens[pos] == ')'
            pos += 1
            return result
        if token.isdecimal():
            return int(token), {}
        assert token in LITERALS
        return LITERALS[token], {token: 0}

    def expr():
        nonlocal pos
        result, offsets = atom()
        operators = 0
        while pos < len(tokens) and tokens[pos] != ')':
            operators += 1
            op = tokens[pos]
            pos += 1
            value, more = atom()
            if op == '<<<':
                assert not more
                result <<= value
                offsets = {key: offset + value for key, offset in offsets.items()}
            else:
                assert op == '+'
                assert not offsets.keys() & more.keys()
                result += value
                offsets |= more
        # Every infix application is explicitly parenthesized in the source,
        # so this parser does not substitute Python's operator precedence.
        assert operators <= 1
        return result, offsets

    packed, offsets = expr()
    assert pos == len(tokens)
    intervals = sorted((offset, offset + WIDTHS[key], key) for key, offset in offsets.items())
    assert intervals[0][0] == 0
    assert all(left[1] == right[0] for left, right in zip(intervals, intervals[1:]))
    assert packed == sum(LITERALS[key] << offset for key, offset in offsets.items())
    return packed, offsets, intervals[-1][1]


def unpack(packed, width, count):
    assert packed.bit_length() <= width * count
    if width % 4 == 0:
        digits = width // 4
        h = format(packed, f'0{digits * count}x')
        return [int(h[i:i + digits], 16) for i in range(len(h) - digits, -1, -digits)]
    assert width == 2
    b = packed.to_bytes((width * count + 7) // 8, 'little')
    return [(b[i // 4] >> (2 * (i % 4))) & 3 for i in range(count)]


TABLES = {}
OFFSETS = {}
for table, width, count in [
    ('rawClass', 12, 4**10),
    ('representatives', 20, 3741),
    ('destinations', 12, 4 * 3741),
    ('edgeKinds', 2, 4 * 3741),
]:
    packed, offsets, storage_width = parse_packed(table)
    TABLES[table] = unpack(packed, width, count)
    OFFSETS[table] = offsets
    print(table, 'literal pieces', len(offsets), 'storage bits', storage_width,
          'nominal bits', width * count, 'value bits', packed.bit_length(), flush=True)

classes = TABLES['rawClass']
representatives = TABLES['representatives']
destinations = TABLES['destinations']
kinds = TABLES['edgeKinds']
STEPS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def bond(p, q):
    return (p, q) if p < q else (q, p)


def decode(code):
    return tuple((code >> (2 * i)) & 3 for i in range(9, -1, -1))


def describe(word):
    p = (0, 0)
    vertices = [p]
    used = set()
    for d in word:
        dx, dy = STEPS[d]
        q = (p[0] + dx, p[1] + dy)
        e = bond(p, q)
        assert e not in used
        used.add(e)
        vertices.append(q)
        p = q
    return vertices, used


def row(code):
    word = decode(code)
    vertices, used = describe(word)
    p = vertices[-1]
    revisit = p in vertices[:-1]
    result = []
    for d, (dx, dy) in enumerate(STEPS):
        q = (p[0] + dx, p[1] + dy)
        allowed = d != (word[-1] + 2) % 4 and bond(p, q) not in used
        kind = 2 if revisit else (0 if d == word[-1] else 1)
        successor_code = (code % (4**9)) * 4 + d
        result.append((allowed, kind, classes[successor_code], successor_code))
    return word[-1], result


# The paper's generation recursion, independent of the class table.
raw_codes = []
counts = [0] * 11


def generate(depth, p, used, code):
    counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        return
    for d, (dx, dy) in enumerate(STEPS):
        q = (p[0] + dx, p[1] + dy)
        e = bond(p, q)
        if e not in used:
            used.add(e)
            generate(depth + 1, q, used, code * 4 + d)
            used.remove(e)


generate(0, (0, 0), set(), 0)
print('raw window counts', counts[1:], flush=True)
raw_set = set(raw_codes)
coverage_errors = [
    (code, value, code in raw_set)
    for code, value in enumerate(classes)
    if value > 3741 or ((value < 3741) != (code in raw_set))
]
print('coverage errors', len(coverage_errors), coverage_errors[:5], flush=True)
assert not coverage_errors
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]

# Regenerate class representatives and compare all admitted stored transitions.
rep_rows = []
edge_counts = Counter()
for a, code in enumerate(representatives):
    assert 0 <= code < 4**10 and code in raw_set and classes[code] == a, (a, code)
    last, generated_row = row(code)
    rep_rows.append((last, generated_row))
    for d, (allowed, kind, successor, successor_code) in enumerate(generated_row):
        dest = destinations[a * 4 + d]
        stored_kind = kinds[a * 4 + d]
        assert dest <= 3741
        assert (dest == 0) == (stored_kind == 3)
        assert (dest != 0) == allowed, (a, code, d, dest, allowed)
        if allowed:
            assert stored_kind == kind, (a, code, d, stored_kind, kind)
            assert dest - 1 == successor, (a, code, d, dest - 1, successor)
            edge_counts[kind] += 1
print('representatives checked', len(rep_rows), 'edge counts', dict(edge_counts), flush=True)
assert edge_counts == {0: 2516, 1: 5032, 2: 1872}

# Check the quotient comparisons on every raw word, for all absolute directions.
transition_checks = 0
arrival_checks = 0
inadmissible_kind_differences = 0
for code in raw_codes:
    a = classes[code]
    last, generated_row = row(code)
    rep_last, rep_row = rep_rows[a]
    for d, (allowed, kind, successor, successor_code) in enumerate(generated_row):
        rep_allowed, rep_kind, rep_successor, _ = rep_row[d]
        assert allowed == rep_allowed, (code, a, d, 'admissibility')
        if allowed:
            assert kind == rep_kind, (code, a, d, 'kind')
            assert successor == rep_successor, (code, a, d, 'successor')
            if kind != 2:
                assert last == rep_last, (code, a, d, 'arrival')
                arrival_checks += 1
        elif kind != rep_kind:
            inadmissible_kind_differences += 1
        transition_checks += 1
print('raw direction comparisons', transition_checks, 'nonrevisit arrival checks',
      arrival_checks, 'inadmissible kind differences', inadmissible_kind_differences, flush=True)
assert inadmissible_kind_differences == 0

# The exact text format specified by the paper: header, code/class pairs,
# then representative, four successor labels, and four kind labels per class.
archive_lines = ['60092 3741']
archive_lines.extend(f'{code} {classes[code]}' for code in raw_codes)
for a, code in enumerate(representatives):
    dest = [destinations[a * 4 + d] - 1 for d in range(4)]
    kind = [kinds[a * 4 + d] if destinations[a * 4 + d] else -1 for d in range(4)]
    archive_lines.append(' '.join(map(str, [code] + dest + kind)))
reconstructed_sha = hashlib.sha256(('\n'.join(archive_lines) + '\n').encode()).hexdigest()
declared_sha = re.search(r'Archive SHA-256: ([0-9a-f]{64})', TEXT)[1]
print('reconstructed text SHA-256', reconstructed_sha,
      'matches declared archive hash', reconstructed_sha == declared_sha, flush=True)

summaries = []
for i in range(75, 80):
    name = f'rawClass_{i}'
    lo = OFFSETS['rawClass'][name]
    hi = lo + WIDTHS[name]
    # Include both partial boundary lanes: chunks are not divisible by 12.
    first, last = lo // 12, (hi - 1) // 12
    codes = range(first, last + 1)
    valid = [code for code in codes if code in raw_set]
    raw_directions = sum(4 for _ in valid)
    summary = dict(
        name=name,
        source_line=TEXT.count('\n', 0, TEXT.index(f'private noncomputable def {name} :')) + 1,
        hex_sha256=hashlib.sha256(format(LITERALS[name], '04096x').encode()).hexdigest(),
        bit_interval=[lo, hi],
        intersecting_code_interval=[first, last],
        low_boundary_bits=lo % 12,
        high_boundary_bits=hi % 12,
        intersecting_lanes=last - first + 1,
        raw_lanes=len(valid),
        sentinel_lanes=last - first + 1 - len(valid),
        minimum_class=min((classes[c] for c in valid), default=None),
        maximum_class=max((classes[c] for c in valid), default=None),
        raw_direction_comparisons=raw_directions,
        first_raw_codes=valid[:3],
        last_raw_codes=valid[-3:],
    )
    summaries.append(summary)
    print(json.dumps(summary), flush=True)

result = dict(
    raw_counts=counts[1:],
    coverage_errors=len(coverage_errors),
    representative_checks=len(rep_rows),
    edge_counts=dict(edge_counts),
    raw_direction_comparisons=transition_checks,
    nonrevisit_arrival_checks=arrival_checks,
    inadmissible_kind_differences=inadmissible_kind_differences,
    reconstructed_text_sha256=reconstructed_sha,
    declared_archive_sha256=declared_sha,
    reconstructed_hash_matches=reconstructed_sha == declared_sha,
    declarations=summaries,
)
Path(__file__).with_name('audit_results.json').write_text(json.dumps(result, indent=2) + '\n')
