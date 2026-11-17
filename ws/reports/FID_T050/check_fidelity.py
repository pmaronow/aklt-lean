"""Read-only reconstruction of the packed constants and the paper's raw windows."""

from collections import Counter
from pathlib import Path
import hashlib
import json
import re


SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M))
literals = {m[1]: int(m[2], 16) for m in literal_matches}
hexes = {m[1]: m[2] for m in literal_matches}


def parse(expression):
    tokens = re.findall(r'\w+|<<<|[()+]', expression)
    assert re.sub(r'\s+', '', expression) == ''.join(tokens)
    index = 0

    def expr(minimum=0):
        nonlocal index
        token = tokens[index]
        index += 1
        if token == '(':
            result = expr()
            assert tokens[index] == ')'
            index += 1
        elif token.isdecimal():
            result = int(token)
        else:
            assert token in literals
            result = token
        while index < len(tokens) and tokens[index] in ('+', '<<<'):
            op = tokens[index]
            priority = {'+': 65, '<<<': 75}[op]
            if priority < minimum:
                break
            index += 1
            result = (op, result, expr(priority + 1))
        return result

    result = expr()
    assert index == len(tokens)
    return result


def evaluate(node):
    if isinstance(node, str):
        return literals[node]
    if isinstance(node, int):
        return node
    op, left, right = node
    left, right = evaluate(left), evaluate(right)
    return left + right if op == '+' else left << right


def offsets(node, offset=0):
    if isinstance(node, str):
        return {node: offset}
    assert isinstance(node, tuple)
    op, left, right = node
    if op == '<<<':
        return offsets(left, offset + evaluate(right))
    result = offsets(left, offset)
    others = offsets(right, offset)
    assert result.keys().isdisjoint(others)
    return result | others


tables = {}
table_offsets = {}
for table in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    expression = re.search(r'^noncomputable def ' + table + r' : ℕ := (.+)$', text, re.M)[1]
    tree = parse(expression)
    tables[table] = evaluate(tree)
    table_offsets[table] = offsets(tree)
    ordered = sorted(table_offsets[table], key=table_offsets[table].get)
    # Check all chunk boundaries, not only the five reviewed ones.
    end = 0
    for name in ordered:
        start = table_offsets[table][name]
        assert start == end
        end = start + 4 * len(hexes[name])
        assert literals[name] < (1 << (end - start))
    assert tables[table].bit_length() <= end


def lanes(table, width, count):
    value = tables[table]
    # Convert once to bytes; shifting the full 12-million-bit integer per
    # individual lane would unnecessarily repeat a large amount of work.
    buf = value.to_bytes((width * count + 7) // 8, 'little') + bytes(3)
    mask = (1 << width) - 1
    result = []
    for i in range(count):
        bit = i * width
        byte, shift = divmod(bit, 8)
        result.append((int.from_bytes(buf[byte:byte + 3], 'little') >> shift) & mask)
    return result


raw_class = lanes('rawClass', 12, 4**10)
representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
assert tables['rawClass'].bit_length() <= 12 * 4**10

steps = ((1, 0), (0, 1), (-1, 0), (0, -1))
raw_windows = {}
counts = Counter()


def bond(a, b):
    return tuple(sorted((a, b)))


def visit(word, code, vertices, bonds):
    depth = len(word)
    counts[depth] += 1
    if depth == 10:
        raw_windows[code] = (word, vertices, bonds)
        return
    x, y = vertices[-1]
    for d, (dx, dy) in enumerate(steps):
        endpoint = (x + dx, y + dy)
        edge = bond(vertices[-1], endpoint)
        if edge not in bonds:
            visit(word + (d,), code * 4 + d, vertices + (endpoint,), bonds | {edge})


visit((), 0, ((0, 0),), frozenset())
assert [counts[j] for j in range(1, 11)] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert all((a < 3741) == (code in raw_windows) and a <= 3741
           for code, a in enumerate(raw_class))


def word_string(code):
    return ''.join('ENWS'[(code // 4**i) % 4] for i in range(9, -1, -1))


target_results = []
for i in range(215, 220):
    name = f'rawClass_{i}'
    start = table_offsets['rawClass'][name]
    width = 4 * len(hexes[name])
    stop = start + width
    first, last = start // 12, (stop - 1) // 12
    # Check every single bit, including partial lanes shared with neighbors.
    expected = sum(((3741 >> ((start + bit) % 12)) & 1) << bit for bit in range(width))
    assert literals[name] == expected
    assert all(raw_class[code] == 3741 and code not in raw_windows
               for code in range(first, last + 1))
    prefixes = sorted({word_string(code)[:5] for code in range(first, last + 1)})
    target_results.append({
        'declaration': name,
        'source_line': text[:literal_matches[i].start()].count('\n') + 1,
        'sha256_hex_digits': hashlib.sha256(hexes[name].encode()).hexdigest(),
        'bit_interval_half_open': [start, stop],
        'code_interval_inclusive': [first, last],
        'code_count': last - first + 1,
        'first_word': word_string(first),
        'last_word': word_string(last),
        'five_direction_prefixes': prefixes,
        'all_bits_match_sentinel_3741': True,
        'raw_windows_in_interval': 0,
    })

# Validate the quotient consumers too, so that a totalization cannot hide an
# incorrect bit order or a class-map discrepancy relevant to the reviewed data.
assert all(code in raw_windows and raw_class[code] == a
           for a, code in enumerate(representatives))
edge_counts = Counter()
for a in range(3741):
    for d in range(4):
        destination, kind = destinations[4*a+d], kinds[4*a+d]
        assert 0 <= destination <= 3741
        assert (destination == 0) == (kind == 3)
        if destination:
            assert kind < 3
            edge_counts[kind] += 1

for code, (word, vertices, bonds) in raw_windows.items():
    a = raw_class[code]
    rep_word, rep_vertices, _ = raw_windows[representatives[a]]
    revisit = vertices[-1] in vertices[:-1]
    for d, (dx, dy) in enumerate(steps):
        endpoint = (vertices[-1][0] + dx, vertices[-1][1] + dy)
        admissible = d != (word[-1] + 2) % 4 and bond(vertices[-1], endpoint) not in bonds
        destination, kind = destinations[4*a+d], kinds[4*a+d]
        assert (destination != 0) == admissible
        if admissible:
            expected_kind = 2 if revisit else (0 if d == word[-1] else 1)
            assert kind == expected_kind
            successor_code = (code % 4**9) * 4 + d
            assert successor_code in raw_windows
            assert destination - 1 == raw_class[successor_code]
            if expected_kind != 2:
                assert word[-1] == rep_word[-1]

assert edge_counts == Counter({0: 2516, 1: 5032, 2: 1872})
result = {
    'raw_counts_by_depth': [counts[j] for j in range(1, 11)],
    'all_1048576_raw_lanes_match_raw_window_domain': True,
    'all_3741_representatives_map_to_own_class': True,
    'all_60092_raw_window_transition_rows_match': True,
    'labelled_edge_counts_straight_turn_revisit': [edge_counts[k] for k in range(3)],
    'targets': target_results,
}
print(json.dumps(result, indent=2))
