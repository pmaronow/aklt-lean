"""Read-only reconstruction of the supplied Lean literals and paper raw windows."""
from pathlib import Path
import collections
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literals = {}
widths = {}
lines = {}
for line_no, line in enumerate(text.splitlines(), 1):
    match = re.fullmatch(r'private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)', line)
    if match:
        name, digits = match.groups()
        literals[name] = int(digits, 16)
        widths[name] = 4 * len(digits)
        lines[name] = line_no


def parse_packed(name):
    expression = re.search(r'^noncomputable def ' + name + r' : ℕ := (.+)$', text, re.M)[1]
    tokens = re.findall(r'<<<|\w+|[()+]', expression)
    assert ''.join(tokens) == re.sub(r'\s+', '', expression)
    groups = [[]]
    for token in tokens:
        if token == '(':
            groups.append([])
        elif token == ')':
            group = groups.pop()
            assert len(group) in (1, 3)
            if len(group) == 3:
                assert group[1] in ('+', '<<<')
            groups[-1].append('GROUP')
        else:
            groups[-1].append(token)
    assert len(groups) == 1 and len(groups[0]) in (1, 3)
    index = 0

    def atom():
        nonlocal index
        token = tokens[index]
        index += 1
        if token == '(':
            result = expr()
            assert tokens[index] == ')'
            index += 1
            return result
        if token.isdecimal():
            return int(token), []
        return literals[token], [(token, 0)]

    def expr():
        nonlocal index
        result = atom()
        while index < len(tokens) and tokens[index] != ')':
            op = tokens[index]
            index += 1
            right = atom()
            if op == '+':
                result = result[0] + right[0], result[1] + right[1]
            else:
                assert op == '<<<' and not right[1]
                result = result[0] << right[0], [(leaf, offset + right[0]) for leaf, offset in result[1]]
        return result

    value, leaves = expr()
    assert index == len(tokens)
    # Every operator-containing operand is explicitly parenthesized, so the
    # grouping is independent of the relative infix precedence of + and <<<.
    ordered = sorted(leaves, key=lambda pair: pair[1])
    end = 0
    for leaf, offset in ordered:
        assert offset == end, (name, leaf, offset, end)
        assert literals[leaf] < (1 << widths[leaf])
        end += widths[leaf]
    return value, dict(leaves), end


tables = {}
offsets = {}
table_bits = {}
for table in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    value, offsets[table], table_bits[table] = parse_packed(table)
    tables[table] = value.to_bytes((table_bits[table] + 7) // 8, 'little')


def lane(table, width, index):
    start, low = divmod(width * index, 8)
    data = tables[table][start:start + (low + width + 7) // 8]
    return (int.from_bytes(data, 'little') >> low) & ((1 << width) - 1)


expected_bits = dict(rawClass=12 * 4**10, representatives=20 * 3741,
                     destinations=12 * 4 * 3741, edgeKinds=2 * 4 * 3741)
assert all(0 <= expected_bits[name] - bits < 32 for name, bits in table_bits.items())
# Natural numerals omit leading zero bits; reading beyond the stored high bit
# correctly returns zero, just as natural division does in Lean's lane.
classes = [lane('rawClass', 12, code) for code in range(4**10)]
reps = [lane('representatives', 20, a) for a in range(3741)]
destinations = [[lane('destinations', 12, 4*a + d) for d in range(4)] for a in range(3741)]
kinds = [[lane('edgeKinds', 2, 4*a + d) for d in range(4)] for a in range(3741)]

steps = [(1, 0), (0, 1), (-1, 0), (0, -1)]
raw = {}
raw_info = {}
counts = [0] * 11
vertices = [(0, 0)]
bonds = set()


def bond(x, y):
    return tuple(sorted((x, y)))


def generate(depth, code):
    counts[depth] += 1
    x = vertices[-1]
    if depth == 10:
        last = code % 4
        revisit = x in vertices[:-1]
        raw_info[code] = last, revisit
        row = []
        for d, delta in enumerate(steps):
            y = x[0] + delta[0], x[1] + delta[1]
            allowed = d != (last + 2) % 4 and bond(x, y) not in bonds
            row.append((2 if revisit else 0 if d == last else 1) if allowed else 3)
        raw[code] = tuple(row)
        return
    for d, delta in enumerate(steps):
        y = x[0] + delta[0], x[1] + delta[1]
        edge = bond(x, y)
        if edge not in bonds:
            vertices.append(y)
            bonds.add(edge)
            generate(depth + 1, 4 * code + d)
            bonds.remove(edge)
            vertices.pop()


generate(0, 0)
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
issues = []
for code, a in enumerate(classes):
    if a > 3741 or ((a < 3741) != (code in raw)):
        issues.append(dict(check='coverage', code=code, value=a))
for a, rep in enumerate(reps):
    if rep >= 4**10 or rep not in raw or classes[rep] != a:
        issues.append(dict(check='representative', a=a, rep=rep))
for a in range(3741):
    for d in range(4):
        dest, kind = destinations[a][d], kinds[a][d]
        if dest > 3741 or ((dest == 0) != (kind == 3)) or (dest != 0 and kind >= 3):
            issues.append(dict(check='row_encoding', a=a, d=d, dest=dest, kind=kind))

checks_by_code = {}
for code, row in raw.items():
    a = classes[code]
    if a >= 3741:
        continue
    local_issues = []
    last, revisit = raw_info[code]
    rep_last, rep_revisit = raw_info[reps[a]]
    for d, kind in enumerate(row):
        raw_kind = 2 if revisit else 0 if d == last else 1
        representative_kind = 2 if rep_revisit else 0 if d == rep_last else 1
        if raw_kind != representative_kind:
            local_issues.append(dict(check='representative_kind_all_directions', d=d))
        dest = destinations[a][d]
        if (dest != 0) != (kind != 3):
            local_issues.append(dict(check='admissibility', d=d))
        if kind != 3:
            if kinds[a][d] != kind:
                local_issues.append(dict(check='kind', d=d))
            successor_code = (code % (4**9)) * 4 + d
            if successor_code not in raw or classes[successor_code] != dest - 1:
                local_issues.append(dict(check='successor', d=d, successor_code=successor_code))
            if kind != 2 and code % 4 != reps[a] % 4:
                local_issues.append(dict(check='arrival', d=d))
    checks_by_code[code] = local_issues
    issues.extend(dict(code=code, a=a, **issue) for issue in local_issues)

chunk_results = []
for i in range(570, 575):
    name = f'rawClass_{i}'
    low = offsets['rawClass'][name]
    high = low + widths[name]
    first = low // 12
    last = (high - 1) // 12
    codes = range(first, last + 1)
    valid = [code for code in codes if code in raw]
    chunk_results.append(dict(
        declaration=name, line=lines[name], bit_interval=[low, high],
        inclusive_codes=[first, last], touched_lanes=len(codes), raw_windows=len(valid),
        invalid_words=len(codes)-len(valid), class_range=[min(classes[c] for c in valid), max(classes[c] for c in valid)],
        admitted_transitions=sum(sum(k != 3 for k in raw[c]) for c in valid),
        boundary_lanes=[dict(code=c, value=classes[c]) for c in (first,last)],
        failures=[issue for issue in issues if first <= issue.get('code', -1) <= last],
    ))

# Independently inspect every touched code by taking all ten base-four digits
# and comparing all unordered endpoint pairs, rather than using the DFS.
first_touched = min(c['inclusive_codes'][0] for c in chunk_results)
last_touched = max(c['inclusive_codes'][1] for c in chunk_results)
for code in range(first_touched, last_touched + 1):
    digits = [(code // 4**i) % 4 for i in range(9, -1, -1)]
    path = [(0, 0)]
    for d in digits:
        x, delta = path[-1], steps[d]
        path.append((x[0] + delta[0], x[1] + delta[1]))
    edges = [frozenset((x, y)) for x, y in zip(path, path[1:])]
    is_raw = len(set(edges)) == 10
    assert is_raw == (code in raw) == (classes[code] < 3741)
    if is_raw:
        row = []
        for d, delta in enumerate(steps):
            x = path[-1]
            edge = frozenset((x, (x[0] + delta[0], x[1] + delta[1])))
            row.append((2 if x in path[:-1] else 0 if d == digits[-1] else 1)
                       if d != (digits[-1] + 2) % 4 and edge not in edges else 3)
        assert tuple(row) == raw[code]

result = dict(source=str(SOURCE), source_sha256=hashlib.sha256(text.encode()).hexdigest(),
              literal_count=len(literals), table_bits=table_bits, raw_counts=counts[1:],
              class_histogram=dict(collections.Counter(classes)),
              edge_counts={str(k):sum(row.count(k) for row in kinds) for k in range(4)},
              issues_count=len(issues), issues=issues[:30], chunks=chunk_results)
Path('check_results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({key:value for key,value in result.items() if key != 'class_histogram'}, indent=2))
