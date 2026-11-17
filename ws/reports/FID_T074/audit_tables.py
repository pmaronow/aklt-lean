"""Read-only reconstruction of Automaton10Data and the paper's raw trail test."""
from pathlib import Path
import ast
from collections import Counter
import hashlib
import json
import re

SOURCE = Path('/home/ubuntu/aklt/review/FID_T/lean/AKLT/Defs/Automaton10Data.lean')
text = SOURCE.read_text()
literal_matches = list(re.finditer(
    r'^private noncomputable def (\w+) : ℕ := 0x([0-9a-f]+)$', text, re.M))
literals = {m[1]: int(m[2], 16) for m in literal_matches}
literal_hex = {m[1]: m[2] for m in literal_matches}
line_numbers = {m[1]: text.count('\n', 0, m.start()) + 1 for m in literal_matches}


def parse_pack(name):
    expression = re.search(
        rf'^noncomputable def {name} : ℕ := (.+)$', text, re.M)[1]
    tree = ast.parse(expression.replace('<<<', '<<'), mode='eval').body

    def walk(node):
        if isinstance(node, ast.Name):
            return literals[node.id], {node.id: 0}
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
            value, locations = walk(node.left)
            assert isinstance(node.right, ast.Constant)
            shift = node.right.value
            return value << shift, {k: v + shift for k, v in locations.items()}
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            left, a = walk(node.left)
            right, b = walk(node.right)
            assert a.keys().isdisjoint(b)
            return left + right, a | b
        raise ValueError(ast.dump(node))

    packed, locations = walk(tree)
    # Every summand has a disjoint bit interval; addition is concatenation.
    ordered = sorted(locations, key=locations.get)
    for a, b in zip(ordered, ordered[1:]):
        assert locations[a] + literals[a].bit_length() <= locations[b], (a, b)
    assert set(locations) == {k for k in literals if k.startswith(name + '_')}
    return packed, locations


packed = {}
offsets = {}
for name in ('rawClass', 'representatives', 'destinations', 'edgeKinds'):
    packed[name], offsets[name] = parse_pack(name)


def lanes(name, width, count):
    # Conversion once avoids repeatedly shifting a twelve-million-bit integer.
    value = packed[name]
    data = value.to_bytes((value.bit_length() + 7) // 8, 'little') + b'\0' * 4
    mask = (1 << width) - 1
    return [
        (int.from_bytes(data[(width*i)//8:(width*i)//8 + 4], 'little')
         >> ((width*i) % 8)) & mask
        for i in range(count)
    ]


classes = lanes('rawClass', 12, 4**10)
representatives = lanes('representatives', 20, 3741)
destinations = lanes('destinations', 12, 3741 * 4)
kinds = lanes('edgeKinds', 2, 3741 * 4)
steps = ((1, 0), (0, 1), (-1, 0), (0, -1))


def decode(code):
    return tuple((code >> (2*(9-i))) & 3 for i in range(10))


def geometry(word):
    point = (0, 0)
    vertices = [point]
    bonds = set()
    for d in word:
        dx, dy = steps[d]
        nxt = point[0] + dx, point[1] + dy
        bond = tuple(sorted((point, nxt)))
        if bond in bonds:
            return None
        bonds.add(bond)
        vertices.append(nxt)
        point = nxt
    return vertices, bonds


def transitions(word, geo):
    vertices, bonds = geo
    endpoint = vertices[-1]
    revisit = endpoint in vertices[:-1]
    for d, (dx, dy) in enumerate(steps):
        nxt = endpoint[0] + dx, endpoint[1] + dy
        allowed = d != (word[-1] + 2) % 4 and tuple(sorted((endpoint, nxt))) not in bonds
        kind = 2 if revisit else 0 if d == word[-1] else 1
        yield d, allowed, kind


raw_codes = []
counts = [0] * 11


def generate(depth=0, code=0, endpoint=(0, 0), bonds=None):
    if bonds is None:
        bonds = set()
    counts[depth] += 1
    if depth == 10:
        raw_codes.append(code)
        return
    for d, (dx, dy) in enumerate(steps):
        nxt = endpoint[0] + dx, endpoint[1] + dy
        bond = tuple(sorted((endpoint, nxt)))
        if bond not in bonds:
            bonds.add(bond)
            generate(depth+1, 4*code+d, nxt, bonds)
            bonds.remove(bond)


generate()
assert counts[1:] == [4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092]
assert raw_codes == sorted(set(raw_codes))
raw_set = set(raw_codes)
coverage_errors = [(c, a, c in raw_set) for c, a in enumerate(classes)
                   if not (a < 3741 if c in raw_set else a == 3741)]
representative_errors = []
for a, c in enumerate(representatives):
    if c not in raw_set or classes[c] != a:
        representative_errors.append((a, c, classes[c]))
format_errors = [(i, d, k) for i, (d, k) in enumerate(zip(destinations, kinds))
                 if not (d <= 3741 and (d == 0) == (k == 3)
                         and (d == 0 or k < 3))]
edge_counts = Counter(k for d, k in zip(destinations, kinds) if d != 0)
transition_errors = []
representative_words = [decode(c) for c in representatives]
representative_transitions = [list(transitions(w, geometry(w)))
                              for w in representative_words]
for c in raw_codes:
    word = decode(c)
    geo = geometry(word)
    assert geo is not None
    a = classes[c] % 3741
    for d, allowed, kind in transitions(word, geo):
        idx = a*4+d
        # The paper's class hypothesis compares raw kinds even on blocked directions.
        _, representative_allowed, representative_kind = representative_transitions[a][d]
        if (allowed, kind) != (representative_allowed, representative_kind):
            transition_errors.append((c, a, d, 'representative admissibility/kind'))
        if (destinations[idx] != 0) != allowed:
            transition_errors.append((c, a, d, 'admissibility'))
        if allowed:
            if kinds[idx] != kind:
                transition_errors.append((c, a, d, 'kind'))
            successor = ((c % 4**9) * 4) + d
            assert successor in raw_set
            if (max(destinations[idx]-1, 0) % 3741) != classes[successor] % 3741:
                transition_errors.append((c, a, d, 'successor', successor))
            if kind != 2 and representatives[a] % 4 != word[-1]:
                transition_errors.append((c, a, d, 'arrival'))

print('Raw window counts:', counts[1:])
print('Raw map entries:', len(classes), 'range:', (min(classes), max(classes)))
print('Map coverage errors:', len(coverage_errors), coverage_errors[:10])
print('Representative errors:', len(representative_errors), representative_errors[:10])
print('Transition format errors:', len(format_errors), format_errors[:10])
print('Admissible class edge counts (0=s, 1=t, 2=r):', dict(edge_counts))
print('Regenerated raw transition errors:', len(transition_errors), transition_errors[:10])

chunk_results = []
for n in range(335, 340):
    name = f'rawClass_{n}'
    offset = offsets['rawClass'][name]
    width = 4*len(literal_hex[name])
    low = offset // 12
    high = (offset + width - 1) // 12
    codes = range(low, high+1)
    valid = [c for c in codes if c in raw_set]
    result = dict(name=name, line=line_numbers[name], bit_offset=offset,
                  width=width, bit_length=literals[name].bit_length(),
                  code_range=[low, high], raw_windows=len(valid),
                  invalid_codes=len(codes)-len(valid),
                  class_range=[min(classes[c] for c in valid), max(classes[c] for c in valid)]
                  if valid else None,
                  affected_coverage_errors=[e for e in coverage_errors if low <= e[0] <= high],
                  affected_transition_errors=[e for e in transition_errors
                                              if low <= e[0] <= high
                                              or len(e) > 4 and low <= e[4] <= high],
                  sha256_hex=hashlib.sha256(literal_hex[name].encode()).hexdigest())
    chunk_results.append(result)
    print(json.dumps(result))

Path('audit_results.json').write_text(json.dumps(dict(
    counts=counts[1:], coverage_errors=coverage_errors,
    representative_errors=representative_errors, format_errors=format_errors,
    edge_counts=dict(edge_counts), transition_errors=transition_errors,
    chunks=chunk_results), indent=2) + '\n')
