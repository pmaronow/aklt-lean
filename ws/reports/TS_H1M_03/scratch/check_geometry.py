"""Finite structural diagnostics, not Lean proofs or polynomial expansion.

Every subset of all 16 template edges is checked in both representations.
The all-active case overapproximates covered patterns: any inactive site has
degree zero and contributes no factor, so removing it changes no factor count.
The current factor list bounds both choices of `next`, which only deletes a bond.
"""

from collections import Counter
from itertools import combinations
import json
from pathlib import Path


sites = {
    (x, y)
    for x in range(-2, 3)
    for y in range(-2, 3)
    if abs(x) + abs(y) <= 2
}
tips = {(2, 0), (0, 2), (-2, 0), (0, -2)}
corners = {(1, 1), (-1, 1), (-1, -1), (1, -1)}
edges = sorted(
    (x, y)
    for x, y in combinations(sorted(sites), 2)
    if abs(x[0] - y[0]) + abs(x[1] - y[1]) == 1
)
leaders = {
    (1, 1): 0,
    (-1, 1): 2,
    (-1, -1): 4,
    (1, -1): 6,
    (2, 0): 8,
    (0, 2): 11,
    (-2, 0): 14,
    (0, -2): 17,
}

assert len(sites) == 13 and len(edges) == 16
assert all(not (x in tips | corners and y in tips | corners) for x, y in edges)

max_degrees = Counter()
max_tokens = Counter()
checked = 0
for mask in range(1 << len(edges)):
    bonds = [edge for i, edge in enumerate(edges) if mask & (1 << i)]
    degree = Counter(x for edge in bonds for x in edge)
    groups = {x for x in tips | corners if degree[x] > 0}
    for representation in ('reduced', 'unreduced'):
        singles = {
            x for x in groups
            if degree[x] == 1 and (x in tips or representation == 'reduced')
        }
        pairs = groups - singles
        retained = {
            x for x in sites
            if x not in tips and (x not in corners or (degree[x] != 0 and x not in singles))
        }
        factor_degrees = Counter()
        tokens = []
        for x, y in bonds:
            if x in retained and y in retained:
                factor_degrees[x] += 1
                factor_degrees[y] += 1
        for x in pairs:
            assert x in corners and x in retained
            factor_degrees[x] += 2
            tokens.extend((leaders[x], min(19, leaders[x] + 1)))
        for x in singles:
            neighbors = [y if z == x else z for z, y in bonds if z == x or y == x]
            assert len(neighbors) == 1
            assert neighbors[0] in retained
            factor_degrees[neighbors[0]] += 1
            tokens.append(leaders[x])
        assert set(factor_degrees) <= retained
        assert max(factor_degrees.values(), default=0) <= 4
        assert len(tokens) == len(set(tokens))
        assert set(tokens) <= set(range(20))
        max_degrees[representation] = max(max_degrees[representation], max(factor_degrees.values(), default=0))
        max_tokens[representation] = max(max_tokens[representation], len(tokens))
        checked += 1

result = {
    'template_sites': len(sites),
    'template_edges': len(edges),
    'edge_subsets_checked': 1 << len(edges),
    'graph_representation_cases_checked': checked,
    'max_spin_factor_degree': dict(max_degrees),
    'max_tokens': dict(max_tokens),
    'failures': 0,
    'scope': 'All edge subsets with all sites active; covers inactive sites by omission of isolated sites; next can only remove an internal bond.',
    'checks': [
        'Each internal coordinate in a factor belongs to the retained spin set.',
        'Every retained spin has at most four linear incident factors.',
        'Distinct groups use distinct vector tokens, including both slots of a retained corner.',
        'Every singly replaced leaf has exactly one retained neighbor.',
    ],
}
(Path(__file__).parent / 'geometry_checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
