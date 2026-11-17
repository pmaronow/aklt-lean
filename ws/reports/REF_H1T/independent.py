"""Referee checks independent of the supplied coverage and tensor contractions.

Run with PYTHONPATH=deps OPENBLAS_NUM_THREADS=1 python3 independent.py.
All generated files stay in the referee directory.
"""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations, product
import hashlib
import json
import re
import numpy as np

HERE = Path(__file__).resolve().parent
SOURCE = Path('/home/ubuntu/aklt/reports/H1TREE_PROOF')
TEX = (SOURCE / 'h1tree.tex').read_text()
MODELS = json.loads((SOURCE / 'data/cores_universal_final.json').read_text())
COORD = dict(E=(1, 0), A=(1, 1), N=(0, 1), B=(-1, 1), W=(-1, 0),
             L=(-1, -1), S=(0, -1), R=(1, -1))


def fractions(s):
    return re.sub(r'\\frac\{(\d+)\}\{(\d+)\}', r'\1/\2', s)


def check_printed_tables():
    printed = []
    for line in TEX.splitlines():
        row = re.match(r'^(\d+) & ([st]) & (.*)', line)
        if not row:
            continue
        i, typ, body = row.groups()
        paths, attrs = [], []
        body = fractions(body)
        for component in body.split(';'):
            path, aa = [], []
            tokens = re.finditer(r'\\ht([MV])\{([EANBWLRS])\}\{([^}]*)\}|([EANBWLRS])', component)
            for token in tokens:
                tag, name, radii, plain = token.groups()
                name = name or plain
                mark = int(name in 'ENW')
                out = int(mark and name == ('N' if typ == 's' else 'E'))
                if tag:
                    kind = 'm' if tag == 'M' else 'u'
                    rs = [str(F(x)) for x in radii.split(',')]
                else:
                    kind = 'd' if name == 'S' else 'u'
                    rs = [] if name == 'S' else ['1', '1']
                path.append(list(COORD[name]))
                aa.append([kind, mark, out, rs])
            assert path
            paths.append(path)
            attrs.append(aa)
        expected = dict(straight=typ == 's', paths=paths, attrs=attrs)
        actual = {k: MODELS[int(i)][k] for k in expected}
        assert expected == actual, (i, expected, actual)
        printed.append(int(i))
    assert printed == list(range(38))

    means = []
    for line in TEX.splitlines():
        if not re.match(r'^\\\(\\ht[UD]\\\) &', line):
            continue
        values = fractions(line).split('&')
        k = 'd' if 'htD' in values[0] else 'u'
        vals = [re.search(r'\d+(?:/\d+)?', v).group() for v in values[1:5]]
        means.append((k, tuple(map(F, vals[:3])), F(vals[3])))
    data = json.loads((SOURCE / 'data/universal_mean_checks.json').read_text())['results']
    expected = [(r['kind'], tuple(map(F, r['radii'])), F(r['R'])) for r in data]
    assert means == expected and len(means) == 21

    witnesses = [json.loads(s) for s in (SOURCE / 'data/universal_certificates.jsonl').read_text().splitlines()]
    rows = []
    for line in TEX.splitlines():
        if not re.match(r'^\d+ & \\\(', line):
            continue
        cols = line.split('&')
        i = int(cols[0])
        inv = list(map(int, re.findall(r'\d+', cols[1])))
        nums = [int(re.search(r'\d+', c).group()) for c in cols[2:]]
        n, g, d, s, margin = nums
        cert = witnesses[i]
        assert cert['S'] == inv
        assert len(cert['forms']) == 1
        f = cert['forms'][0]
        assert [f['n'], f['g'], f['den'], f['S'], f['margin']] == nums
        rows.append(i)
    assert len(rows) == 16
    return means


phi = (1 + np.sqrt(5)) / 2
LETTERS = np.array([(0, a, b) for a in (-1, 1) for b in (-phi, phi)] +
                   [(a, b, 0) for a in (-1, 1) for b in (-phi, phi)] +
                   [(b, 0, a) for a in (-1, 1) for b in (-phi, phi)]) / np.sqrt(phi + 2)
SPINS = np.vstack([LETTERS, np.zeros((1, 3))])
LAW = {'u': np.array([1/12] * 12 + [0]), 'd': np.array([1/20] * 12 + [2/5])}
PAIR = 1 + SPINS @ SPINS.T
RNG = np.random.default_rng(20261117)


def vector(radius=1, boundary=False):
    v = RNG.normal(size=3)
    return radius * v / np.linalg.norm(v) * (1 if boundary else RNG.random())


def mean_direct(kind, fields):
    weight = LAW[kind].copy()
    for field in fields:
        weight *= 1 + SPINS @ field
    assert weight.sum() > 0
    return weight @ SPINS / weight.sum()


def check_means(means):
    max_excess = -np.inf
    trials = 0
    for k, radii, bound in means:
        for j in range(1000):
            fields = [vector(float(r), j % 2 == 0) for r in radii]
            mu = mean_direct(k, fields)
            excess = np.linalg.norm(mu) - float(bound)
            max_excess = max(max_excess, excess)
            assert excess < 2e-14, (k, radii, bound, mu)
            trials += 1
        axis = np.array([1., 0., 0.])
        assert abs(np.linalg.norm(mean_direct(k, [float(r) * axis for r in radii])) - float(bound)) < 2e-14
    for radius, bound in [(F(1, 10), F(18, 35)), (F(3, 25), F(137, 265))]:
        for j in range(2000):
            fields = [vector(1, j % 2 == 0), vector(1, j % 2 == 0), vector(float(radius), j % 2 == 0)]
            excess = np.linalg.norm(mean_direct('u', fields)) - float(bound)
            max_excess = max(max_excess, excess)
            assert excess < 2e-14
            trials += 1
    return dict(trials=trials, maximum_norm_excess=max_excess)


def direct_forest(model, directions):
    """Finite icosahedron sums by one-dimensional messages, no moments/tensors."""
    vertices, fields, marks, outgoing = {}, {}, [], None
    j = 0
    ring_order = list(COORD.values())
    items = [(x, a) for path, aa in zip(model['paths'], model['attrs']) for x, a in zip(path, aa)]
    for x, (kind, marked, out, radii) in sorted(items, key=lambda item: ring_order.index(tuple(item[0]))):
            x = tuple(x)
            vertices[x] = kind
            if kind == 'm':
                radius = float(F(radii[0]))
                fields[x] = radius * directions[j] if radius else np.zeros(3)
                j += int(radius != 0)
            else:
                weight = LAW[kind].copy()
                for r in radii:
                    r = float(F(r))
                    if r:
                        weight *= 1 + SPINS @ (r * directions[j])
                        j += 1
                fields[x] = weight
            if marked:
                marks.append(x)
            if out:
                assert outgoing is None
                outgoing = x
    assert j == len(directions)

    def contraction(observation):
        answer = 1.
        for path in model['paths']:
            path = list(map(tuple, path))
            if vertices[path[0]] == 'm':
                assert len(path) == 1
                x = path[0]
                answer *= fields[x][observation[x]] if x in observation else 1.
            else:
                message = np.ones(13)
                for h, x in enumerate(path):
                    message *= fields[x]
                    if x in observation:
                        message *= SPINS[:, observation[x]]
                    if h + 1 < len(path):
                        message = message @ PAIR
                answer *= message.sum()
        return answer

    z = contraction({})
    corr = {frozenset((a, b)): sum(contraction({a: k, b: k}) for k in range(3))
            for a, b in combinations(marks, 2)}
    fg = [x for x in marks if x != outgoing]
    cur = z + sum(corr.values()) / 3
    nxt = z + (corr[frozenset(fg)] / 5 if len(fg) == 2 else 0)
    return np.array([cur, nxt])


def check_reconstruction():
    # Import only the supplied coefficient constructor, then compare it with
    # direct finite-spin sums using a separate integration algorithm.
    import sys
    sys.path.insert(0, str(HERE / 'replay/checks'))
    from reconstruct import Tree
    trials, max_error, min_slack = 0, 0., np.inf
    for i, model in enumerate(MODELS):
        tree = Tree(model)
        c = .961 if model['straight'] else .935
        for j in range(48):
            directions = [vector(1, j % 2 == 0) for _ in range(tree.n)]
            direct = direct_forest(model, directions)
            tensor = []
            for arr, mult in [(tree.cur, 3), (tree.nxt, 5)]:
                aa = np.asarray(arr, dtype=float)
                for v in directions:
                    aa = np.tensordot(np.r_[1, v], aa, axes=(0, 0))
                tensor.append(float(aa) / (float(tree.scale) * mult))
            error = np.max(np.abs(direct - tensor)) / max(1., np.max(np.abs(direct)))
            max_error = max(max_error, error)
            assert error < 2e-13, (i, direct, tensor)
            assert direct[1] > 0
            slack = direct[0] / direct[1] - c
            min_slack = min(min_slack, slack)
            assert slack > -2e-13
            trials += 1
    return dict(trials=trials, maximum_relative_error=max_error, minimum_ratio_slack=min_slack)


def check_single_site_identities():
    errors = []
    for _ in range(300):
        a, b = vector(), vector()
        left = np.sum(LAW['d'] * (1 + SPINS @ a) * (1 + SPINS @ b))
        right = np.mean((1 + np.sqrt(.6) * (LETTERS @ a)) * (1 + np.sqrt(.6) * (LETTERS @ b)))
        errors.append(abs(left - right))
        assert abs(left - right) < 3e-15
    q = F(226, 495)
    assert 1 - q*q/3 == F(683999, 735075) < F(187, 200)
    return dict(arrival_split_trials=300, maximum_error=max(errors), discarded_correlation_counterexample=str(1 - q*q/3))


if __name__ == '__main__':
    means = check_printed_tables()
    result = dict(printed_models_checked=38, printed_mean_rows_checked=21,
                  printed_matrix_rows_checked=16, means=check_means(means),
                  reconstruction=check_reconstruction(),
                  identities=check_single_site_identities())
    (HERE / 'independent-results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
