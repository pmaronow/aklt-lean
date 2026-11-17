"""Exact arithmetic checks for REV_C1a; these do not certify H1/H2."""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import re
import sympy as sp

ROOT = Path(__file__).resolve().parent
PLAN = Path("/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md")
ASSIGNED = {
    "sec2-moments.tex": [
        "d:moment", "l:moments", "d:pinmodel", "l:finitefacts",
        "l:35", "l:exact", "h:P",
    ],
    "sec6-walks.tex": [
        "d:domain", "d:trace", "l:stepid", "p:pairwalk", "d:ratios",
        "l:response", "l:exposure", "d:pattern", "h:H1", "l:local",
        "d:weights", "h:H2", "l:onepoint",
    ],
}


def audit_statements():
    fence = chr(96) * 3
    pattern = r"^### ([^ \n]+).*?\n" + fence + r"latex\n(.*?)\n" + fence
    registry = {
        m.group(1): m.group(2)
        for m in re.finditer(pattern, PLAN.read_text(), re.M | re.S)
    }
    whole = ""
    interface_count = 0
    interface = PLAN.with_name("interfaces.tex").read_text()
    for name, expected in ASSIGNED.items():
        text = (ROOT / name).read_text()
        positions = []
        for label in expected:
            statement = registry[label]
            assert statement in text, (name, label, "statement changed")
            positions.append(text.index(statement))
            if rf"\label{{{label}}}" in interface:
                assert statement in interface, (label, "interface mismatch")
                interface_count += 1
        assert positions == sorted(positions), name
        assert "% PROOF" not in text and "TODO" not in text
        whole += text
    labels = re.findall(r"\\label\{([^}]+)\}", whole)
    refs = set(re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", whole))
    assert len(labels) == len(set(labels)), "duplicate labels"
    assert not refs - set(labels), ("unresolved references", refs - set(labels))
    print("PASS: 20 exact statements, plan order,",
          interface_count, "matching interface exports; no unresolved references")


@lru_cache(None)
def moment(exponents, status="U"):
    degree = sum(exponents)
    assert degree <= 4, (exponents, status)
    if degree == 0:
        return F(1)
    if any(e % 2 for e in exponents):
        return F(0)
    if degree == 2:
        result = F(1, 3)
    elif 4 in exponents:
        result = F(1, 5)
    else:
        assert sorted(exponents) == [0, 2, 2]
        result = F(1, 15)
    return result if status == "U" else F(3, 5) * result


def polynomial_functional(poly, n, status="U"):
    return sp.expand(sum(
        coefficient * sp.Rational(moment(exponents, status).numerator,
                                  moment(exponents, status).denominator)
        for exponents, coefficient in sp.Poly(sp.expand(poly), *n).terms()
    ))


def check_moments_and_steps():
    n = sp.symbols("n0:3")
    phi = (1 + sp.sqrt(5)) / 2
    r = sp.sqrt(phi + 2)
    letters = []
    for a, b in product([-1, 1], repeat=2):
        letters.extend([(0, a/r, b*phi/r),
                        (a/r, b*phi/r, 0),
                        (a*phi/r, 0, b/r)])
    assert len(set(letters)) == 12
    for letter in letters:
        assert sp.simplify(sum(x*x for x in letter) - 1) == 0
        assert any(all(sp.simplify(x+y) == 0 for x, y in zip(letter, other))
                   for other in letters)
    v = sp.Matrix([1, 2, 2])
    rotation = sp.eye(3) - 2 * v * v.T / 9
    assert rotation * rotation.T == sp.eye(3)
    transformed = rotation * sp.Matrix(n)
    count = 0
    for degree in range(5):
        for i in range(degree + 1):
            for j in range(degree - i + 1):
                exponents = (i, j, degree-i-j)
                actual = sum(
                    sp.prod(x**e for x, e in zip(letter, exponents))
                    for letter in letters
                ) / 12
                expected = moment(exponents)
                assert sp.simplify(actual - sp.Rational(expected)) == 0
                rotated = sp.prod(x**e for x, e in zip(transformed, exponents))
                assert polynomial_functional(rotated, n) == sp.Rational(expected)
                count += 1
    assert count == 35

    a = sp.symbols("a0:3")
    fields = [sp.symbols(f"u{i}_0 u{i}_1 u{i}_2") for i in range(3)]
    dot = lambda x, y: sum(s*t for s, t in zip(x, y))
    for k in range(4):
        factors = [1 + dot(n, u) for u in fields[:k]]
        lhs = polynomial_functional(dot(a, n) * sp.prod(factors), n)
        rhs = sum(
            dot(a, fields[i]) / 3 *
            polynomial_functional(
                sp.prod(factors[j] for j in range(k) if j != i), n, "D"
            )
            for i in range(k)
        )
        assert sp.expand(lhs-rhs) == 0
    for k in range(2):
        lhs = polynomial_functional(
            dot(a, n) * sp.prod(1+dot(n, u) for u in fields[:k]), n, "D"
        )
        rhs = sum(dot(a, u)/5 for u in fields[:k])
        assert sp.expand(lhs-rhs) == 0
    assert polynomial_functional(dot(n, n), n) == 1
    assert polynomial_functional(dot(n, n), n, "D") == sp.Rational(3, 5)
    print("PASS: 12 unit letters; all 35 moments; rational orthogonal covariance; "
          "all 6 used step identities and both squared-norm moments")


def check_mean_and_response():
    x, y, z = sp.symbols("x y z")
    p = x+y+z
    squared = ((5+z)**2+(5+y)**2+(5+x)**2
               +2*x*(5+z)*(5+y)+2*y*(5+z)*(5+x)+2*z*(5+y)*(5+x))
    X, Y, Z = 1-z, 1-y, 1-x
    sos = 4*((X-Y)**2+(X-Z)**2+(Y-Z)**2)+6*X*Y*Z
    assert sp.expand((9+3*p)**2-squared-sos) == 0
    for s, exact, upper, cross in [
        (F(41, 50), F(340634561, 926892330),
         F(367502, 10**6), 224059660),
        (F(22, 25), F(24332081, 68523180),
         F(35510, 100000), 50021800),
    ]:
        t = (1-s)/(1+s)
        B = 2/(1-s)*(t+t**3/3+t**5/(5*(1-t*t)))
        assert B/3 == exact and exact < upper
        # Cross products use the displayed right-hand denominators.
        numerator, denominator = ((367502, 10**6) if s == F(41, 50)
                                  else (35510, 100000))
        assert numerator*exact.denominator-denominator*exact.numerator == cross
    assert F(25, 102)-F(25, 116) == F(175, 5916) > 0
    alpha = F(367502, 10**6)-F(25, 134)
    assert alpha == F(6061317, 33500000)
    assert F(18094, 100000)-alpha == F(173, 33500000) > 0
    assert F(35510, 100000) <= F(36751, 100000)
    print("PASS: three-field sum-of-squares identity and every displayed "
          "rational response bound/cross product")


@lru_cache(None)
def network_sum(statuses, edges, fields=(), observable=None):
    """Exact edge-component expansion for small retained networks.

    fields lists (site, multiplicity) for unit fields e_1. These checks
    concern the expansion algebra; their stopping sets are specified
    separately, without asserting a geometric mixing hypothesis.
    """
    statuses = dict(statuses)
    sites = tuple(sorted(statuses))
    indices = {site: i for i, site in enumerate(sites)}
    degree = Counter(site for edge in edges for site in edge)
    for site, power in fields:
        degree[site] += power
    if observable is not None:
        degree.update(observable)
    assert all(degree[site] <= 4 for site in sites), (degree, observable)
    endpoint_colors = range(3) if observable is not None else [None]
    terms = [[(k, int(sp.binomial(power, k))) for k in range(power+1)]
             for site, power in fields]
    total = F(0)
    for edge_colors in product(range(4), repeat=len(edges)):
        base = [[0, 0, 0] for _ in sites]
        for edge, color in zip(edges, edge_colors):
            if color:
                for site in edge:
                    base[indices[site]][color-1] += 1
        for field_terms in product(*terms):
            scalar = 1
            exponents = [row[:] for row in base]
            for (site, power), (k, coefficient) in zip(fields, field_terms):
                exponents[indices[site]][0] += k
                scalar *= coefficient
            for color in endpoint_colors:
                current = [row[:] for row in exponents]
                if color is not None:
                    for site in observable:
                        current[indices[site]][color] += 1
                local = [moment(tuple(row), statuses[site])
                         for site, row in zip(sites, current)]
                if all(local):
                    value = F(scalar)
                    for factor in local:
                        value *= factor
                    total += value
    return total


def check_pair_expansions():
    # c--a--b--d--c is a unit square; u and v are leaves at c.
    loop_edges = (("a", "b"), ("a", "c"), ("b", "d"),
                  ("c", "d"), ("c", "u"), ("c", "v"))
    completed = 0
    revisits = 0
    boundary_hits = 0
    for pinned in [False, True]:
        edges = loop_edges + ((("b", "e"),) if pinned else ())
        stop = {"v", "e"} if pinned else {"v"}
        fields = (("e", 2),) if pinned else ()
        for start_status, target_status in product(["U", "D"], repeat=2):
            statuses = {x: "U" for x in set(sum(edges, ()))}
            statuses["u"], statuses["v"] = start_status, target_status
            initial = tuple(sorted(statuses.items()))
            lhs = network_sum(initial, edges, fields, ("u", "v"))
            rhs = F(0)

            def trace(current, st, remaining, coefficient, length, nd):
                nonlocal rhs, revisits, boundary_hits
                if current in stop:
                    rhs += coefficient * network_sum(
                        tuple(sorted(st.items())), remaining, fields,
                        (current, "v")
                    )
                    assert coefficient == F(1, 3)**length * F(3, 5)**nd
                    boundary_hits += current == "e"
                    revisits += nd > (start_status == "D")
                    return
                incident = [edge for edge in remaining if current in edge]
                assert len(incident) <= (3 if st[current] == "U" else 1)
                for edge in incident:
                    target = edge[0] if edge[1] == current else edge[1]
                    next_edges = tuple(e for e in remaining if e != edge)
                    next_status = st.copy()
                    was_d = st[current] == "D"
                    if was_d:
                        assert len(incident) == 1
                        del next_status[current]
                        before = network_sum(tuple(sorted(st.items())),
                                             remaining, fields)
                        after = network_sum(tuple(sorted(next_status.items())),
                                            next_edges, fields)
                        assert before == after
                    else:
                        next_status[current] = "D"
                    trace(target, next_status, next_edges,
                          coefficient * F(1, 5 if was_d else 3),
                          length+1, nd+was_d)

            trace("u", statuses, edges, F(1), 0, 0)
            assert lhs == rhs, (pinned, start_status, target_status, lhs, rhs)
            norm = network_sum(initial, edges, fields)
            expected = F(1, 3 if start_status == "U" else 5) * F(
                1, 3 if target_status == "U" else 5
            )
            assert lhs / norm == expected
            completed += 1
    assert revisits and boundary_hits
    print("PASS:", completed, "exact pair expansions, including D revisits, "
          "D starts/targets, unchanged boundary fields and all degree bounds")


if __name__ == "__main__":
    audit_statements()
    check_moments_and_steps()
    check_mean_and_response()
    check_pair_expansions()
