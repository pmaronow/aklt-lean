"""Exact algebra checks for the referee audit of Sections 2 and 6.

Uses only Python's standard library, one process, and no data files.
These checks supplement the proof audit; they are not a Lean certificate.
"""

from collections import defaultdict
from fractions import Fraction as F
from itertools import product


def moment(indices, status="U"):
    degree = len(indices)
    if degree == 0:
        return F(1)
    if degree % 2:
        return F(0)
    if degree == 2:
        return F(indices[0] == indices[1], 3 if status == "U" else 5)
    if degree == 4:
        a, b, c, d = indices
        numerator = (
            int(a == b and c == d)
            + int(a == c and b == d)
            + int(a == d and b == c)
        )
        return F(numerator, 15 if status == "U" else 25)
    raise ValueError(degree)


def step_identities():
    count = 0
    # Multilinearity reduces the identity to every subset of fields and
    # every coordinate choice for the marked vector and selected fields.
    for k in range(4):
        for bits in product((0, 1), repeat=k):
            selected = [i for i, bit in enumerate(bits) if bit]
            for coordinates in product(range(3), repeat=1 + len(selected)):
                marked = coordinates[0]
                field = dict(zip(selected, coordinates[1:]))
                lhs = moment(coordinates)
                rhs = sum(
                    (
                        F(marked == field[i], 3)
                        * moment([field[j] for j in selected if j != i], "D")
                        for i in selected
                    ),
                    F(0),
                )
                assert lhs == rhs
                count += 1
    assert count == 255
    print("l:stepid U identity: all 255 multilinear coefficients agree")

    count = 0
    for k in range(2):
        for bits in product((0, 1), repeat=k):
            selected = [i for i, bit in enumerate(bits) if bit]
            for coordinates in product(range(3), repeat=1 + len(selected)):
                lhs = moment(coordinates, "D")
                rhs = F(coordinates[0] == coordinates[1], 5) if selected else F(0)
                assert lhs == rhs
                count += 1
    assert count == 15
    print("l:stepid D identity: all 15 multilinear coefficients agree")


# Sparse exact polynomials in x=b.c, y=a.c, z=a.b.
def constant(c):
    return {(0, 0, 0): F(c)} if c else {}


def add(*polynomials):
    result = defaultdict(F)
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] += coefficient
    return {e: c for e, c in result.items() if c}


def scale(polynomial, scalar):
    return {e: c * scalar for e, c in polynomial.items() if c * scalar}


def multiply(p, q):
    result = defaultdict(F)
    for a, c in p.items():
        for b, d in q.items():
            result[tuple(x + y for x, y in zip(a, b))] += c * d
    return {e: c for e, c in result.items() if c}


def square(p):
    return multiply(p, p)


def mean_bound_identity():
    x = {(1, 0, 0): F(1)}
    y = {(0, 1, 0): F(1)}
    z = {(0, 0, 1): F(1)}
    p = add(x, y, z)
    A, B, C = [add(constant(5), v) for v in (x, y, z)]
    v_squared = add(
        square(A), square(B), square(C),
        scale(multiply(z, multiply(A, B)), 2),
        scale(multiply(y, multiply(A, C)), 2),
        scale(multiply(x, multiply(B, C)), 2),
    )
    X, Y, Z = [add(constant(1), scale(v, -1)) for v in (x, y, z)]
    rhs = add(
        scale(add(square(add(X, scale(Y, -1))),
                  square(add(X, scale(Z, -1))),
                  square(add(Y, scale(Z, -1)))), 4),
        scale(multiply(X, multiply(Y, Z)), 6),
    )
    residual = add(square(add(constant(9), scale(p, 3))),
                   scale(v_squared, -1), scale(rhs, -1))
    assert not residual
    print("l:35 norm identity: zero polynomial residual")


def icosahedral_identities():
    # Exact Q(phi) arithmetic, phi^2=phi+1; all coordinates with an odd
    # exponent cancel by the independent coordinate sign symmetries.
    def qadd(a, b):
        return tuple(x + y for x, y in zip(a, b))

    def qmul(a, b):
        x, y = a
        u, v = b
        return (x * u + y * v, x * v + y * u + y * v)

    one, phi = (F(1), F(0)), (F(0), F(1))
    phi2 = qmul(phi, phi)
    phi4 = qmul(phi2, phi2)
    r2 = qadd(phi, (F(2), F(0)))
    r4 = qmul(r2, r2)
    assert qadd(one, phi2) == r2
    assert r4 == qmul((F(5), F(0)), phi2)
    assert qadd(one, phi4) == qmul((F(3), F(0)), phi2)
    print("l:moments: norm and fourth-moment algebra verified in Q(phi)")


def response_constants():
    rows = [
        (F(41, 50), F(340634561, 926892330), 367502, 10**6, 224059660),
        (F(22, 25), F(24332081, 68523180), 35510, 100000, 50021800),
    ]
    for value, expected, numerator, denominator, difference in rows:
        t = (1 - value) / (1 + value)
        B = 2 / (1 - value) * (t + t**3 / 3 + t**5 / (5 * (1 - t*t)))
        assert B / 3 == expected
        assert F(numerator, denominator) > expected
        assert (numerator * expected.denominator
                - denominator * expected.numerator) == difference
    assert F(25, 102) - F(25, 116) == F(175, 5916) > 0
    upper = F(367502, 10**6) - F(25, 134)
    assert upper == F(6061317, 33500000)
    assert F(18094, 100000) - upper == F(173, 33500000) > 0
    assert F(367502, 10**6) < F(36751, 100000)
    assert F(35510, 100000) < F(36751, 100000)
    print("l:response: both logarithm rows, cross products, and alpha/beta margins agree")


if __name__ == "__main__":
    icosahedral_identities()
    mean_bound_identity()
    step_identities()
    response_constants()
    print("All exact checks passed.")
