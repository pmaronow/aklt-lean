"""Independent exact check of the H2 existence assertion; uses no archive files."""

from fractions import Fraction
from itertools import product
import json
from pathlib import Path


DIRECTIONS = ((1, 0), (0, 1), (-1, 0), (0, -1))
DENOMINATOR = 2695605
NUMERATORS = (935000, 961000, 539121)
Q = Fraction(1119948287353, 1120437614225)


def edge(x, y):
    return tuple(sorted((x, y)))


def code(word):
    return sum(d * 4**i for i, d in enumerate(word))


def canonical(word):
    return min(
        code(tuple((sign * d + rotation) % 4 for d in word))
        for sign in (-1, 1)
        for rotation in range(4)
    )


def window_data(word):
    x = (0, 0)
    used = set()
    departed = set()
    for d in word:
        departed.add(x)
        dx, dy = DIRECTIONS[d]
        y = (x[0] + dx, x[1] + dy)
        bond = edge(x, y)
        if bond in used:
            return None
        used.add(bond)
        x = y
    return x, used, departed


def check():
    assert Fraction(NUMERATORS[0], DENOMINATOR) == Fraction(1000, 2883)
    assert Fraction(NUMERATORS[1], DENOMINATOR) == Fraction(200, 561)
    assert Fraction(NUMERATORS[2], DENOMINATOR) == Fraction(1, 5)
    raw = {
        word: data
        for word in product(range(4), repeat=6)
        if (data := window_data(word)) is not None
    }
    orbit_codes = {canonical(word) for word in raw}
    records = json.loads(
        Path(__file__).with_name('referee_h2_witness.json').read_text()
    )
    assert len(raw) == 916 and len(orbit_codes) == 115
    assert len(records) == 115
    values = {row['code']: row['h'] for row in records}
    assert len(values) == 115 and set(values) == orbit_codes
    assert all(type(value) is int and value > 0 for value in values.values())
    assert values[441] == min(values.values()) == 186377076276
    assert values[0] == max(values.values()) == 1000000000000
    assert Fraction(max(values.values()), min(values.values())) == Fraction(
        250000000000, 46594269069
    )
    assert max(values.values()) < 6 * min(values.values())
    ratios = []
    for word, (x, used, departed) in raw.items():
        numerator = 0
        for d, (dx, dy) in enumerate(DIRECTIONS):
            y = (x[0] + dx, x[1] + dy)
            if edge(x, y) in used:
                continue
            kind = 2 if x in departed else (0 if d == word[-1] else 1)
            successor = word[1:] + (d,)
            assert successor in raw
            numerator += NUMERATORS[kind] * values[canonical(successor)]
        value = values[canonical(word)]
        assert Q.denominator * numerator <= Q.numerator * DENOMINATOR * value
        ratios.append(Fraction(numerator, DENOMINATOR * value))
        if code(word) == 428:
            assert value == 224087522845
            assert numerator == 603787640626036713
            assert ratios[-1] == Q
    assert max(ratios) == Q
    assert Fraction(999, 1000) < Q < Fraction(2499, 2500) < 1
    assert 6 * (Fraction(200, 187) / Q) ** 6 < 10
    print('PASS: 916 raw rows, 115 orbits, exact extrema and maximum q, C_V = 10.')


if __name__ == '__main__':
    check()
