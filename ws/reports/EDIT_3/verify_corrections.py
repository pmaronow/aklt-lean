"""Exact checks for the four EDIT_3 statement corrections; no certificate discharge."""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import re
import subprocess


PAPER = Path("/home/ubuntu/aklt/manuscript-v2")
DIRS = ((1, 0), (0, 1), (-1, 0), (0, -1))
CENTER = (0, 0)
U = (-1, 0)
V = (0, 1)
H = F(5404319552844595, 4503599627370496)
X = {"s": F(1000, 961), "t": F(200, 187)}
A = {"s": F(145217, 10**6), "t": F(150000, 10**6)}
B = {"s": F(352782, 10**6), "t": F(357549, 10**6)}
BP = {"s": F(340008, 10**6), "t": F(344661, 10**6)}


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def sub(x, y):
    return x[0] - y[0], x[1] - y[1]


def bond(x, y):
    return frozenset((x, y))


# REF2_5.1: re-create the arrival-neighbor counterexample from the trace rules.
grid = set(product(range(-4, 5), repeat=2))
status = {x: "U" for x in grid}
status[(1, 0)] = "X"
kept = {x: {add(x, d) for d in DIRS if add(x, d) in grid} for x in grid}
start, live = (0, 0), (0, 1)
kept[start].remove((1, 0))  # Initial flag normalization into the removed center.
kept[start].remove(live)
kept[live].remove(start)
status[start] = "D"
status[live] = "X"  # The ordinary domain just before the U departure, with y removed.


def present(x, y):
    return (
        status[x] != "X"
        and status[y] != "X"
        and y in kept[x]
        and x in kept[y]
    )


assert kept[start] == {(-1, 0), (0, -1)}
assert sum(present(start, y) for y in kept[start]) == 2
for x in grid:
    if status[x] == "U":
        assert kept[x] == {add(x, d) for d in DIRS if add(x, d) in grid}
    elif status[x] == "D":
        assert len(kept[x]) == 2
    if status[x] != "X":
        for y in (add(x, d) for d in DIRS):
            if y in grid and status[y] != "X":
                assert (y in kept[x]) == (x in kept[y])
assert status[start] == "D" and status[(1, 1)] == "U"
assert sum(abs(t) for t in sub(start, (1, 1))) == 2
nonarrival = [add(live, d) for d in DIRS if add(live, d) != start]
for x, y in combinations(nonarrival, 2):
    assert status[x] == status[y] == "U"
    assert sum(abs(t) for t in sub(x, y)) == 2
# A D non-arrival neighbor keeps the live-site bond among exactly two flags.
for flags in combinations(DIRS, 2):
    for arrival_bond in flags:
        assert len(set(flags) - {arrival_bond}) == 1
print("PASS REF2_5.1: arrival D retains two present bonds; non-arrival restriction is valid.")


def trail_data(w):
    assert w[0] == U and w[-1] == V and V not in w[:-1]
    assert CENTER not in w and all(sub(y, x) in DIRS for x, y in zip(w, w[1:]))
    assert len({bond(x, y) for x, y in zip(w, w[1:])}) == len(w) - 1
    departures = Counter()
    data = []
    for i, (site, out) in enumerate(zip(w, w[1:])):
        incoming = sub(site, w[i - 1]) if i else sub(U, CENTER)
        direction = sub(out, site)
        kind = "r" if departures[site] else ("s" if direction == incoming else "t")
        reward = F(0)
        if kind != "r":
            arrival = sub(site, incoming)
            other = [add(site, d) for d in DIRS if add(site, d) not in (arrival, out)]
            live_others = [y for y in other if y != CENTER and departures[y] < 2]

            def pair_weight(x, y):
                return F(1) if add(x, y) == (2 * site[0], 2 * site[1]) else H

            if len(live_others) == 2:
                f, g = live_others
                reward = A[kind] * pair_weight(f, g)
                reward += B[kind] * (pair_weight(f, out) + pair_weight(g, out))
            elif live_others:
                reward = BP[kind] * pair_weight(live_others[0], out)
        data.append((kind, reward))
        departures[site] += 1
    return data


def contribution(data, order):
    pref, total = F(1), F(0)
    for i in order:
        kind, reward = data[i]
        assert kind != "r"
        pref *= X[kind]
        total += reward * pref
    revisits = sum(kind == "r" for kind, _ in data)
    return F(1, 3) ** len(data) * F(3, 5) ** revisits * total


def phase_sum(data):
    pa, pb, pc, pd = F(1), F(1), F(0), F(0)
    for kind, reward in data:
        if kind == "r":
            pa, pb, pc, pd = (v / 5 for v in (pa, pb, pc, pd))
        elif kind == "s":
            x = X[kind]
            pa, pb, pc, pd = x * pa / 3, x * pb / 3, x * pc / 3, (pd + x * reward * pb) / 3
        else:
            x = X[kind]
            pa, pb, pc, pd = x * pa / 3, pb / 3, (pc + x * reward * pa) / 3, pd / 3
    return pc + pd


# REF2_5.2: a required short kernel trail has distinct endpoints.
short = [U, (-1, 1), V]
assert len(trail_data(short)) == 2 and short[0] != short[-1]
print("PASS REF2_5.2: the length-two C kernel trail is open and needs an ordering.")

# REF2_6.2: the ten-step diagnostic distinguishes the two orderings exactly.
w = [
    U, (-1, -1), (0, -1), (0, -2), (1, -2), (1, -1),
    (2, -1), (2, 0), (1, 0), (1, 1), V,
]
data = trail_data(w)
assert all(kind == "t" for kind, _ in data)
k = B["t"] + (A["t"] + B["t"]) * H
p, o, x = BP["t"] * H, BP["t"], X["t"]
assert k > p > o > 0
assert [r for _, r in data] == [k, k, p, k, k, k, k, k, o, k]
order = sorted(range(10), key=lambda i: ((x - 1) / (x * data[i][1]), i))
assert order == [0, 1, 3, 4, 5, 6, 7, 9, 2, 8]
phase = phase_sum(data)
assert phase == contribution(data, range(10))
difference = F(1, 3) ** 10 * ((k - p) * (x**9 - x**3) + (k - o) * (x**10 - x**9))
assert phase - contribution(data, order) == difference > 0
# A long trail uses the phase order, including path order within each type.
long = [
    U, (-2, 0), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, 3),
    (-1, 3), (0, 3), (1, 3), (2, 3), (2, 2), (2, 1), (1, 1), V,
]
data = trail_data(long)
order = [i for t in ("s", "t") for i, (kind, _) in enumerate(data) if kind == t]
assert len(long) - 1 > 12 and phase_sum(data) == contribution(data, order)
print("PASS REF2_6.2: exact short-order discrepancy and long-order phase identity.")

# REF2_6.3: a valid quotient can fail to carry terminal rewards.
words = [(a, b) for a, b in product(DIRS, repeat=2) if b != (-a[0], -a[1])]


def transition(word, direction):
    if direction == (-word[-1][0], -word[-1][1]):
        return None
    return ("s" if direction == word[-1] else "t", direction)


for word1, word2 in product(words, repeat=2):
    if word1[-1] == word2[-1]:
        for direction in DIRS:
            assert transition(word1, direction) == transition(word2, direction)
en, wn = ((1, 0), (0, 1)), ((-1, 0), (0, 1))
assert en[-1] == wn[-1] and int(en == en) != int(wn == en)
print("PASS REF2_6.3: final-direction quotient is valid; a non-pullback zero-step reward differs.")

# Check that no principal unconditional theorem/proposition statement was changed.
statements = {
    "sec1-result.tex": ("t:main",),
    "sec8-inputs.tex": ("t:H1", "t:inputs"),
    "app-input-contracts.tex": ("p:H2-test", "p:automaton10", "p:stationary-check"),
}
for filename, labels in statements.items():
    old = subprocess.check_output(["git", "show", f"HEAD:{filename}"], cwd=PAPER, text=True)
    new = (PAPER / filename).read_text()
    for label in labels:
        pattern = r"\\begin\{(theorem|proposition)\}\\label\{" + re.escape(label) + r"\}.*?\\end\{\1\}"
        original, edited = re.search(pattern, old, re.S), re.search(pattern, new, re.S)
        assert original is not None and edited is not None
        assert original.group() == edited.group(), label

sites = [
    (path.name, i, match.group(1))
    for path in sorted(PAPER.glob("*.tex"))
    for i, line in enumerate(path.read_text().splitlines(), 1)
    for match in re.finditer(r"\\certpending\{([^}]+)\}", line)
]
assert len(sites) == len({tag for _, _, tag in sites}) == 22
assert r"\newcommand{\certpending}[1]{\textbf{[certificate check pending]}}" in (PAPER / "main.tex").read_text()
assert 8439 + 2 + 3732 == 12173
assert 4 * 3741 * (19881 - 2) == 297469356
assert F(2 * 351207554 + 290599163, 10**9) < F(993015, 10**6)
assert F(527872005 + 380754375 + 273048088, 10**9) < F(993015, 10**6) * H
print("PASS scope: six unconditional statements unchanged; 22 unique pending-check sites.")
print("PASS arithmetic: block coverage, row count, and final assembly comparisons.")
