"""Numerical sanity checks of the definitions; no Lean proofs are generated."""

import itertools
import json
import math
from pathlib import Path


phi = (1 + math.sqrt(5)) / 2
radius = math.sqrt(phi + 2)
vectors = [(0.0, 0.0, 0.0)]
for group, sign_a, sign_b in itertools.product(range(3), (1, -1), (1, -1)):
    a, b = sign_a, sign_b * phi
    raw = ((0, a, b), (a, b, 0), (b, 0, a))[group]
    vectors.append(tuple(c / radius for c in raw))


def dot(a, b):
    return math.fsum(x * y for x, y in zip(a, b))


def site_weight(status, letter):
    if letter == 0:
        return 0.4 if status == "D" else 0.0
    return 1 / 12 if status == "U" else 1 / 20


def factor(a, b):
    value = 1 + dot(a, b)
    assert value >= -1e-14
    # The exact factor is nonnegative. Remove antipodal roundoff only.
    return max(0.0, value)


def local_mean(status, fields):
    weights = [
        site_weight(status, letter)
        * math.prod(factor(vector, field) for field in fields)
        for letter, vector in enumerate(vectors)
    ]
    mass = math.fsum(weights)
    assert mass > 0
    mean = tuple(
        math.fsum(w * v[i] for w, v in zip(weights, vectors)) / mass
        for i in range(3)
    )
    return mass, mean


def check_network(statuses, bonds, pins, root, pinned):
    n = len(statuses)
    assert all(status in ("U", "D") for status in statuses)
    assert len(bonds) == len(set(bonds))
    assert all(a < b for a, b in bonds)
    assert all(
        sum(x in edge for edge in bonds) + len(pins.get(x, ())) <= 4
        for x in range(n)
    )
    assert not pins.get(root)
    incident = [edge for edge in bonds if root in edge]
    assert len(incident) <= 3
    outside = [x for x in range(n) if x != root]
    fibres = {}
    for config in itertools.product(range(13), repeat=n):
        weight = math.prod(site_weight(statuses[x], config[x]) for x in range(n))
        weight *= math.prod(
            factor(vectors[config[a]], vectors[config[b]]) for a, b in bonds
        )
        if pinned:
            weight *= math.prod(
                factor(pin, vectors[config[x]])
                for x, local_pins in pins.items()
                for pin in local_pins
            )
        key = tuple(config[x] for x in outside)
        entry = fibres.setdefault(key, [0.0, [0.0, 0.0, 0.0]])
        entry[0] += weight
        for i in range(3):
            entry[1][i] += weight * vectors[config[root]][i]

    partition = math.fsum(entry[0] for entry in fibres.values())
    assert partition > 0
    positive = zero = 0
    min_local_mass = math.inf
    max_error = 0.0
    for key, (mass, numerator) in fibres.items():
        if mass <= 1e-14:
            zero += 1
            continue
        positive += 1
        sigma = dict(zip(outside, key))
        fields = [
            vectors[sigma[b if a == root else a]] for a, b in incident
        ]
        assert all(dot(field, field) <= 1 + 1e-14 for field in fields)
        local_mass, expected_mean = local_mean(statuses[root], fields)
        # Explicitly perform both normalization divisions in the statement.
        normalized_event_mass = mass / partition
        conditional = tuple((value / partition) / normalized_event_mass for value in numerator)
        error = max(abs(a - b) for a, b in zip(conditional, expected_mean))
        assert error < 1e-12
        max_error = max(max_error, error)
        min_local_mass = min(min_local_mass, local_mass)
    return {
        "n": n,
        "root": root,
        "root_status": statuses[root],
        "degree": len(incident),
        "pinned": pinned,
        "positive_fibres_checked": positive,
        "zero_fibres_excluded": zero,
        "min_local_normalizer": min_local_mass,
        "max_coordinate_error": max_error,
    }


rows = []
for status, pinned in itertools.product(("U", "D"), (False, True)):
    # Zero incident factors and no outside coordinates.
    rows.append(check_network([status], [], {}, 0, pinned))
    # Both positions of the conditioned site in an ordered bond.
    rows.append(check_network([status, "U"], [(0, 1)], {}, 0, pinned))
    rows.append(check_network(["D", status], [(0, 1)], {}, 1, pinned))
    # An off-site bond and off-site pin create genuinely zero fibres.
    rows.append(
        check_network(
            ["U", status, "D"],
            [(0, 1), (0, 2), (1, 2)],
            {0: [vectors[1]]},
            1,
            pinned,
        )
    )
    # Three factors, with the root on both sides of ordered bonds.
    rows.append(
        check_network(
            ["U", status, "D", "U"],
            [(0, 1), (1, 2), (1, 3)],
            {0: [vectors[1]], 2: [vectors[2]], 3: [vectors[3]]},
            1,
            pinned,
        )
    )

result = {
    "kind": "floating-point sanity checks, not a formal proof",
    "roundoff_policy": "Clamp negative interaction factors of magnitude at most 1e-14 to zero; exclude fibre masses at most 1e-14.",
    "networks_checked": len(rows),
    "positive_fibres_checked": sum(row["positive_fibres_checked"] for row in rows),
    "zero_fibres_excluded": sum(row["zero_fibres_excluded"] for row in rows),
    "max_coordinate_error": max(row["max_coordinate_error"] for row in rows),
    "max_atom_normSq_error": max(abs(dot(v, v) - 1) for v in vectors[1:]),
    "cases": rows,
}
Path(__file__).with_name("checks.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({key: value for key, value in result.items() if key != "cases"}, indent=2))
