"""Finite sanity checks for TS_Q_06; these are not Lean proofs."""

from itertools import product
from math import prod, sqrt
from random import Random
import json


rng = Random(6006)
results = {}


def next_site(x, d, L, N):
    return ((x[0] + 1) % L, x[1]) if d == 0 else (x[0], (x[1] + 1) % N)


def neighbours(x, L, N):
    return {
        ((x[0] + 1) % L, x[1]),
        ((x[0] - 1) % L, x[1]),
        (x[0], (x[1] + 1) % N),
        (x[0], (x[1] - 1) % N),
    }


geometry_sites = 0
for L, N in product(range(3, 9), repeat=2):
    sites = list(product(range(L), range(N)))
    bonds = [(y, d) for y in sites for d in range(2)]
    for x in sites:
        incident = [(y, d) for y, d in bonds if x in {y, next_site(y, d, L, N)}]
        other = [next_site(y, d, L, N) if y == x else y for y, d in incident]
        assert len(incident) == len(set(other)) == 4
        assert set(other) == neighbours(x, L, N)
        assert x not in other
        assert sum(y != x for y, d in incident) == 2
        geometry_sites += 1
results['geometry'] = {'sizes': '3 <= L,N <= 8', 'sites_checked': geometry_sites}

letters = list(product(range(3), range(2), range(2)))
phi = (1 + sqrt(5)) / 2
radius = sqrt(phi + 2)


def vector(j, letter):
    k, s, t = letter
    a = 1 if s == 0 else -1
    b = (1 if t == 0 else -1) * phi
    v = [(0, a, b), (a, b, 0), (b, 0, a)][k]
    x, y, z = [u / radius for u in v]
    for _ in range(j):
        x, y = (99*x - 20*y)/101, (20*x + 99*y)/101
    return x, y, z


def spinor(j, letter):
    x, y, z = vector(j, letter)
    if z == -1:
        return 0j, 1 + 0j
    return sqrt((1 + z)/2) + 0j, (x + 1j*y)/sqrt(2*(1 + z))


spinors = {(j, a): spinor(j, a) for j in range(3) for a in letters}


def det(z, w):
    return z[0]*w[1] - z[1]*w[0]


minimum = min(
    abs(det(spinors[i, a], spinors[j, b]))**2
    for i, j in product(range(3), repeat=2) if i != j
    for a, b in product(letters, repeat=2)
)
assert minimum > 0
assert abs(minimum - (5-sqrt(5))/1010) < 1e-14
results['frame_separation'] = {'ordered_frame_letter_pairs': 6*12*12, 'min_det_normSq': minimum}


def close(a, b, scale=1):
    assert abs(a-b) < 2e-10 * max(scale, abs(a), abs(b)), (a, b)


L = N = 3
sites = list(product(range(L), range(N)))
bonds = [(x, d) for x in sites for d in range(2)]
kappa = {x: (x[0]+x[1]) % 3 for x in sites}
assert all(kappa[x] != kappa[next_site(x, d, L, N)] for x, d in bonds)
q = 5/12


def sample_complex():
    return rng.uniform(-2, 2) + 1j*rng.uniform(-2, 2)


def edge_value(e, sigma, colours):
    y, d = e
    z = next_site(y, d, L, N)
    return det(spinors[colours[y], sigma[y]], spinors[colours[z], sigma[z]])


def beta(x, sigma, colours):
    return prod(det(spinors[colours[x], sigma[x]], spinors[colours[y], sigma[y]])
                for y in neighbours(x, L, N))


def rho(x, sigma, colours):
    sign = prod(1 if y == x else -1 for y, d in bonds if x in {y, next_site(y, d, L, N)})
    return sign * prod(edge_value(e, sigma, colours) for e in bonds
                       if x not in {e[0], next_site(e[0], e[1], L, N)})


for iteration in range(100):
    sigma = {y: rng.choice(letters) for y in sites}
    x = rng.choice(sites)
    # Factorization also holds for arbitrary, possibly improper colourings.
    colours = kappa if iteration < 50 else {y: rng.randrange(3) for y in sites}
    full = prod(edge_value(e, sigma, colours) for e in bonds)
    close(full, beta(x, sigma, colours)*rho(x, sigma, colours))
    original_rho = rho(x, sigma, colours)
    for a in letters:
        updated = dict(sigma)
        updated[x] = a
        close(rho(x, updated, colours), original_rho)

    # Fibre formulas use a proper colouring, making every beta and rho nonzero.
    updates = [dict(sigma, **{}) for _ in letters]
    for updated, a in zip(updates, letters):
        updated[x] = a
    betas = [beta(x, updated, kappa) for updated in updates]
    rhos = [rho(x, updated, kappa) for updated in updates]
    assert all(abs(b) > 0 for b in betas)
    assert all(abs(r) > 0 for r in rhos)
    D = sum(q*abs(b)**2 for b in betas)
    assert D > 0

    def projection(h):
        coeff = sum(q*b.conjugate()*v for b, v in zip(betas, h))/D
        return [b*coeff for b in betas]

    h = [sample_complex() for _ in letters]
    ph = projection(h)
    close(sum(q*b.conjugate()*(v-p) for b, v, p in zip(betas, h, ph)), 0)
    c = sample_complex()
    k = [c*b for b in betas]
    for pk, value in zip(projection(k), k):
        close(pk, value)
    distance = sum(q*abs(v-p)**2 for v, p in zip(h, ph))
    competitor = sum(q*abs(v-value)**2 for v, value in zip(h, k))
    correction = sum(q*abs(p-value)**2 for p, value in zip(ph, k))
    close(competitor, distance + correction)
    assert distance <= competitor + 1e-10

    # The global reference is constant on a fibre; its outside factor cancels.
    bvals = [b*r for b, r in zip(betas, rhos)]
    norm_B = 2.7
    reference = q**len(sites)
    mu = [reference*abs(b)**2/norm_B**2 for b in bvals]
    f = [sample_complex() for _ in letters]
    ef = sum(p*v for p, v in zip(mu, f))/sum(mu)
    uf = [v*b/norm_B for v, b in zip(f, bvals)]
    puf = projection(uf)
    for actual, b in zip(puf, bvals):
        close(actual, ef*b/norm_B)
    close(sum(reference*abs(u)**2 for u in uf), sum(p*abs(v)**2 for p, v in zip(mu, f)))
    close(sum(p*abs(v-ef)**2 for p, v in zip(mu, f)),
          sum(reference*abs(u-p)**2 for u, p in zip(uf, puf)))

results['fibre_checks'] = {'random_seed': 6006, 'samples': 100, 'letters_per_fibre': 12,
                           'identities': ['incident orientation and factorization', 'rho invariance',
                                          'projection fixed point and least squares',
                                          'intertwining', 'norm and Dirichlet identities']}

# A signed-weight isometry verifies that positivity is unnecessary for polarization.
w = [1, 1, -1]


def E(v):
    return [v[0], sqrt(2)*v[1], v[1]]


for _ in range(100):
    v = [sample_complex(), sample_complex()]
    t = [sample_complex(), sample_complex()]
    ev, et = E(v), E(t)
    close(sum(p*abs(z)**2 for p, z in zip(w, ev)), sum(abs(z)**2 for z in v))
    close(sum(p*z.conjugate()*u for p, z, u in zip(w, ev, et)),
          sum(z.conjugate()*u for z, u in zip(v, t)))

B = [1+1j, 2-1j]
psi = [-B[1].conjugate(), B[0].conjugate()]
eb, ep = E(B), E(psi)
norm_B = sqrt(sum(abs(z)**2 for z in B))
mu = [p*abs(z)**2/norm_B**2 for p, z in zip(w, eb)]
f = [norm_B*p/b for p, b in zip(ep, eb)]
mean = sum(p*z for p, z in zip(mu, f))
close(mean, 0)
close(sum(p*abs(z-mean)**2 for p, z in zip(mu, f)), sum(abs(z)**2 for z in psi))
results['signed_weight_algebra'] = {'polarization_samples': 100, 'quotient_mean_and_variance': 'passed',
                                   'note': 'abstract algebra check; these signed weights are not torusLaw'}

print(json.dumps(results, indent=2))
