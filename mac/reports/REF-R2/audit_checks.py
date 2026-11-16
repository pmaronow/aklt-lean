"""Small exact checks for referee lane R2; no manuscript programs are run."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
import json
from pathlib import Path


def main():
    counts = {"sum_identities": 0, "autocorrelation_sequences": 0,
              "periodic_autocorrelation_cases": 0, "shell_index_cases": 0}
    for n in range(2, 101):
        u = [j * (n + 1 - j) for j in range(1, n + 1)]
        ss = sum(u)
        r0 = sum(x*x for x in u)
        r1 = sum(u[j]*u[j+1] for j in range(n-1))
        assert ss == F(n*(n+1)*(n+2), 6)
        assert r0 == F(n*(n+1)*(n+2)*(n*n+2*n+2), 30)
        assert r1 == F((n-1)*n*(n+1)*(n+2)*(n+3), 30)
        assert r0-r1 == ss
        threshold = F(n*n*r0*(r0-r1), ss**4)
        prefactor = F(ss**4, n*n*r0*r1)
        assert threshold == F(36*(n*n+2*n+2), 5*(n+1)**2*(n+2)**2)
        assert prefactor == F(25*(n+1)**2*(n+2)**2,
                              36*(n-1)*(n+3)*(n*n+2*n+2))
        counts["sum_identities"] += 1

    for n in range(2, 11):
        for half in combinations_with_replacement(range(4), (n+1)//2):
            u = list(half) + list(half[:-1] if n % 2 else half)[::-1]
            r = [sum(u[j]*u[j+k] for j in range(n-k)) for k in range(n)]
            assert all(r[k] >= r[k+1] for k in range(n-1))
            counts["autocorrelation_sequences"] += 1
            for circumference in range(n+1, 2*n+3):
                cyclic = [0] + u + [0]*(circumference-n-1)
                rr = [sum(cyclic[j]*cyclic[(j+k) % circumference]
                          for j in range(circumference))
                      for k in range(circumference)]
                assert rr[0] == r[0] and rr[1] == rr[-1] == r[1]
                assert all(rr[k] <= r[1] for k in range(2, circumference-1))
                counts["periodic_autocorrelation_cases"] += 1

    for snum in range(16, 401):
        s = F(snum, 4)
        i1 = s.numerator // s.denominator + 1
        for bad in [None] + list(range(2, i1+1)):
            good_trials = [i for i in range(2, i1) if i != bad and i+1 != bad]
            assert len(good_trials) >= s-4
            assert all(i <= s for i in good_trials)
            assert (i1-1)*s <= s*s
            counts["shell_index_cases"] += 1

    # Every arithmetic comparison here uses rational numbers, not binary floats.
    assert F(1,1)/F('0.82') <= F('1.22')
    assert F(2,1)/F('0.734') <= F('2.73')
    assert F('0.7776')/(15*F('0.734')) <= F('0.0707')
    assert 1-F(3*9, 6*25) == F('0.82')
    assert 1-F(4*9, 6*25)-F(3,15)*F(9,25)**2 >= F('0.734')
    assert F(1)-F(9,125) == F('0.928')
    assert F(1)+F(9,125) == F('1.072')
    assert F(961,1000) == F('0.961') and F(187,200) == F('0.935')
    assert 1-F(169,385)**2/3 == F(416114,444675)
    assert F('0.98777') < F('0.98779') < 1
    assert F('0.85594872') <= F('0.98075')**8
    counts["t8_exact"] = str(F(36*(8*8+2*8+2),5*9**2*10**2))
    print(json.dumps(counts, indent=2))


if __name__ == '__main__':
    main()
