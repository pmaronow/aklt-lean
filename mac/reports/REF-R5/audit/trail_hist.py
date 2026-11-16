from fractions import Fraction as F
import csv

W = [[F(0), F(0)] for _ in range(16)]
ws, wt, wr = F(1000, 2883), F(200, 561), F(1, 5)
with open('audit/trail_hist.csv') as stream:
    for row in csv.DictReader(stream):
        n, s, t = (int(row[x]) for x in ('n', 'ns', 'nt'))
        weight = ws**s * wt**t * wr**(n-s-t)
        W[n][0] += int(row['all']) * weight
        W[n][1] += int(row['forbid_initial_reverse']) * weight
q = F(3923, 4000)  # 0.98075
print('All values below are exact-rational computations, displayed numerically.')
print('n W_all/q^n W_forbid_initial_reverse/q^n')
for n, (a, b) in enumerate(W):
    print(n, f'{float(a/q**n):.12f}', f'{float(b/q**n):.12f}')
for choice, tag in enumerate(('all', 'forbid_initial_reverse')):
    cv = max(max(W[n][choice]/q**n for n in range(8)),
             100*max(W[n][choice]/q**n for n in range(8, 16)))
    print('C_V using max h/min h = 100:', tag, float(cv), 'C_V <=153:', cv <= 153)
print('0.85594872 <= 0.98075^8:', F('0.85594872') <= q**8)
print('0.98075^8 =', float(q**8))
