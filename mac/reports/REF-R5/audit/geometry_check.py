from fractions import Fraction as F

D = ((1, 0), (0, 1), (-1, 0), (0, -1))
windows = []
def gen(pos, word, bonds):
    if len(word) == 8:
        windows.append(word)
        return
    for d, step in enumerate(D):
        dest = (pos[0]+step[0], pos[1]+step[1])
        bond = frozenset((pos, dest))
        if bond not in bonds:
            gen(dest, word+(d,), bonds | {bond})
gen((0, 0), (), set())
orbits = {min(tuple((sign*d+r)%4 for d in word)
              for sign in (-1, 1) for r in range(4)) for word in windows}
print('Exact window and D4 orbit counts:', len(windows), len(orbits))

word = (1,)*28 + (2,)*26 + (3,) + (0,)*27 + (3,)*26
vertices = [(-1, 0)]
for d in word:
    vertices.append((vertices[-1][0]+D[d][0], vertices[-1][1]+D[d][1]))
bonds = [frozenset((a, b)) for a, b in zip(vertices, vertices[1:])]
assert len(bonds) == len(set(bonds))
assert (0, 0) not in vertices
assert vertices[-1] == (0, 1) and (0, 1) not in vertices[:-1]
assert vertices[54] == (-27, 28)
image_c = (-28, 28)
assert image_c not in vertices[:55]
print('Exact boundary example: n=108, row C, first N; passage 54 at', vertices[54],
      'arrival W, out S; unvisited live neighbour', image_c, 'is an image of c.')
print('Direction word: N^28 W^26 S E^27 S^26')

q = F('0.98075')
print('Exact comparison 0.85594872 <= q^8:', F('0.85594872') <= q**8)
scale = F('0.18094')/F('0.18093')
old = F('0.987730')*scale
print('Old-coefficient rescaling, displayed numerically:', float(old),
      '< 0.98779:', old < F('0.98779'))
hc = F.from_float(1.23)
print('h_C as exact binary64 rational:', hc)
print('Displayed C-row total is consistent with the final quotient:',
      F('1.191407')/hc < F('0.968624'))
print('Sum of displayed B subtotals:', sum(map(F, ('0.594580','0.026669','0.302932','0.057384','0.006199'))))
print('Sum of displayed C subtotals:', sum(map(F, ('0.841681','0.022644','0.268029','0.053319','0.005737'))))
