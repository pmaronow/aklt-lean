"""Lemma: for unit a, b, c the mean of the density prop. to (1+n.a)(1+n.b)(1+n.c) on S^2 has |mu| <= 3/5 (agent 57).
15*Z*mu = 5(a+b+c) + a(b.c) + b(a.c) + c(a.b) =: V,  15*Z = 15 + 5(a.b+a.c+b.c).  |mu| <= 3/5  <=>  |V| <= 9 + 3s,
s = a.b + a.c + b.c.  With x = b.c, y = a.c, z = a.b:  f := (9 + 3(x+y+z))^2 - |V|^2 >= 0 is checked symbolically."""
import sympy as sp
x, y, z = sp.symbols('x y z', real=True)
al, be, ga = 5 + x, 5 + y, 5 + z
V2 = al**2 + be**2 + ga**2 + 2*al*be*z + 2*al*ga*y + 2*be*ga*x
f = sp.expand((9 + 3*(x + y + z))**2 - V2)
print('f =', f)
print('factor:', sp.factor(f))
# Gram determinant of (a,b,c): 1 - x^2 - y^2 - z^2 + 2xyz >= 0
g = 1 - x**2 - y**2 - z**2 + 2*x*y*z
# try f = A*(1-x)(1-y)(1-z)-type decompositions numerically: check min of f on the elliptope by a dense grid
import numpy as np
F = sp.lambdify((x, y, z), f, 'numpy'); G = sp.lambdify((x, y, z), g, 'numpy')
t = np.linspace(-1, 1, 201)
X, Y, Z = np.meshgrid(t, t, t, indexing='ij')
mask = G(X, Y, Z) >= -1e-12
vals = F(X, Y, Z)
print('min f on elliptope grid', vals[mask].min(), ' min f on whole cube', vals.min())
