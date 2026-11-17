from pathlib import Path
import re

ROOT = Path('/home/ubuntu/aklt/reports/REV-PLAN')
S = []
def add(section, label, title, owner, status, source, deps, body, interface=False, note=''):
    S.append(dict(section=section, label=label, title=title, owner=owner,
                  status=status, source=source, deps=deps, body=body.strip(),
                  interface=interface, note=note))

add('1. Result and conventions', 'd:model', 'The torus Hamiltonian', 'A',
    'kept with edits', 'baseline e:H and e:B; STRENGTHEN-ALL §1', [],
r"""
\begin{definition}\label{d:model}
For integers \(L,N\ge3\), let \(\Lambda=\Lambda_{L,N}=\mathbb Z_L\times\mathbb Z_N\)
with its simple, unoriented nearest-neighbour edge set \(E_{L,N}\).
The Hilbert space is \(\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}V_4\).
Each site carries the spin-\(2\) space \(V_4\), and \(P_{\{x,y\}}\)
is the orthogonal projection onto total spin \(4\) in \(V_4\otimes V_4\).
Fix one orientation of each edge and set
\[
 q_{xy}=z_{x,1}z_{y,2}-z_{x,2}z_{y,1},\qquad
 B_{L,N}=\prod_{e\in E_{L,N}}q_e,\qquad
 H_{L,N}=\sum_{e\in E_{L,N}}P_e.
\]
Every edge is counted once. The spectral gap of \(H_{L,N}\) means its
smallest positive eigenvalue.
\end{definition}
""", True)

add('1. Result and conventions', 't:main', 'Unconditional main theorem', 'A',
    'replaces baseline t:main', 'STRENGTHEN-ALL t:main, restricted to the author’s scope', ['p:toruskernel','t:mainW','t:cutMOS','t:rec','t:inputs'],
r"""
\begin{theorem}\label{t:main}
For every \(L,N\ge3\), \(B_{L,N}\ne0\) and
\(\ker H_{L,N}=\mathbb C B_{L,N}\).
There exist \(c>0\) and an integer \(L_0\ge3\) such that, for all
integers \(L,N\ge L_0\), every nonzero eigenvalue of \(H_{L,N}\)
is at least \(c\).
\end{theorem}
""", note='No hypotheses appear in this theorem. The certified-input theorems must be proved before the manuscript is accepted; this plan is not a claim that their redesigned Lean certificates already exist.')

add('2. Finite moment algebra and the response input', 'd:moment', 'The finite fourth-moment functional', 'C',
    'new; replaces spherical integration in the core', 'OPPORTUNITIES #2; STRENGTHEN-ALL e:threeframes', [],
r"""
\begin{definition}\label{d:moment}
Write \(\mathbb S^2=\{a\in\mathbb R^3:|a|=1\}\), put
\(\phi=(1+\sqrt5)/2\), \(r=\sqrt{\phi+2}\), and set
\[
 D=\frac1r\{(0,\pm1,\pm\phi),(\pm1,\pm\phi,0),(\pm\phi,0,\pm1)\},
 \qquad
 \mathcal M(f)=\frac1{12}\sum_{a\in D}f(a).
\]
All indicated signs are independent. Define finite probability laws
\(\lambda_{\mathrm U}=\frac1{12}\sum_{a\in D}\delta_a\) and
\(\lambda_{\mathrm D}=\frac35\lambda_{\mathrm U}+\frac25\delta_0\).
Products of these functionals always mean finite sums.
For plane sites, \(d\) denotes ambient \(\ell^1\) distance and
\(\operatorname{dist}_\infty\) denotes ambient \(\ell^\infty\) distance.
Distances to an empty set are \(+\infty\); a product over an empty site
set has its one empty configuration. For finite probabilities, use
\[
 d_{\rm TV}(p,p')=\tfrac12\sum_z|p(z)-p'(z)|,\qquad
 \operatorname{Var}_\mu f=\mu(|f-\mu f|^2),\qquad
 d_H(n,n')=\sum_x\mathbf1_{\{n_x\ne n'_x\}} .
\]
\end{definition}
""", True)

add('2. Finite moment algebra and the response input', 'l:moments', 'Moments and bounded-degree covariance', 'C',
    'replaces baseline e:moments and its all-orders Gaussian proof', 'OPPORTUNITIES #2; STRENGTHEN-ALL l:threeframes', ['d:moment'],
r"""
\begin{lemma}\label{l:moments}
The set \(D\) has twelve distinct unit vectors and is antipodal.
For \(i,j,k,l\in\{1,2,3\}\),
\[
 \begin{gathered}
 \mathcal M(1)=1,\qquad \mathcal M(n_i)=\mathcal M(n_in_jn_k)=0,\qquad
 \mathcal M(n_in_j)=\delta_{ij}/3,\\
 \mathcal M(n_in_jn_kn_l)=
 (\delta_{ij}\delta_{kl}+\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk})/15.
 \end{gathered}
\]
For every polynomial \(p\) of total degree at most four and every
\(R\in\mathrm O(3)\), \(\mathcal M(p\circ R)=\mathcal M(p)\).
The same covariance holds for \(\lambda_{\mathrm D}\); its constant
moment is one and its moments of positive degree at most four are
\(3/5\) times those displayed above.
These assertions hold site by site for polynomials of separate degree
at most four in a finite product of spins.
\end{lemma}
""", True, 'Covariance is a polynomial identity on the stated degree range. It is not invariance of the finite law for arbitrary functions.')

add('2. Finite moment algebra and the response input', 'd:pinmodel', 'Original legs, removals, and finite partition sums', 'C',
    'kept with edits', 'baseline s:contmodel, e:Zpin; OPPORTUNITIES #2', ['d:moment'],
r"""
\begin{definition}\label{d:pinmodel}
For finite \(G\subset\mathbb Z^2\), let
\[
 \mathcal L(G)=\{(x,z):x\in G,\ z\notin G,\ d(x,z)=1\},\qquad
 S(G)=\{x\in G:d(x,\mathbb Z^2\setminus G)\le2\}.
\]
A pin assignment is \(\tau\in(\mathbb S^2)^{\mathcal L(G)}\).
For \(Y\subset G\), write \(D_Y=G\setminus Y\) and define
\[
 Z^\tau_{D_Y}[f]=
 \sum_{n\in D^{D_Y}}12^{-|D_Y|}f(n)
 \prod_{\substack{\{x,y\}\subset D_Y\\d(x,y)=1}}(1+n_x\cdot n_y)
 \prod_{\substack{(x,z)\in\mathcal L(G)\\x\in D_Y}}
       (1+\tau_{xz}\cdot n_x).
\]
The free sum \(Z^0_{D_Y}[f]\) omits all leg factors.
Write \(Z^\bullet_{D_Y}=Z^\bullet_{D_Y}[1]\),
\(\mathbb E^\bullet_{D_Y}f=Z^\bullet_{D_Y}[f]/Z^\bullet_{D_Y}\),
and \(\Psi_{D_Y}(\tau)=Z^\tau_{D_Y}/Z^0_{D_Y}\).
Here and below \(\bullet\) is either \(\tau\) or \(0\).
The empty partition sum is one. There are no new factors on legs into \(Y\).
Different original legs may carry unrelated unit pins, even if their
outside endpoints coincide.
\end{definition}
""", True)

add('2. Finite moment algebra and the response input', 'l:finitefacts', 'Positivity and the admissible free-positivity statement', 'C',
    'kept with edits; narrows unused observable generality', 'baseline s:contmodel and s:domains; OPPORTUNITIES #2', ['d:moment','l:moments','d:pinmodel'],
r"""
\begin{lemma}\label{l:finitefacts}
Consider a finite network with site laws \(\lambda_{\mathrm U}\) or
\(\lambda_{\mathrm D}\), retained distinct-endpoint bonds
\(1+n_x\cdot n_y\), and retained original unit-pin factors
\(1+\tau_\ell\cdot n_x\), with at most four factors incident to each site.
Its pinned and free partition sums are strictly positive, including
the empty network. Non-neighbours are conditionally independent given
the other spins on every conditioning event of positive probability.
If \(f\) is a product of scalar products of spins and the product of
\(f\) with the bond factors has separate degree at most four at every
site, then \(Z^0[f]\ge0\), hence \(\mathbb E^0 f\ge0\).
All normalized spins have norm at most one.
\end{lemma}
""", True, 'A finite positivity proof selects unit letters successively: each incident factor forbids at most one of twelve letters. Free positivity uses only the displayed second and fourth moment tensors.')

add('2. Finite moment algebra and the response input', 'l:35', 'The three-factor mean bound and covering tips', 'C',
    'kept with edits', 'baseline l:35 and the tip-covering argument in l:local; OPPORTUNITIES #2/#21', ['l:moments','l:finitefacts'],
r"""
\begin{lemma}\label{l:35}
For \(0\le k\le3\) and \(|a_j|\le1\), the probability law proportional to
\(\prod_{j=1}^k(1+n\cdot a_j)\lambda_{\mathrm U}(\mathrm dn)\)
has mean of norm at most \(3/5\). The same bound holds with
\(\lambda_{\mathrm D}\) in place of \(\lambda_{\mathrm U}\).
Moreover,
\[
 \left\{
 \frac{\mathcal M\!\left(n\prod_{j=1}^3(1+n\cdot a_j)\right)}
      {\mathcal M\!\left(\prod_{j=1}^3(1+n\cdot a_j)\right)}
       :a_1,a_2,a_3\in\mathbb S^2
 \right\}=\{b\in\mathbb R^3:|b|\le3/5\}.
\]
Consequently an unpinned site having at most three present factors
has conditional mean of norm at most \(3/5\), on every positive
conditioning fibre.
\end{lemma}
""", True, 'Keep the elementary sum-of-squares proof of the 3/5 bound. The range assertion uses the degree-four mean formula, a zero-mean triple, an aligned triple, continuity, and polynomial covariance. It does not use the deleted FKG radius lemma.')

add('2. Finite moment algebra and the response input', 'l:exact', 'Finite quadrature, with its precise degree limit', 'C',
    'kept with edits', 'baseline l:exact; STRENGTHEN-ALL l:exact; OPPORTUNITIES #2', ['l:moments'],
r"""
\begin{lemma}\label{l:exact}
At each site of a finite set choose any positive weighted unit-vector
law whose moments through degree four equal those of \(\mathcal M\).
A polynomial of separate degree at most four has the same product
functional under these laws as under \(\lambda_{\mathrm U}\) at all
sites. The analogous assertion holds after replacing any chosen site
laws by \(3/5\) times that law plus \(2/5\,\delta_0\).
In particular this applies to partition products of factors
\(1\pm n_x\cdot n_y\) and \(1\pm n_x\cdot a\), \(|a|=1\), whenever
each variable occurs at most four times, and to inserted observables
only when their degrees are included in this same bound.
\end{lemma}
""", True, 'This transfers summed-out partition functions. It does not identify window laws on different alphabets or arbitrary observable expectations.')

add('2. Finite moment algebra and the response input', 'h:P', 'The response statement passed from C to B', 'C',
    'kept with edits', 'baseline h:P/e:P; OPPORTUNITIES #2/#20', ['d:pinmodel'],
r"""
\begin{definition}[(P)]\label{h:P}
For \(A\ge2\) and \(0<\theta<1\), property \(\mathsf P(A,\theta)\)
means that, for every finite \(G\subset\mathbb Z^2\), every unit-pin
assignment on \(\mathcal L(G)\), every
\(Y\subset G\setminus S(G)\), and all \(u,v\in G\setminus Y\) with
\(d(u,v)=2\) and a common neighbour in \(Y\),
\[
 \left|\mathbb E^\tau_{G\setminus Y}(n_u\cdot n_v)
             -\mathbb E^0_{G\setminus Y}(n_u\cdot n_v)\right|
 \le A\theta^{\min\{d(u,S(G)),d(v,S(G))\}} .
\]
The distances are ambient plane distances to the original \(S(G)\);
removed sites are not added to the boundary.
\end{definition}
""", True)

add('3. The quantum model, uniqueness, and positive frames', 'd:poly', 'Polynomial normalization without a sphere integral', 'A',
    'replaces baseline e:Vinner and the global spinor choice', 'OPPORTUNITIES #2/#6; baseline s:poly', [],
r"""
\begin{definition}\label{d:poly}
Let \(V_d\) be the homogeneous binary polynomials of degree \(d\).
Its monomials \(z_1^{d-j}z_2^j\), \(0\le j\le d\), are orthogonal with
squared norms \(\binom dj^{-1}\). The action is
\((U_gp)(z)=p(g^{-1}z)\). Use \(V_4\) at each physical site.
For each of the finitely many frame letters \(a\) choose one unit
spinor \(\zeta(a)\in\mathbb C^2\) with
\(\zeta(a)\zeta(a)^*=(I+a\cdot\sigma)/2\).
No spinor choice on the whole sphere is part of the definitions.
\end{definition}
""", True)

add('3. The quantum model, uniqueness, and positive frames', 'l:edge', 'The edge kernel', 'A',
    'kept as is (with the torus understood)', 'baseline l:edge; Cartan proof from OPPORTUNITIES #6', ['d:model','d:poly'],
r"""
\begin{lemma}\label{l:edge}
For \(e=\{x,y\}\) and \(\varphi\in\mathcal H_\Lambda\),
\(P_e\varphi=0\) if and only if
\(\varphi=q_e\chi\), where \(\chi\) is homogeneous of degree three
in \(z_x,z_y\) and degree four in every other site variable.
\end{lemma}
""", note='Use the Cartan map p(z_x,z_y) -> p(z,z): it is onto V_8, its kernel is the 16-dimensional determinant image, and its adjoint image is the total-spin-4 space. This is the chosen proof path; no full Clebsch–Gordan decomposition is required.')

add('3. The quantum model, uniqueness, and positive frames', 'l:divisibility', 'Local divisibility on the torus', 'A',
    'kept with edits (torus scope only)', 'baseline l:divisibility; STRENGTHEN-ALL p:graphkernel algebra', ['l:edge'],
r"""
\begin{lemma}\label{l:divisibility}
Let \(L,N\ge3\), \(R\subset\Lambda_{L,N}\), and
\(E_R=\{e\in E_{L,N}:e\cap R\ne\varnothing\}\).
If \(\varphi\in\mathcal H_\Lambda\) and \(P_e\varphi=0\)
for every \(e\in E_R\), then
\(\varphi=(\prod_{e\in E_R}q_e)\chi\), where \(\chi\) is independent
of every \(z_x\), \(x\in R\).
\end{lemma}
""")

add('3. The quantum model, uniqueness, and positive frames', 'p:toruskernel', 'Uniqueness at every stated size', 'A',
    'new; replaces the all-graph strengthening by its torus specialization', 'STRENGTHEN-ALL p:graphkernel; REF-SA-A', ['l:divisibility'],
r"""
\begin{proposition}\label{p:toruskernel}
For every \(L,N\ge3\), the torus is simple and has four distinct
neighbours at each site, \(B_{L,N}\ne0\), and
\(\ker H_{L,N}=\mathbb C B_{L,N}\).
Changing edge orientations does not change this one-dimensional space.
\end{proposition}
""", note='Take R equal to the torus. This proof has no frame, mixing, or computer-assisted premise. State no general-graph ground-space theorem.')

add('3. The quantum model, uniqueness, and positive frames', 'l:star', 'The fixed star comparison', 'A',
    'kept as is (promoted from e:star)', 'baseline e:star; REF-SA-A finding 2', ['l:edge'],
r"""
\begin{lemma}\label{l:star}
Let \(h_\star=\sum_{j=1}^4P_{\{0,j\}}\) on \(V_4^{\otimes5}\).
Its smallest positive eigenvalue \(g_\star\) exists and is positive.
For \(L,N\ge3\), set \(H_x=\sum_{e\ni x}P_e\) and
\(\mathcal S_x=\ker H_x\). Then
\[
 H_x\ge g_\star(I-\Pi_{\mathcal S_x}),\qquad
 \sum_xH_x=2H_{L,N}.
\]
\end{lemma}
""")

add('3. The quantum model, uniqueness, and positive frames', 'd:frame', 'Finite moment frames', 'A',
    'kept with edits', 'baseline d:frame; OPPORTUNITIES #2', ['d:moment'],
r"""
\begin{definition}\label{d:frame}
A frame is a finite set \(A\subset\mathbb S^2\) with positive weights
\(w(a)\) summing to one such that
\(\sum_{a\in A}w(a)p(a)=\mathcal M(p)\)
for every real polynomial \(p\) of degree at most four.
\end{definition}
""", True)

add('3. The quantum model, uniqueness, and positive frames', 'l:tight', 'The coherent-state tight frame identity', 'A',
    'kept as is', 'baseline l:tight, with algebraic norm verification from OPPORTUNITIES #2', ['d:poly','d:frame','l:moments'],
r"""
\begin{lemma}\label{l:tight}
For every frame \((A,w)\) and every \(p\in V_4\),
\[
 \sum_{a\in A}5w(a)|p(\zeta(a))|^2=\|p\|_{V_4}^2.
\]
For site frames \((D_x,w_x)\), set \(\Omega=\prod_xD_x\),
\(\pi(s)=\prod_x5w_x(s_x)\), and
\(\iota\varphi(s)=\varphi((\zeta(s_x))_x)\).
Then \(\iota:\mathcal H_\Lambda\to\ell^2(\Omega,\pi)\) is an isometry.
\end{lemma}
""", True)

add('3. The quantum model, uniqueness, and positive frames', 'l:threeframes', 'The three rotated icosahedra', 'A',
    'replaces baseline e:icodod and the dodecahedral construction', 'STRENGTHEN-ALL l:threeframes; REF-SA-A', ['d:moment','l:moments','d:frame'],
r"""
\begin{lemma}\label{l:threeframes}
Let
\[
 T=\begin{pmatrix}99/101&-20/101&0\\20/101&99/101&0\\0&0&1\end{pmatrix},
 \quad D^{(j)}=T^jD\ (j=0,1,2),\quad
 b=\frac{5-\sqrt5}{505},\quad r_b=\frac b{2-b}.
\]
The matrix \(T\) is in \(\mathrm{SO}(3)\).
Each \(D^{(j)}\), with uniform weights \(1/12\), is an antipodal frame.
For \(i\ne j\), \(a\in D^{(i)}\), \(a'\in D^{(j)}\),
\[
 0<b<1,\qquad b\le1\pm a\cdot a'\le2-b,\qquad0<r_b<1.
\]
The common lower bound \(b\) is attained, and distinct frames are
disjoint even up to antipodal signs.
\end{lemma}
""", True)

add('3. The quantum model, uniqueness, and positive frames', 'l:colour', 'A proper colouring for all tori', 'A',
    'new', 'STRENGTHEN-ALL l:colour; REF-SA-A', ['d:model'],
r"""
\begin{lemma}\label{l:colour}
For \(m\ge3\) and representatives \(0\le i<m\), put
\[
 a_m(i)=\begin{cases}2,&m\text{ odd and }i=m-1,\\i\bmod2,&\text{otherwise}.
 \end{cases}
\]
Then \(\kappa(i,j)=a_L(i)+a_N(j)\pmod3\) is a proper
three-colouring of \(\Lambda_{L,N}\) for every \(L,N\ge3\).
\end{lemma}
""")

add('3. The quantum model, uniqueness, and positive frames', 'd:framemodel', 'The torus and plane frame specifications', 'A',
    'kept with edits; replaces e:muD and e:QDrot', 'STRENGTHEN-ALL e:mucirc/e:muDW; OPPORTUNITIES #16', ['l:threeframes','d:model','d:poly','l:tight'],
r"""
\begin{definition}\label{d:framemodel}
Given any proper three-colouring \(\kappa\) of a plane or torus,
put \(D_x=D^{(\kappa(x))}\), with weights \(1/12\).
On the torus define
\[
 \mu^{\mathrm{af}}_{\kappa,L,N}(s)=
 \frac1{Z^{\mathrm{af}}}\prod_x\frac1{12}
       \prod_{\{x,y\}\in E_{L,N}}(1-s_x\cdot s_y).
\]
On the plane, for finite \(W\subset\mathbb Z^2\) and
\(\eta_z\in D_z\) at exterior neighbour sites, define
\[
 \mu^{+,\eta}_{\kappa,W}(n)=\frac1{Z^{+,\eta}_{\kappa,W}}
 \prod_{x\in W}\frac1{12}
 \prod_{\substack{\{x,y\}\subset W\\d(x,y)=1}}(1+n_x\cdot n_y)
 \prod_{\substack{x\in W,z\notin W\\d(x,z)=1}}(1+n_x\cdot\eta_z).
\]
Only the finitely many needed exterior letters are specified.
These laws have full support. Write \(E_U\) for conditioning off \(U\),
\(\operatorname{Var}_U f=E_U|f-E_Uf|^2\), and
\[
 \mathcal D_\mu(f)=\sum_x\mu(\operatorname{Var}_x f),\qquad
 \lambda(\mu)=\inf_{\operatorname{Var}_\mu f>0}
             \frac{\mathcal D_\mu(f)}{\operatorname{Var}_\mu f}.
\]
All generators have one update per physical site. A gap lower bound is
always equivalently a Poincare inequality, including one-point spaces.
\end{definition}
""", True)

add('3. The quantum model, uniqueness, and positive frames', 't:QD', 'Quantum to classical comparison on every torus', 'A',
    'kept with edits', 'baseline t:QD/e:QDcomp; STRENGTHEN-ALL t:QD; REF-SA-A', ['l:star','l:divisibility','l:tight','d:framemodel','l:threeframes'],
r"""
\begin{theorem}\label{t:QD}
For every \(L,N\ge3\) and every proper torus three-colouring,
\[
 \mu^{\mathrm{af}}(s)=
 \frac{\pi(s)|\iota B_{L,N}(s)|^2}{\|B_{L,N}\|^2},\qquad
 H_{L,N}\big|_{B_{L,N}^{\perp}}\ge
       \frac{g_\star}{2}\lambda(\mu^{\mathrm{af}})I .
\]
In particular
\(\operatorname{gap}(H_{L,N})\ge(g_\star/2)\lambda(\mu^{\mathrm{af}})\).
\end{theorem}
""", note='Retain the orientation factor c_x = product of epsilon_{e,x} in both local factorizations, the squared modulus, unnormalized reference measure pi, and the inclusion of quantum local ground vectors in the classical fibre range. Do not strengthen that inclusion to equality.')

add('3. The quantum model, uniqueness, and positive frames', 'l:planeenergy', 'Uniform finite energy and conditional consistency', 'A',
    'replaces the cell finite-energy and local comparison constants', 'STRENGTHEN-ALL e:energy; OPPORTUNITIES #7/#16; MOSPROOF lem:spec', ['d:framemodel','l:threeframes'],
r"""
\begin{lemma}\label{l:planeenergy}
All the frame specifications above are consistent under conditioning
and have nearest-neighbour Markov dependence. Uniformly over proper
colourings, finite volumes, admissible frame-valued boundaries, and
fully specified one-site fibres, every letter has conditional
probability at least
\[
 \alpha=\frac1{12}r_b^4\in(0,1].
\]
The same lower bound holds after conditioning on fewer letters.
Any prescribed assignment on \(k\) sites, under arbitrary consistent
partial conditioning off those sites, has conditional probability
at least \(\alpha^k\).
For a finite plane block \(Q\), every conditional single-site
heat-bath law in \(Q\) has Poincare gap at least
\(r_b^{|E(Q)|}\), where \(E(Q)\) is its internal edge set.
\end{lemma}
""", True, 'Use the density comparison of l:density: absorb all boundary factors into a positive product reference law. Only internal bonds enter the density ratio. No finite-energy bound is claimed for arbitrary unit-vector pins.')

add('3. The quantum model, uniqueness, and positive frames', 'l:boxlift', 'Local gauge for a lifted physical square', 'A',
    'replaces baseline l:boxcell and r:Kpins', 'STRENGTHEN-ALL l:boxcell/e:localgauge; OPPORTUNITIES #1/#16', ['d:framemodel','l:threeframes'],
r"""
\begin{lemma}\label{l:boxlift}
Let \(Q'=a+\{-M,\ldots,M\}^2\subset\mathbb Z^2\), \(M\ge1\),
and \(L,N\ge2M+3\). Reduction modulo the periods is injective
on the \(\ell^\infty\) one-neighbourhood of \(Q'\), preserves exactly
the internal nearest-neighbour edges of \(Q'\), and identifies all its
crossing bonds with the torus crossing bonds of its image \(Q\).
For every torus outside configuration \(\sigma\), pull back the
colouring and set
\[
 n_z=(-1)^{z_1+z_2}s_{p(z)}\quad(z\in Q'),\qquad
 \eta_z=(-1)^{z_1+z_2}\sigma_{p(z)}
       \quad(z\notin Q',\ d(z,Q')=1).
\]
This coordinatewise bijection carries the conditional
antiferromagnetic law in \(Q\) to
\(\mu^{+,\eta}_{\kappa\circ p,Q'}\), intertwines every site update,
and preserves Hamming distances between configurations in each fibre.
\end{lemma}
""", note='No global sign function on an odd torus is defined. The two spare sites per coordinate deliberately avoid exterior identifications; no parity assumption or 2 by 2 cell is used.')

add('4. Windows, stopped coupling, and the periodic block gap', 'd:shells', 'Physical-site shells and exceptional indices', 'A (frozen shared definition)',
    'kept with edits', 'baseline e:shells; MOSPROOF eq:shells; OPPORTUNITIES #16', ['d:moment'],
r"""
\begin{definition}\label{d:shells}
For \(a\in\mathbb Z^2\), integer \(u\ge1\), put
\(C_u(a)=a+\{-u,\ldots,u\}^2\).
For \(\operatorname{dist}_\infty(y,C_u(a))=1\), let
\(s=u^{1/4}\), \(k_i=\lfloor is\rfloor\), \(i_1=\lfloor s\rfloor+1\).
For an integer \(l_0\ge1\) define
\[
 \begin{split}
 F_i&=\{x\in C_u(a):|x-y|_\infty>(i-1)s\},\\
 D_i&=\{x\in C_u(a):|x-y|_\infty=k_i\},\\
 A_i&=\{x\in D_i:\operatorname{dist}_\infty
                    (x,\mathbb Z^2\setminus C_u(a))\le l_0\},\qquad
 B_i=D_i\setminus A_i .
 \end{split}
\]
Let \(I_0\) consist of the integers \(2\le i\le i_1\) for which
some point of \(D_i\) is at distance strictly less than \(s/3\)
from a corner site of \(C_u(a)\).
All these are sets of physical sites.
\end{definition}
""", True)

add('4. Windows, stopped coupling, and the periodic block gap', 'd:W', 'The uniform window interface', 'A (contract); B (establishes it)',
    'kept with edits', 'baseline d:W; STRENGTHEN-ALL d:W; OPPORTUNITIES #16/#20', ['d:framemodel','d:shells'],
r"""
\begin{definition}[(W)]\label{d:W}
The family of plane frame specifications has \(\mathsf W(l_0,p_0,M_\star)\)
if \(l_0,M_\star\) are positive integers, \(0<p_0\le1\), and,
for every proper plane three-colouring, every translate \(C_u(a)\)
with integer \(u\ge M_\star\), every \(y\) as in Definition~\ref{d:shells},
every integer \(2\le i\le u^{1/4}\) outside \(I_0\), and every two
admissible frame-valued boundary conditions \(\eta,\xi\) for \(F_i\),
\[
 d_{\mathrm{TV}}\!\left(
       \mu^{+,\eta}_{\kappa,F_i,B_i},
       \mu^{+,\xi}_{\kappa,F_i,B_i}\right)\le1-p_0 .
\]
The subscript \(B_i\) denotes a marginal. Boundaries are arbitrary
within their site alphabets; they need not agree anywhere.
\end{definition}
""", True)

add('4. Windows, stopped coupling, and the periodic block gap', 'l:stopped', 'The stopped coupling at site scale', 'A',
    'replaces the coupling proof behind baseline p:surgery', 'MOSPROOF lem:stopped; STRENGTHEN-ALL l:stopped; OPPORTUNITIES #16', ['d:W','l:shellgeom','l:planeenergy','l:finitecoupling','l:surgery'],
r"""
\begin{lemma}\label{l:stopped}
Suppose a consistent positive plane specification with site-dependent
finite alphabets has range one in \(\ell^\infty\), one-site probabilities
at least \(\alpha\in(0,1]\), and the window bound (W) at every translate.
Put \(\delta=p_0\alpha^{16l_0}\) and
\(M_{\mathrm g}(l_0)=\max\{16,6(l_0+1)\}^4\).
For \(u\ge\max\{M_\star,M_{\mathrm g}(l_0)\}\), boundaries of \(C_u(a)\)
agreeing off one exterior site \(y\), and any integer
\(4\le h\le\lfloor u^{1/4}\rfloor\), there is a coupling of the
full laws such that
\[
 \mathbb P(n_{Q_h}\ne n'_{Q_h})\le(1-\delta)^{h-3},
 \qquad Q_h=\{x\in C_u(a):|x-y|_\infty>hu^{1/4}\}.
\]
If \(y\) is farther than range one, the full laws are equal.
\end{lemma}
""", note='Use trials 2 through h and propagation through h+1. Independently resample A_i after coupling/completing B_i. Multiply conditional failure bounds, not unconditional probabilities. No success estimate at an index above s is used.')

add('4. Windows, stopped coupling, and the periodic block gap', 'p:surgery', 'The corrected original terminal-radius conclusion', 'A',
    'kept with edits (as a short corollary)', 'baseline p:surgery; MOSPROOF cor:originalprop', ['l:stopped'],
r"""
\begin{corollary}\label{p:surgery}
Under the hypotheses and size threshold of Lemma~\ref{l:stopped},
the same two laws have marginal total variation at most
\((1-\delta)^{u^{1/4}-4}\) on
\(\{x\in C_u(a):|x-y|_\infty>u^{1/2}\}\).
When \(\delta=1\), this upper bound is zero.
\end{corollary}
""", note='This corollary is retained but is not the input to periodic contraction. The earlier stopped coupling is essential.')

add('4. Windows, stopped coupling, and the periodic block gap', 'l:hamming', 'One square scale with small Hamming cost', 'A',
    'new; narrows MOSPROOF lem:windowK to one radius', 'MOSPROOF lem:tail/lem:windowK; OPPORTUNITIES #1/#16', ['l:stopped','l:finitecoupling'],
r"""
\begin{lemma}\label{l:hamming}
Assume (W) and \(\alpha\in(0,1]\) as above, and put
\(d_0=\min\{1/2,p_0\alpha^{16l_0}\}\).
Choose an integer \(n\) satisfying
\[
 n\ge44,\quad n^8\ge M_\star,\quad
 n^2\ge\max\{50000,6(l_0+1)\},\quad
 n^{12}d_0^{20}\ge50000\,2^{20}\,20!.
\]
Such an integer exists. Set \(M=n^8\).
Every translated \(C_M(a)\), with any two admissible boundaries
agreeing off one exterior site, admits a full-law coupling with
expected Hamming distance at most \(M/1000\).
One sufficient bound is
\[
 25n^6+25n^{16}(1-d_0)^{n-3}\le M/1000.
\]
\end{lemma}
""", note='Keep n and M as existence scales. The finite binomial estimate (1-d_0)^(n-3) <= 2^20 20!/(d_0^20 n^20) proves the displayed claim. No clamped squares or interval of block radii is needed.')

add('4. Windows, stopped coupling, and the periodic block gap', 't:periodic', 'Direct periodic physical-site block criterion', 'A',
    'new; replaces baseline t:K and c:gapcell', 'OPPORTUNITIES #1/#16; MOSPROOF lem:contraction/lem:comparison', ['l:contraction','l:comparison'],
r"""
\begin{theorem}\label{t:periodic}
Let \(M\ge1\), \(L,N\ge2M+3\), and let \(\mu>0\) be a
probability on a finite product over \(\Lambda_{L,N}\) whose
conditional law on any set depends only on letters in its exterior
\(\ell^\infty\) one-neighbourhood.
For every translated square \(Q\) of side \(2M+1\), suppose that:
all conditional single-site laws on \(Q\) have Poincare gap at least
\(g>0\); and any two conditional block laws whose outside
configurations agree off one site admit a coupling with expected
Hamming distance in \(Q\) at most \(K\ge0\), whenever that site is
outside and at \(\ell^\infty\) distance one from \(Q\).
Put \(T_M=(2M+1)^2\), \(S_M=8M+8\), and suppose \(S_MK<T_M\).
Then
\[
 \sum_{Q}(I-E_Q)\text{ has Poincare gap at least }T_M-S_MK,\qquad
 \lambda(\mu)\ge g\left(1-\frac{S_MK}{T_M}\right).
\]
The sum is over all torus translates, each at rate one.
In particular, \(K\le M/1000\) implies
\(\lambda(\mu)\ge(499/500)g\).
\end{theorem}
""", note='A fixed site belongs to exactly T_M translated blocks; exactly S_M blocks exclude it at infinity-distance one (this includes four harmless corner positions for nearest-neighbour fields). Counts use labels/placements, never invariant eigenvectors. The block gap and its comparison must both use unnormalized rates.')

add('4. Windows, stopped coupling, and the periodic block gap', 't:mainW', 'Assembly from the physical window estimate', 'A',
    'replaces baseline t:mainW', 'OPPORTUNITIES #1/#7/#16; STRENGTHEN-ALL local gauge and comparison', ['l:hamming','l:boxlift','l:planeenergy','t:periodic','t:QD','p:toruskernel'],
r"""
\begin{theorem}\label{t:mainW}
If the plane frame family satisfies (W), there exist \(c>0\) and
an integer \(L_0\ge3\) such that
\(\ker H_{L,N}=\mathbb C B_{L,N}\) and every nonzero eigenvalue is
at least \(c\), for all integers \(L,N\ge L_0\).
\end{theorem}
""", note='For the existence scale M, use g_M = r_b^[2(2M+1)(2M)], take L_0=2M+3, and use the quantum comparison with c=(499/1000) g_star g_M. These are symbolic normalization checks in the proof; the theorem and abstract keep c and L_0 existential. There is no explicit-constant appendix.')

add('5. The cut and the site-scale window theorem', 'l:shellgeom', 'Shared shell geometry, including parallel clearance', 'B',
    'kept with edits', 'baseline l:shellgeom; MOSPROOF lem:geometry; REF-MOS insertion note', ['d:shells'],
r"""
\begin{lemma}\label{l:shellgeom}
For \(u\ge M_{\mathrm g}(l_0)=\max\{16,6(l_0+1)\}^4\),
\(|I_0|\le1\), and \(D_i\subset F_i\) for \(2\le i\le i_1\).
For \(2\le i\le i_1\) outside \(I_0\), \(|A_i|\le8l_0\).
Every side of \(y+[-k_i,k_i]^2\) parallel to an edge of \(C_u(a)\)
and meeting \(C_u(a)\) is at distance at least \(s/3\) from the
exterior half-plane beyond that edge.
For \(i\ge2\), every point of \(C_u(a)\setminus F_i\)
within \(\ell^\infty\) distance one of \(F_i\) lies in \(D_{i-1}\);
\(y\) is not within that distance of \(F_i\).
\end{lemma}
""", True, 'This pure geometry lemma is B’s second export to A. Include the parallel-side clearance in the statement, since the cut count consumes it. Coordinate reflections do not assert symmetry of any Gibbs specification.')

add('5. The cut and the site-scale window theorem', 'l:cut', 'Factorization and common minorization', 'B',
    'kept with edits; replaces the tanh conclusion', 'baseline l:cut; STRENGTHEN-ALL e:windowlaw–e:cutratio; OPPORTUNITIES #10', ['l:exact','l:finitefacts','d:framemodel'],
r"""
\begin{lemma}\label{l:cut}
Let \(F\subset\mathbb Z^2\) be finite, \(B\subset F\) have no
neighbour outside \(F\), and \(G=F\setminus B\).
Suppose \(X\subset G\) and \(G\setminus X=G_1\sqcup G_2\), with
no bond between the pieces, no site of \(G_1\) adjacent to \(F^c\),
and no site of \(G_2\) adjacent to \(B\).
For the original legs of \(G\), use pins \(\eta\) into \(F^c\)
and window letters \(s\) into \(B\). Put
\[
 e(\eta,s)=\log\Psi_{G\setminus X}(\eta s)-\log\Psi_G(\eta s).
\]
If \(|e(\eta,s)|\le E<\infty\) for all admissible \(\eta,s\),
then there is a strictly positive probability \(\nu\) on window
configurations, independent of \(\eta\), such that
\[
 e^{-2E}\nu(s)\le\mu^{+,\eta}_{\kappa,F}(n_B=s)
                         \le e^{2E}\nu(s).
\]
Consequently any two window laws have total variation at most
\(1-e^{-2E}\).
One may take \(\nu(s)\) proportional to \(W_B(s)Z_{G_1}^{s}\),
where \(W_B\) is the actual product of frame site weights and
internal window bond weights. Only original legs are retained in
the partition functions after removing \(X\).
\end{lemma}
""", note='Keep the full-support check for nu and every normalizer. The overlap identity with the common minorization replaces likelihood-ratio optimization; no hyperbolic function is required.')

add('5. The cut and the site-scale window theorem', 'l:removal', 'One seed and a connected removal order', 'B',
    'replaces baseline l:removal constants', 'baseline l:removal/e:Ij/e:telescope; OPPORTUNITIES #10', ['h:P','l:35','l:finitefacts','l:moments'],
r"""
\begin{lemma}\label{l:removal}
Assume \(\mathsf P(A,\theta)\), and put
\(\mathsf F(d)=A\theta^{\max\{d,0\}}\).
Let \(x_1,\ldots,x_p\) be distinct points of \(G\), \(p\ge1\),
with \(b_G(x_j)=d(x_j,G^c)\ge3\), such that each \(x_j\), \(j\ge2\),
has a nearest neighbour among its predecessors.
For \(X=\{x_1,\ldots,x_p\}\) and every original unit-pin assignment,
\[
 |\log\Psi_{G\setminus X}(\tau)-\log\Psi_G(\tau)|
 \le1+4\mathsf F(b_G(x_1)-3)
                  +2\sum_{j=2}^p\mathsf F(b_G(x_j)-3).
\]
\end{lemma}
""", note='The first four-neighbour removal remains a seed. Its raw four-spin bracket costs at most 1 after logarithmic comparison; do not drop this additive term. Later removals have at most three neighbours. It suffices to bound every integrated factor below by 1/2.')

add('5. The cut and the site-scale window theorem', 'd:thickcut', 'The tapered site set and thickened cut', 'B',
    'replaces baseline e:Ucut/e:Xcut (no cells)', 'OPPORTUNITIES #3/#16; baseline s:cutgeom', ['d:shells'],
r"""
\begin{definition}\label{d:thickcut}
Fix \(l_0=64\), a nonexceptional shell with \(2\le i\le s\),
and write \(k=k_i\), \(F=F_i\), \(B=B_i\), \(G=F\setminus B\).
For \(z\in\mathbb Z^2\), set
\[
 t(z)=\big||z-y|_\infty-k\big|,\qquad
 h(z)=\operatorname{dist}_\infty(z,C_u(a)^c)\quad
        (h(z)=0\text{ outside }C_u(a)).
\]
Define
\[
 \begin{gathered}
 U=\{z\in C_u(a):t(z)\le\min(h(z)-32,s/12)\},\\
 X_0=\{z\notin U:\operatorname{dist}_\infty(z,U)=1\},\qquad
 X=\{z:d(z,X_0)\le1\}.
 \end{gathered}
\]
Set \(G_1=(U\setminus B)\setminus X\) and
\(G_2=G\setminus(U\cup X)\).
\end{definition}
""")

add('5. The cut and the site-scale window theorem', 'l:cutgeom', 'The physical geometry and summable cut cost', 'B',
    'replaces baseline l:cutgeom', 'baseline l:cutgeom with OPPORTUNITIES #3/#16; to be written at site scale', ['d:thickcut','l:shellgeom'],
r"""
\begin{lemma}\label{l:cutgeom}
There exists \(s_0\ge\max\{16,6(64+1)\}\) such that, uniformly
in the translate, \(y\), and nonexceptional integer \(2\le i\le s\),
the following hold for \(s=u^{1/4}\ge s_0\).
The set \(U\) is finite, nonempty, and star-connected, and \(U^c\)
is star-connected. We have \(B\subset U\subset F\), all neighbours
of \(B\) lie in \(U\), and no site of \(U\) is adjacent to \(F^c\).
The set \(X_0\) is nonempty and lies in \(G\). For \(x\in X_0\),
\[
 b_G(x)\ge
 \begin{cases}\max\{t(x),16\}-2,&t(x)\le s/12,\\s/12-1,&t(x)>s/12,
 \end{cases}
 \qquad b_G(x)\ge14 .
 \]
For each integer \(j\ge0\), there are at most \(48\) sites of
\(X_0\) with \(t(x)=j\le s/12\).
For \(0<\vartheta<1\), put
\[
 C_{\rm near}(\vartheta)=48\vartheta^{14}
                \left(17+\frac1{1-\vartheta}\right).
\]
Then
\[
 \sum_{x\in X_0}\vartheta^{b_G(x)}
 \le C_{\rm near}(\vartheta)
                 +4(2u+1)^2\vartheta^{s/12-1}.
\]
The thickened set \(X\) lies in \(G\), has \(b_G\ge13\), and
\(G\setminus X=G_1\sqcup G_2\) satisfies all separation and
no-adjacency assumptions of Lemma~\ref{l:cut}. Moreover
\[
 \sum_{z\in X}\vartheta^{b_G(z)}
       \le5\vartheta^{-1}\sum_{x\in X_0}\vartheta^{b_G(x)} .
\]
\end{lemma}
""", note='The site-scale near estimate loses the baseline factor two. Count intersections of the two square boundaries using signed inward depths and the exported parallel clearance; retain the corrected coincident-side argument. Radial paths prove connectivity of U and its complement. The deleted no-diagonal-only-block argument is not needed.')

add('5. The cut and the site-scale window theorem', 'l:Xconn', 'Connectedness of the thickened cut', 'B',
    'replaces baseline l:Xconn', 'OPPORTUNITIES #3; baseline topology Steps 1–2', ['l:cutgeom','l:boundaryconn','l:thicken'],
r"""
\begin{lemma}\label{l:Xconn}
Under Lemma~\ref{l:cutgeom}, the finite nonempty cut \(X\) is
nearest-neighbour connected. Hence it can be ordered so that every
site after the first has a previously listed nearest neighbour.
\end{lemma}
""")

add('5. The cut and the site-scale window theorem', 't:cutMOS', 'The interface from (P) to physical windows', 'B',
    'replaces baseline t:cutMOS', 'baseline t:cutMOS; STRENGTHEN-ALL uniformity; OPPORTUNITIES #3/#10/#16', ['h:P','l:cut','l:removal','l:cutgeom','l:Xconn','d:W'],
r"""
\begin{theorem}\label{t:cutMOS}
If \(\mathsf P(A,\theta)\) holds, then the family of plane frame
specifications has \(\mathsf W(64,p_0,M_\star)\), with common
\(p_0\in(0,1]\) and integer \(M_\star\ge1\) depending only on
\(A,\theta\). The constants work for every proper plane
three-colouring and every translate.
Specifically, let
\[
 E=1+4A+10A\theta^{-4}
       \left[48\theta^{14}\left(17+\frac1{1-\theta}\right)+1\right],
 \qquad p_0=e^{-2E}.
\]
One may choose \(M_\star\) sufficiently large that, for all
integers \(u\ge M_\star\),
\[
 u^{1/4}\ge s_0,\qquad
 4(2u+1)^2\theta^{u^{1/4}/12-1}\le1.
\]
With this choice the displayed \(p_0\) is valid.
\end{theorem}
""", True, 'The proof uses only the common finite moment/partition interface and actual positive window weights. It must not infer equality of discrete marginals across colourings. Refer to source labels, correcting the REF-SA-B subsection-locator defect.')

add('6. Walk expansion without scalar trace masses', 'd:domain', 'Ordinary domains and auxiliary terminal networks', 'C',
    'kept with edits; removes only the scalar mass field', 'baseline d:domain with corrected auxiliary networks; OPPORTUNITIES #2/#4', ['d:pinmodel','d:moment'],
r"""
\begin{definition}\label{d:domain}
Fix finite \(G\), \(S=S(G)\), and original unit pins \(\tau\).
A domain assigns statuses \(\mathrm U,\mathrm D,\mathrm X\);
\(\mathrm X\) sites are removed. Each nonremoved site has a kept
subset of its incident bonds inside \(G\). A bond is present if both
ends are nonremoved and both keep it. A \(\mathrm D\) site has at
most two present bonds. Protected sites in \(S\) have status
\(\mathrm U\) and keep every incident bond inside \(G\).
Use \(\lambda_{\mathrm U},\lambda_{\mathrm D}\) at the corresponding
sites and define
\[
 Z_D^\tau[f]=\sum_n f(n)
       \prod_{\text{present }\{x,y\}}(1+n_x\cdot n_y)
       \prod_{\substack{(x,z)\in\mathcal L(G)\\x\in S}}
                   (1+\tau_{xz}\cdot n_x)
       \prod_{x:\,\mathrm{st}(x)\ne\mathrm X}\lambda_{\mathrm{st}(x)}(n_x).
\]
The sum is over the product of the supports \(D\) at \(\mathrm U\)
sites and \(D\cup\{0\}\) at \(\mathrm D\) sites.
Define the free sum, normalized expectations and \(\Psi_D\) as before.
The class \(\mathcal D_{\mathrm{cons}}(G)\) consists of domains in
which every \(\mathrm U\) site keeps all its bonds, every \(\mathrm D\)
site keeps exactly two, and every bond between nonremoved sites is
kept by both ends or by neither.
An auxiliary network has the same data but permits protected
\(\mathrm U\) sites to have arbitrary kept subsets. It retains every
original leg factor. Neither domains nor auxiliary networks carry
a scalar trace mass. Only the networks occurring below, with at most
four factors at each site, are used.
\end{definition}
""", True)

add('6. Walk expansion without scalar trace masses', 'd:trace', 'Restricted starts, tracing, and the new coefficient', 'C',
    'replaces the trace definition and scalar mass convention in baseline §6', 'OPPORTUNITIES #4/#20; baseline corrected trace definition', ['d:domain'],
r"""
\begin{definition}\label{d:trace}
A trail uses distinct present unoriented bonds. Its prefixes are
\(w_j=(v_0,\ldots,v_j)\), and \(\mathcal T_D(u,T)\) denotes trails
starting at \(u\) and stopping at their first hit of \(T\).
No trail departs from \(S\).
At departure from \(y=v_{j-1}\), drop \(\{y,v_j\}\) at both ends.
If \(y\) is \(\mathrm U\), change it to \(\mathrm D\), keeping its
other kept bonds. If \(y\) is \(\mathrm D\), remove it.
Call the resulting network \(D[w_j]\), with \(D[w_0]=D\).
Admissible initial starts are unpinned sites outside \(S\) of status
\(\mathrm U\) with at most three present bonds, or status \(\mathrm D\)
with at most one. The same restrictions then hold at every later
departure. Set
\[
 a_D(w)=3^{-N_{\mathrm U}(w)}5^{-N_{\mathrm D}(w)},\qquad
 R_D^\bullet(w)=Z^\bullet_{D[w]}/Z^\bullet_D,
\]
where the counts record the status at departure, not the original status.
Original legs are always unchanged, including at a terminal hit of \(S\).
\end{definition}
""")

add('6. Walk expansion without scalar trace masses', 'l:stepid', 'The two used step identities', 'C',
    'replaces baseline l:stepid by its used degree range', 'OPPORTUNITIES #2/#4', ['l:moments'],
r"""
\begin{lemma}\label{l:stepid}
For vectors \(a,u_1,\ldots,u_k\in\mathbb R^3\),
\[
 \mathcal M\!\left((a\cdot n)\prod_{i=1}^k(1+n\cdot u_i)\right)
 =\frac13\sum_{i=1}^k(a\cdot u_i)
       \lambda_{\mathrm D}\!\left(\prod_{i'\ne i}(1+n\cdot u_{i'})\right)
       \quad(0\le k\le3),
\]
and
\[
 \lambda_{\mathrm D}\!\left((a\cdot n)\prod_{i=1}^k(1+n\cdot u_i)\right)
       =\frac15\sum_{i=1}^k a\cdot u_i\quad(0\le k\le1).
\]
An empty sum is zero. The second identity removes the departure site
with no residual scalar mass.
\end{lemma}
""", note='Do not keep the old k=4 U identity when only fourth moments are specified. The initial two-bond D case is outside this new lemma and outside every application.')

add('6. Walk expansion without scalar trace masses', 'p:pairwalk', 'The pair expansion on its narrowed domain', 'C',
    'kept with edits', 'baseline p:pairwalk; OPPORTUNITIES #2/#4/#20', ['d:trace','l:stepid','l:finitefacts'],
r"""
\begin{proposition}\label{p:pairwalk}
Let \(D\) be a domain or auxiliary network, and let \(u\) be an
admissible initial start. Let \(v\ne u\) be nonremoved; if it is
\(\mathrm U\), assume at most three incident factors, counting
original legs; if it is \(\mathrm D\), assume at most one present bond.
Put \(T=S\cup\{v\}\). For \(\bullet=\tau,0\),
\[
 \mathbb E_D^\bullet(n_u\cdot n_v)=
 \sum_{w\in\mathcal T_D(u,T)}a_D(w)R_D^\bullet(w)
           \mathbb E_{D[w]}^\bullet(n_{v_{|w|}}\cdot n_v).
\]
If the endpoint is \(v\), its last factor is independent of the
choice of \(\bullet\): it is \(1\) for status \(\mathrm U\),
and \(3/5\) for status \(\mathrm D\).
Every partition product with an inserted observable used in this
identity has separate degree at most four.
\end{proposition}
""", note='Prove the expansion first for unnormalized numerators and divide once. The second expansion’s target is the already defective terminal site e in S, which has lost its arrival bond and therefore has at most three factors. This is why the endpoint restriction is sufficient.')

add('6. Walk expansion without scalar trace masses', 'd:ratios', 'Ratios after moving revisit mass', 'C',
    'replaces baseline §6 step-ratio formulas', 'OPPORTUNITIES #4; baseline e:IJ', ['d:trace'],
r"""
\begin{definition}\label{d:ratios}
At a step \(j\), put
\(\rho_j^\bullet=Z^\bullet_{D[w_j]}/Z^\bullet_{D[w_{j-1}]}\).
At a \(\mathrm D\) departure \(\rho_j^\tau=\rho_j^0=1\).
At a \(\mathrm U\) departure from \(y\) to \(o\), let \(E'\)
be the pre-step network with \(y\) removed.
If the other present neighbours are \(f,g\), set
\[
 I=1+\tfrac13(P_{fg}+P_{fo}+P_{go}),\quad
 J=1+\tfrac15P_{fg},\quad P_{ab}=n_a\cdot n_b,\qquad
 (\rho_j^\bullet)^{-1}=\mathbb E_{E'}^\bullet I/
                                      \mathbb E_{E'}^\bullet J.
\]
With only one other neighbour \(f\), use \(I=1+P_{fo}/3,\ J=1\);
with no other neighbour, \(\rho_j^\bullet=1\).
Straight/turning refers to the incoming direction, with a designated
absent incoming bond at the first step.
\end{definition}
""")

add('6. Walk expansion without scalar trace masses', 'l:response', 'The unchanged rational response bounds', 'C',
    'kept as is on the used U departures', 'baseline l:response; OPPORTUNITIES #4', ['d:ratios','l:35','l:finitefacts'],
r"""
\begin{lemma}\label{l:response}
At a \(\mathrm U\) departure \(y\notin S\), write
\(r_{ab}=\mathbb E^\tau_{E'}P_{ab}-\mathbb E^0_{E'}P_{ab}\).
With three present neighbours,
\[
 \log\rho_j^0-\log\rho_j^\tau
       =\alpha_jr_{fg}+\beta_j(r_{fo}+r_{go}),\qquad
 0<\alpha_j\le\bar\alpha=\frac{18094}{100000},\quad
 0<\beta_j\le\bar\beta=\frac{36751}{100000}.
\]
With two present neighbours the response is \(\beta_j'r_{fo}\),
where \(0<\beta_j'\le35510/100000\le\bar\beta\);
with one it is zero. Also \(\rho_j^0\le1\) and
\(\rho_j^\tau\le12/5\).
A \(\mathrm D\) departure has zero logarithmic response.
\end{lemma}
""", note='All terminating decimals denote exact rationals. Retain the logarithmic-mean proof and rigorous scalar inequalities; these coefficients feed the unchanged kernel, so they cannot be rounded down.')

add('6. Walk expansion without scalar trace masses', 'l:exposure', 'Exposure for the new ratio convention', 'C',
    'kept with edits', 'baseline l:exposure; OPPORTUNITIES #4', ['d:trace','l:response'],
r"""
\begin{lemma}\label{l:exposure}
For an admissibly started stopped trail, let \(\Phi\) be its
\(\mathrm U\) departures, and suppose \(\rho_j^\tau\le x_j\),
\(x_j\ge1\), for \(j\in\Phi\).
For every ordering \(\sigma\) of \(\Phi\),
\[
 |R_D^\tau(w)-R_D^0(w)|
 \le\sum_{k=1}^{|\Phi|}
       |\log\rho_{\sigma(k)}^0-\log\rho_{\sigma(k)}^\tau|
                         \prod_{l\le k}x_{\sigma(l)}.
\]
Multiplication by \(a_D(w)\) gives the corresponding bound on the
coefficient in the pair expansion.
\end{lemma}
""", note='There is no extra (3/5) factor in this formula: it is already in a_D(w). Every D departure has ratio one for both pin choices.')

add('6. Walk expansion without scalar trace masses', 'd:pattern', 'The corrected covered pattern class', 'C',
    'kept with edits (finite functional, no infimum)', 'baseline d:pattern, including every covered-tip and slot correction; OPPORTUNITIES #20', ['d:domain'],
r"""
\begin{definition}\label{d:pattern}
Let \(\mathsf T=\{z:d(z,0)\le2\}\), with passage site \(0\),
arrival site \(\mathsf s=(0,-1)\), other neighbours
\(\mathsf e=(1,0),\mathsf N=(0,1),\mathsf W=(-1,0)\),
four corners \((\pm1,\pm1)\), and tips \((\pm2,0),(0,\pm2)\).
The external slots are the two external bonds at each corner and
the three at each tip, twenty in total.
A pattern chooses an out-neighbour \(o\in\{\mathsf e,\mathsf N,\mathsf W\}\)
and statuses/kept sets with the following rules.
The passage site is \(\mathrm U\) and keeps precisely its three
non-arrival bonds. The arrival site is removed or is \(\mathrm D\)
keeping two of its three non-passage bonds.
Each other neighbour is \(\mathrm U,\mathrm X\), or \(\mathrm D\)
keeping its passage bond and one other bond; \(o\) is not removed.
Each corner is \(\mathrm U,\mathrm X\), or \(\mathrm D\) keeping
two of its four bonds. Every \(\mathrm U\) site other than the
passage site keeps all four bonds.
Between nonremoved non-tip sites, a bond is kept by both ends or
by neither. Tips are covering \(\mathrm U\) sites; their bond to
a neighbour \(z\) is present exactly when \(z\) is nonremoved and
keeps that bond. No consistency condition with a global tip kept
set is imposed.
For \(m\in(\mathbb S^2)^{20}\), include every external slot factor
at every nonremoved corner and tip, including both corner slots
when the corresponding actual external bonds are missing.
Let \(Z_{\rm cur}(\pi;m)\) be the finite product functional of
all present template bonds and these slots, using the status laws.
Let \(Z_{\rm next}(\pi;m)\) change the passage law to
\(\lambda_{\mathrm D}\) and drop its out-bond.
The resulting class is \(\mathcal P_{\rm ext}\); it is straight
when \(o=\mathsf N\), and turning otherwise.
\end{definition}
""", True, 'These are covered local integrals, not protected-boundary domains. Missing actual external factors are filled by convex averaging. Do not reinstate the older uncorrrected pattern class.')

add('6. Walk expansion without scalar trace masses', 'h:H1', 'The precise local computational contract', 'C',
    'kept with edits (inequalities rather than optimization)', 'baseline h:H1/t:H1; OPPORTUNITIES #20/#21', ['d:pattern'],
r"""
\begin{definition}[(H1)]\label{h:H1}
For \(c_{\mathrm s},c_{\mathrm t}\in(0,1]\), (H1) means that
for every \(\pi\in\mathcal P_{\rm ext}\) and every
\(m\in(\mathbb S^2)^{20}\),
\[
 Z_{\rm cur}(\pi;m)\ge c_{\rm type(\pi)}Z_{\rm next}(\pi;m).
\]
In the paper the fixed thresholds are
\(c_{\mathrm s}=961/1000\), \(c_{\mathrm t}=187/200\).
No minimum, minimizing pins, or optimal inversion is asserted.
\end{definition}
""", True)

add('6. Walk expansion without scalar trace masses', 'l:local', 'Local covering implies the step bound', 'C',
    'kept with edits', 'baseline l:local; OPPORTUNITIES #2/#20', ['l:35','h:H1','d:ratios'],
r"""
\begin{lemma}\label{l:local}
At any \(\mathrm U\) departure outside \(S\) whose normalized
non-tip template data belong to \(\mathcal P_{\rm ext}\), (H1)
implies \(\rho_j^\tau\le1/c_{\rm type}\).
The conclusion is uniform in all original unit pins, all outside
spins of norm at most one, all missing external factors, and all
actual tip statuses and kept sets allowed by the ordinary-domain rules.
\end{lemma}
""", note='Ratios of positive averages preserve lower bounds; fill missing slots by averaging opposite unit pins and use l:35 to replace any tip field by a covering U tip. Use polynomial covariance of the mean, not invariance of the finite law.')

add('6. Walk expansion without scalar trace masses', 'd:weights', 'The unchanged dominating lattice weights', 'C',
    'kept as is', 'baseline s:H2def; OPPORTUNITIES #4/#20', ['h:H1'],
r"""
\begin{definition}\label{d:weights}
Put \(x_{\mathrm s}=1/c_{\mathrm s}\), \(x_{\mathrm t}=1/c_{\mathrm t}\).
A lattice trail \(w=(v_0,\ldots,v_n)\) has distinct unoriented
nearest-neighbour bonds. Give it a designated unit incoming direction
\(a\), and forbid \(v_1-v_0=-a\) when \(n\ge1\); the virtual
incoming bond is not itself a used bond of the trail.
For departure \(i\), \(0\le i<n\), give weight \(1/5\) if \(v_i\)
has been departed from earlier, and otherwise weight \(x_{\mathrm s}/3\)
for continuing in the incoming direction and \(x_{\mathrm t}/3\)
for a turn. Let \(\mathsf W(w)\) be the product, with
\(\mathsf W(\varnothing)=1\).
\end{definition}
""", True)

add('6. Walk expansion without scalar trace masses', 'h:H2', 'The open-trail computational contract', 'C',
    'kept with edits (explicit positive rate)', 'baseline h:H2; OPPORTUNITIES #20', ['d:weights'],
r"""
\begin{definition}[(H2)]\label{h:H2}
For \(C_V\ge1\) and \(0<q<1\), (H2) means that for every
integer \(n\ge0\), every start and every designated incoming direction,
\[
 \sum_{\substack{|w|=n\\\text{initial reversal forbidden}}}
                      \mathsf W(w)\le C_Vq^n .
\]
The sum is over plane lattice trails with those specified initial data.
\end{definition}
""", True)

add('6. Walk expansion without scalar trace masses', 'l:onepoint', 'A common majorant for both pin choices', 'C',
    'kept with edits (mass-free coefficient and restricted D start)', 'baseline l:onepoint with its corrected maximum; OPPORTUNITIES #4/#20', ['h:H1','h:H2','l:local','l:response','d:trace'],
r"""
\begin{lemma}\label{l:onepoint}
Assume (H1) and (H2). Start a trace at an admissible \(x\notin S\)
with incoming direction \(a\) such that \(\{x-a,x\}\) is absent.
Suppose each stopped trail from \(x\) to \(S\) has at most twelve
\(\mathrm U\) departures whose templates are not covered patterns.
Then
\[
 \sum_{w\in\mathcal T_D(x,S)}a_D(w)
                  \max\{R_D^\tau(w),R_D^0(w)\}
 \le (12/5)^{12}\frac{C_V}{1-q}\,q^{d(x,S)}.
\]
Pointwise the summand is at most \((12/5)^{12}\mathsf W(w)\).
\end{lemma}
""", note='An initially D site with two present bonds is excluded. For an initially D site treated as a lattice first visit, 1/5 <= x_type/3 supplies domination. Prove the pointwise bound for the maximum before summing; separate sums do not imply this statement.')

add('7. Pair closure, a positive-vector witness, and renewal', 'd:pairenv', 'The two response envelopes', 'C',
    'kept as is', 'baseline s:pairclass/e:FX; OPPORTUNITIES #20', ['d:domain'],
r"""
\begin{definition}\label{d:pairenv}
For \(D\in\mathcal D_{\rm cons}(G)\), let \(P_B(D)\) and \(P_C(D)\)
be the ordered nonremoved pairs \((u,v)\) at distance two,
collinear or diagonal respectively, with a designated common neighbour
\(c\) of status \(\mathrm X\). Each endpoint is \(\mathrm U\),
or \(\mathrm D\) with at most one present bond.
For integer \(d\ge0\), let \(F_X(d)\) be the supremum of
\[
 \left|\mathbb E_D^\tau(n_u\cdot n_v)
                    -\mathbb E_D^0(n_u\cdot n_v)\right|
\]
over every finite \(G\), every original unit-pin assignment,
every \(D\in\mathcal D_{\rm cons}(G)\), and every pair in \(P_X(D)\)
with \(\min\{d(u,S(G)),d(v,S(G))\}\ge d\).
Use supremum zero for an empty class, and set \(F_X(d)=F_X(0)\)
for negative integers. Thus \(0\le F_X\le2\), and \(F_X\)
is nonincreasing.
\end{definition}
""")

add('7. Pair closure, a positive-vector witness, and renewal', 'l:closure', 'The corrected closure invariant', 'C',
    'kept with edits (no mass-reset language)', 'baseline l:closure; OPPORTUNITIES #4/#20', ['d:pairenv','d:trace','d:pattern'],
r"""
\begin{lemma}\label{l:closure}
Let \(D\in\mathcal D_{\rm cons}(G)\), \((u,v)\in P_X(D)\) have
centre \(c\), and \(u\notin S\). Before tracing, if \(u\) is
\(\mathrm U\), drop its kept bond to the removed \(c\); this changes
no partition function. Trace any trail from \(u\) without visiting
\(S\) before its last site; it need not avoid \(v\).
After every prefix ending at the live endpoint \(y\):
all departed sites are \(\mathrm D\) or \(\mathrm X\);
consistency between nonremoved sites holds; all nonlive
\(\mathrm U\) sites have full kept sets and all nonlive \(\mathrm D\)
sites have exactly two kept bonds.
After a positive-length prefix a live \(\mathrm U\) site has lost
only its arrival bond, and a live \(\mathrm D\) site keeps one bond;
the arrival site's other endpoint is \(\mathrm D\) or \(\mathrm X\).
At length zero a live \(\mathrm U\) site has its three non-\(c\)
kept bonds, while a live \(\mathrm D\) site retains its two kept
bonds but has at most one present bond.
Whenever \(y\notin S\), removing \(y\) yields an ordinary member
of \(\mathcal D_{\rm cons}(G)\). Every \(\mathrm U\) departure
before stopping has a covered pattern, and its nonremoved neighbour
pairs belong to \(P_B\) or \(P_C\) of that ordinary domain.
If the endpoint is \(e\in S\), it is \(\mathrm U\) with just its
arrival bond lost. This is the sole kept-set defect in the terminal
auxiliary network; all original legs remain. No removal of \(e\)
or ordinary-domain membership after removing \(e\) is asserted.
\end{lemma}
""")

add('7. Pair closure, a positive-vector witness, and renewal', 'l:terminalcover', 'The second expansion and its twelve exceptions', 'C',
    'new explicit statement of the corrected T2 argument', 'baseline t:rec, term T2; corrected unlabelled remark after l:local', ['l:closure','l:local','l:onepoint'],
r"""
\begin{lemma}\label{l:terminalcover}
In the first expansion of a pair of Definition~\ref{d:pairenv},
suppose the trail avoids its target \(v\) and stops at \(e\in S\).
In the terminal auxiliary network, start a second expansion from \(v\)
to \(S\), again dropping its kept bond to \(c\) if it is \(\mathrm U\).
The starts of both expansions have their designated incoming bond
absent and are admissible in Definition~\ref{d:trace}.
Before the second trail hits \(S\), a \(\mathrm U\) departure
outside \(\{y':0<d(y',e)\le2\}\) has a covered pattern.
There are at most twelve exceptional \(\mathrm U\) departures
on each second trail. Both expansions satisfy Lemma~\ref{l:onepoint}.
\end{lemma}
""", note='The twelve exceptions may occur anywhere along the second trail. They are not asserted to be its final twelve steps. No response supremum is taken over auxiliary terminal networks.')

add('7. Pair closure, a positive-vector witness, and renewal', 'd:kernel', 'The unchanged closed-trail shift kernel', 'C',
    'kept as is numerically; records the mass equivalence explicitly', 'baseline e:kernel; OPPORTUNITIES #4/#9/#20', ['d:weights'],
r"""
\begin{definition}\label{d:kernel}
For \(X=B,C\), fix \(c=0\), \(u=(-1,0)\), and \(v=(1,0)\)
for \(B\), \(v=(0,1)\) for \(C\).
Let \(\mathcal T_n^X\) be the length-\(n\) plane trails avoiding
\(c\), from \(u\) to their first hit of \(v\).
The initial incoming direction is \(u-c\).
Departure \(i\), \(0\le i<n\), is a lattice revisit if \(v_i\)
was departed from earlier. At each lattice first visit put
\(x_i=x_{\mathrm s}\) or \(x_{\mathrm t}\) according to its type.
Of the three neighbours other than the arrival site, the pair not
containing the outgoing neighbour has coefficient
\(\bar\alpha=18094/100000\), and each other pair has coefficient
\(\bar\beta=36751/100000\). A pair is dead if it contains \(c\) or a
site departed from twice before departure \(i\).
A live pair \(p\) has type \(Y=B,C\) and shift
\[
 s(p)=\max_{z\in p}\min\{d(z,u),d(z,v)\}.
\]
Let \(\kappa_{Y,s}(i)\) sum its coefficients at that type and shift.
Choose once and for all, for each trail \(w\), an ordering
\(\sigma_w\) of its lattice first visits, independent of any later
\(\theta\). Define
\[
 M_{XY,s}=\sum_{n\ge1}\sum_{w\in\mathcal T_n^X}
 3^{-n}(3/5)^{\operatorname{rev}(w)}
 \sum_k\kappa_{Y,s}(\sigma_w(k))\prod_{l\le k}x_{\sigma_w(l)},\qquad
 M_\theta[X,Y]=\sum_{s\ge0}M_{XY,s}\theta^{-s}.
\]
All sums are nonnegative series. The identity
\[
 3^{-n}(3/5)^{r}=3^{-(n-r)}5^{-r}
\]
identifies these coefficients with the new trace convention when
the statuses are determined by the lattice trail.
\end{definition}
""", True, 'Actual initially D sites count as extra diluted departures and are dominated by lattice first visits. Keep the dead-pair rule and shifts exactly; no alternative kernel is authorized.')

add('7. Pair closure, a positive-vector witness, and renewal', 'h:H3', 'Positive-vector replacement for (H3 prime)', 'C',
    'replaces baseline h:H3 (no spectral radius)', 'OPPORTUNITIES #9/#20; baseline p:tail row bounds', ['d:kernel'],
r"""
\begin{definition}[(H3\( _h\))]\label{h:H3}
For the same \(c_{\mathrm s},c_{\mathrm t}\) and the kernel above,
(H3\( _h\)) means that there exist fixed orderings \(\sigma_w\),
a vector \(h=(h_B,h_C)\in\mathbb Q_{>0}^2\), and
\(\rho_0\in\mathbb Q\cap(0,1)\) such that, for \(X=B,C\) and
every integer \(R\ge0\),
\[
 \sum_{n=1}^{R}\sum_{w\in\mathcal T_n^X}
 3^{-n}(3/5)^{\operatorname{rev}(w)}
 \sum_k\left(\sum_{Y,s}\kappa_{Y,s}(\sigma_w(k))h_Y\right)
                          \prod_{l\le k}x_{\sigma_w(l)}
 \le\rho_0h_X .
\]
Equivalently the full nonnegative sums obey \(M_1h\le\rho_0h\).
An ordering is only a supplied witness; no optimality is required.
\end{definition}
""", True, 'The finite-partial-sum formulation is the exact handoff to the certificate owner. It requires a bound for every R, not a finite prefix alone. It preserves the meaning of the old contraction input while avoiding spectral-radius theory.')

add('7. Pair closure, a positive-vector witness, and renewal', 'l:Mtheta', 'Transport the same witness to a shifted kernel', 'C',
    'replaces baseline l:Mtheta', 'OPPORTUNITIES #9; baseline shift estimate in l:Mtheta', ['h:H2','h:H3','d:kernel'],
r"""
\begin{lemma}\label{l:Mtheta}
Assume (H2) and (H3\( _h\)).
For every \(q^2<\theta\le1\), all entries of \(M_\theta\) are
finite. There exist \(q^2<\theta<1\) and \(\rho_0<\rho<1\)
such that the same vector \(h\) satisfies \(M_\theta h\le\rho h\).
Every shift of a length-\(n\) trail is at most \(n/2+1\), and
each matrix entry is bounded by
\[
 \sum_{n\ge1} n(\bar\alpha+2\bar\beta)
                      C_V q^n\theta^{-n/2-1}.
\]
\end{lemma}
""", note='Use convergence of nonnegative series or elementary geometric majorants with this fixed vector. Do not choose orderings after theta, invoke spectral-radius continuity, or construct a Perron eigenvector.')

add('7. Pair closure, a positive-vector witness, and renewal', 'l:recineq', 'The response recursion with the retained source constant', 'C',
    'kept as is (promoted from e:recineq)', 'baseline e:recineq and corrected proof of t:rec; OPPORTUNITIES #4/#20', ['l:closure','l:terminalcover','l:exposure','l:response','l:onepoint','d:kernel','d:pairenv'],
r"""
\begin{lemma}\label{l:recineq}
Assume (H1) and (H2), with the fixed orderings used in the kernel.
For \(X=B,C\) and every integer \(d\ge1\),
\[
 F_X(d)\le\sum_{Y=B,C}\sum_{s\ge0}M_{XY,s}F_Y(d-s)+C_Tq^{2d},
 \qquad
 C_T=2(12/5)^{24}\left(\frac{C_V}{1-q}\right)^2 .
\]
\end{lemma}
""", note='The target-hit part uses ordinary-domain closure and the exposure ordering. The boundary-hit part uses two stopped expansions and the common maximum majorant. These are the only auxiliary networks required.')

add('7. Pair closure, a positive-vector witness, and renewal', 'l:renewal', 'Bounded nonnegative renewal', 'C',
    'replaces the truncated-supremum/fixed-point end of baseline t:rec', 'OPPORTUNITIES #9', [],
r"""
\begin{lemma}\label{l:renewal}
Let \(m_{XY,s}\ge0\), \(h_X>0\), \(0<q^2<\theta<1\),
\(0<\rho<1\), and
\(\sum_{Y,s}m_{XY,s}h_Y\theta^{-s}\le\rho h_X\).
Suppose \(0\le F_X(d)\le2\) on \(\mathbb Z\), with
\(F_X(d)=F_X(0)\) for \(d<0\), and, for integers \(d\ge1\),
\[
 F_X(d)\le\sum_{Y,s}m_{XY,s}F_Y(d-s)+C_Tq^{2d},
 \qquad C_T\ge0.
\]
Writing \(H=\max_Xh_X/\min_Xh_X\), one has, for \(d\ge0\),
\[
 F_X(d)\le A\theta^d,\qquad
 A=\frac{H\max\{2,C_T\}}{1-\rho}\ge2 .
\]
\end{lemma}
""", note='Extend the source as 2 on nonpositive integers, iterate a finite number of times, bound the remainder by 2 h_X rho^k/min h, and sum the geometric source bound. No fixed-point theorem is an input.')

add('7. Pair closure, a positive-vector witness, and renewal', 't:rec', 'The export of (P)', 'C',
    'kept with edits', 'baseline t:rec; OPPORTUNITIES #9/#20', ['l:recineq','l:Mtheta','l:renewal','d:pairenv','h:P'],
r"""
\begin{theorem}\label{t:rec}
Assume (H1), (H2), and (H3\( _h\)) at the same pair
\((c_{\mathrm s},c_{\mathrm t})\).
Then there exist \(A\ge2\) and \(0<\theta<1\) such that
\(\mathsf P(A,\theta)\) holds.
One may take the \(\theta,\rho,h\) supplied by the shifted-witness
lemma and
\[
 A=\frac{\max h}{\min h}\,
       \frac{\max\{2,\,2(12/5)^{24}(C_V/(1-q))^2\}}{1-\rho}.
\]
\end{theorem}
""", True, 'The proof actually bounds both envelopes on every ordinary consistent domain. That stronger internal fact supplies (P) by the U/X specialization. No frame colouring or quantum gap is used here.')

add('8. Exact statements of the computational inputs', 't:H1', 'The operator-only local input theorem', 'C',
    'kept with edits (one proof path)', 'baseline t:H1 and operator-only file; OPPORTUNITIES #21', ['p:certificate','l:integercheck','h:H1'],
r"""
\begin{theorem}\label{t:H1}
For every \(\pi\in\mathcal P_{\rm ext}\) and every
\(m\in(\mathbb S^2)^{20}\),
\[
 Z_{\rm cur}(\pi;m)\ge
 \begin{cases}
 (961/1000)Z_{\rm next}(\pi;m),&\pi\text{ straight},\\
 (187/200)Z_{\rm next}(\pi;m),&\pi\text{ turning}.
 \end{cases}
\]
\end{theorem}
""", True, 'The proof must cover the corrected raw pattern rules, not just accept 7,962 records. Check completeness and thresholds, then the operator-only certificates. Historical selected numerical minima are not theorem statements.')

add('8. Exact statements of the computational inputs', 't:inputs', 'The complete numerical handoff', 'C (theorem text and proof account); separate certificate owner supplies H2/H3 witnesses',
    'replaces baseline t:inputs and the spectral-radius conclusion of p:tail', 'baseline t:inputs/p:tail; OPPORTUNITIES #9/#20/#21; to be written with redesigned certificates', ['t:H1','h:H2','h:H3'],
r"""
\begin{theorem}\label{t:inputs}
At \(c_{\mathrm s}=961/1000\) and \(c_{\mathrm t}=187/200\),
(H1) holds. There exist rational constants
\(C_V\ge1\), \(0<q<1\), \(h_B,h_C>0\), \(0<\rho_0<1\),
and fixed orderings \(\sigma_w\), for which (H2) and
(H3\( _h\)) hold with these constants and orderings.
\end{theorem}
""", True, 'This is the exact required result, independent of certificate format. Existing fallback values are C_V=153, q=3923/4000, h=(1,2769713770832855/2251799813685248), rho_0=99/100, with the archived short-trail orderings and straights-first long order. The historical row bounds imply this slack rational witness. Redesign may supply any rational witnesses satisfying this theorem; downstream interfaces do not fix their numerical values.')

add('Appendix A. Finite probability and operator tools', 'l:CE', 'Finite conditional expectations', 'A',
    'new explicit consolidation', 'MOSPROOF lem:CE; baseline e:lambdaHB', [],
r"""
\begin{lemma}\label{l:CE}
For a positive probability \(\mu\) on a finite product
\(\Omega=\prod_{x\in V}S_x\), with nonempty finite alphabets,
\(E_U\) is a self-adjoint orthogonal projection preserving constants
and \(\mu\). For real or complex \(f\),
\[
 \langle f,(I-E_U)f\rangle_\mu
   =\mu(\operatorname{Var}_U f)=\|f-E_Uf\|_\mu^2,\qquad
 \operatorname{Var}_\mu f=\mu(\operatorname{Var}_U f)
                          +\operatorname{Var}_\mu(E_Uf).
\]
A finite sum \(\sum_a(I-E_{B_a})\), allowing repeated blocks,
has quadratic form \(\sum_a\mu(\operatorname{Var}_{B_a}f)\).
\end{lemma}
""")

add('Appendix A. Finite probability and operator tools', 'l:finitecoupling', 'Couplings, overlap, and Hamming distance', 'A',
    'new explicit consolidation', 'MOSPROOF lem:coupling; OPPORTUNITIES #10', [],
r"""
\begin{lemma}\label{l:finitecoupling}
For probabilities \(p,p'\) on a finite set,
\[
 d_{\rm TV}(p,p')=\tfrac12\sum_z|p(z)-p'(z)|
          =1-\sum_z\min\{p(z),p'(z)\}.
\]
There exists a coupling with disagreement probability equal to this
quantity; every coupling has at least that disagreement probability.
Marginalization cannot increase total variation.
For laws on configurations in a finite \(V\), a marginal coupling
on \(Q\subset V\) can be completed to a coupling of the full laws.
If its disagreement probability on \(Q\) is at most \(\varepsilon\),
the completion can have expected Hamming cost at most
\(|V\setminus Q|+|V|\varepsilon\).
If both laws dominate \(p_0\nu\) for a common probability \(\nu\)
and \(0\le p_0\le1\), their total variation is at most \(1-p_0\).
\end{lemma}
""")

add('Appendix A. Finite probability and operator tools', 'l:surgery', 'Preservation under pair-dependent surgery', 'A',
    'new explicit consolidation', 'MOSPROOF lem:surgery; corrected baseline p:surgery', ['l:CE'],
r"""
\begin{lemma}\label{l:surgery}
Let \(\nu\) couple two positive finite-volume specification laws.
Fix a set \(F\) in the volume. For every input pair, resample \(F\)
from any coupling whose first and second marginals are the two
respective conditional laws given their own complements, and keep
the complements fixed. The resulting law still couples the original
two laws. The chosen coupling may depend on the entire input pair.
A finite composition of such kernels has the same property.
\end{lemma}
""")

add('Appendix A. Finite probability and operator tools', 'l:density', 'Density comparison with a product law', 'A',
    'new; replaces four-site minimum/path constants', 'OPPORTUNITIES #7, adapted to the three new frames', ['l:CE'],
r"""
\begin{lemma}\label{l:density}
Let \(\pi\) be a positive product probability on a finite product,
and \(d\mu=\varrho\,d\pi\), with \(0<m\le\varrho\le M<\infty\).
Then for every \(f\),
\[
 \mathcal D_\mu(f)\ge m\mathcal D_\pi(f),\qquad
 \operatorname{Var}_\mu f\le M\operatorname{Var}_\pi f,\qquad
 \mathcal D_\pi(f)\ge\operatorname{Var}_\pi f .
\]
Thus \(\lambda(\mu)\ge m/M\).
In a conditional frame block, absorbing site weights and every
fixed boundary factor into \(\pi\) gives
\(\lambda(\mu)\ge r_b^{|E(Q)|}\).
\end{lemma}
""", note='Use the variational formula for each integrated conditional variance; comparing only pointwise conditional densities would introduce an unnecessary second density-ratio loss.')

add('Appendix A. Finite probability and operator tools', 'l:comparison', 'Block-to-site comparison', 'A',
    'replaces baseline l:compare by the general finite lemma', 'MOSPROOF lem:comparison', ['l:CE'],
r"""
\begin{lemma}\label{l:comparison}
Let \(\mu>0\) be on a finite product, and let \((B_a)\) be a
nonempty finite labelled family of nonempty blocks.
Suppose the single-site heat bath of every conditional law on each
\(B_a\) has Poincare gap at least \(g>0\), uniformly in its exterior fibre,
and \(\sum_a(I-E_{B_a})\) has Poincare gap at least \(c>0\).
If \(t_{\max}=\max_x\#\{a:x\in B_a\}\), then
\[
 \operatorname{Var}_\mu f\le
             \frac{t_{\max}}{cg}\mathcal D_\mu(f).
\]
Repeated blocks are counted with multiplicity.
\end{lemma}
""")

add('Appendix A. Finite probability and operator tools', 'l:contraction', 'Finite Hamming contraction gives a block gap', 'A',
    'new', 'MOSPROOF lem:contraction; OPPORTUNITIES #1', ['l:CE'],
r"""
\begin{lemma}\label{l:contraction}
Let \(P=A^{-1}\sum_aE_{B_a}\), where \(A\ge1\) is the number
of labels. Suppose \(0<c\le A\) and that for every two input
configurations at Hamming distance one, their \(P\)-output laws
have a coupling of expected Hamming distance at most \(1-c/A\).
Then \(\sum_a(I-E_{B_a})=A(I-P)\) has Poincare gap at least \(c\).
This applies to site-dependent finite alphabets and also to a
one-point product space.
\end{lemma}
""", note='Use the Hamming Lipschitz seminorm and a finite self-adjoint eigenbasis. There is no continuous-time Markov process or path-coupling mixing-time theorem to cite.')

add('Appendix B. The weakened planar topology lemma', 'l:boundaryconn', 'Only star-connectivity of the boundary is needed', 'B',
    'replaces baseline l:boundaryconn', 'baseline topology Steps 1–2; OPPORTUNITIES #3', [],
r"""
\begin{lemma}\label{l:boundaryconn}
If \(A\subset\mathbb Z^2\) is finite, nonempty and star-connected,
and \(A^c\) is star-connected, then
\(\partial_\infty A=\{z\notin A:\operatorname{dist}_\infty(z,A)=1\}\)
is nonempty and star-connected.
Here star-neighbours differ by \(\ell^\infty\) distance one.
\end{lemma}
""", note='Retain the finite mod-two even-edge/triangle argument. Delete the no-diagonal-only-block hypothesis and the nearest-neighbour conclusion for the raw boundary. Neither of those is required after thickening.')

add('Appendix B. The weakened planar topology lemma', 'l:thicken', 'Nearest-neighbour connected crosses', 'B',
    'new', 'OPPORTUNITIES #3', [],
r"""
\begin{lemma}\label{l:thicken}
If \(X_0\) is finite, nonempty and star-connected, then
\(X=\{z:d(z,X_0)\le1\}\) is nearest-neighbour connected.
For any finite \(G\) containing \(X\), every \(0<\vartheta<1\)
satisfies
\[
 \sum_{z\in X}\vartheta^{d(z,G^c)}
       \le5\vartheta^{-1}
                      \sum_{x\in X_0}\vartheta^{d(x,G^c)}.
\]
\end{lemma}
""")

add('Appendix C. Certificate-facing growth and kernel contracts', 'd:memorygrowth', 'A permissible finite-memory upper bound', 'C',
    'kept with edits; allows the true revisit weight', 'baseline §8 H2 definition; OPPORTUNITIES #20 and the certificate-owner handoff', ['d:weights'],
r"""
\begin{definition}\label{d:memorygrowth}
Fix \(m,k\ge1\) and \(\eta\in[1/5,1/3]\).
The states are all length-\(m\) step sequences forming a lattice
trail, modulo translation. Let \(\mathsf M_k(\varsigma,\varsigma')\)
sum the weights of the \(k\)-step continuations making the known
length-\(m+k\) path a trail and ending with window \(\varsigma'\).
Use only this known history: a departure already seen earlier in
it has weight \(\eta\), otherwise use \(x_{\rm type}/3\).
The first new type uses the window's last step.
Let \(A_n(\varsigma)\) be the true total \(\mathsf W\)-weight of
length-\(n\) trails, with their prescribed nonreversing initial data,
whose final window is \(\varsigma\); write \(W_n=\sum_{|w|=n}\mathsf W(w)\).
\end{definition}
""", note='Eta=1/4 recovers the corrected baseline transfer matrix; eta=1/5 is also valid. The certificate owner may use a different proved domination, provided the semantic H2 contract is delivered.')

add('Appendix C. Certificate-facing growth and kernel contracts', 'l:alm', 'Positive transfer witness implies the open-trail bound', 'C',
    'kept with edits (no numerical root)', 'baseline l:alm', ['d:memorygrowth'],
r"""
\begin{lemma}\label{l:alm}
With the preceding definitions, for \(n\ge m\),
\[
 A_{n+k}(\varsigma')\le
       \sum_\varsigma A_n(\varsigma)\mathsf M_k(\varsigma,\varsigma').
\]
If \(h_\varsigma>0\), \(0<q<1\), and
\(\mathsf M_kh\le q^kh\), then (H2) holds with
\[
 C_V=\max\left\{
       \max_{0\le n<m}W_nq^{-n},
       \frac{\max h}{\min h}
                    \max_{m\le n<m+k}W_nq^{-n}\right\}.
\]
\end{lemma}
""", note='Any quotient of windows must separately prove its domination and lift its witness. This lemma does not make an unproved quotient or a printed final row sum into a certificate.')

add('Appendix C. Certificate-facing growth and kernel contracts', 'l:kernelcontract', 'The exact acceptance meaning of a tail certificate', 'C',
    'replaces l:CW and the spectral-radius part of p:tail', 'OPPORTUNITIES #9/#20; nonnegative-series form of baseline e:mT', ['d:kernel','h:H3'],
r"""
\begin{lemma}\label{l:kernelcontract}
For fixed orderings, positive \(h\), and \(0<\rho_0<1\), the
finite-partial-sum inequalities in (H3\( _h\)) are equivalent to
convergence of the corresponding nonnegative row sums and
\(M_1h\le\rho_0h\). In particular every entry of \(M_1\) is finite.
To prove this conclusion by splitting trails into classes, it suffices
to give nonnegative upper bounds covering every length and class,
whose total in row \(X\) is at most \(\rho_0h_X\).
A bound on finitely many lengths without a proved uniform tail
bound does not satisfy this criterion.
\end{lemma}
""", note='The redesigned search owns the representation of those all-length bounds. This plan neither prescribes the old memory-10 quotient nor asserts that a new smaller certificate has succeeded.')

add('Appendix D. Operator-only verification of (H1)', 'l:Iw', 'Integrating out the passage site', 'C',
    'kept with edits', 'baseline l:Iw/e:IcJ; OPPORTUNITIES #2', ['d:pattern','l:moments','l:finitefacts'],
r"""
\begin{lemma}\label{l:Iw}
Let \(Z_w\) be the finite template functional after deleting
the passage site and its incident factors, retaining all other
present bonds and all covered slot factors. Put \(P_{ab}=n_a\cdot n_b\)
for nonremoved sites and zero if either is removed.
For the out-neighbour \(o\) and the other two neighbours \(f,g\),
\[
 Z_{\rm cur}=Z_w[I],\qquad Z_{\rm next}=Z_w[J]>0,\qquad
 I=1+\tfrac13(P_{fg}+P_{fo}+P_{go}),\quad J=1+\tfrac15P_{fg}.
\]
For \(0<c<1\), \(F_c=Z_{\rm cur}-cZ_{\rm next}=Z_w[I-cJ]\), with
\[
 I-cJ=(1-c)+\tfrac13(P_{fo}+P_{go})+(\tfrac13-\tfrac c5)P_{fg}.
\]
Both partition polynomials are affine in each slot vector and
invariant under simultaneous orthogonal transformations of the slots.
\end{lemma}
""")

add('Appendix D. Operator-only verification of (H1)', 'l:leaf', 'Only the elementary leaf reductions', 'C',
    'kept with edits', 'baseline l:leaf; OPPORTUNITIES #2/#21', ['l:35','l:moments','l:finitefacts'],
r"""
\begin{lemma}\label{l:leaf}
In a covered template, integrating a nonremoved tip or corner
with no present internal bond gives a positive factor depending
only on its own slots.
A tip with its one internal bond to \(x\) gives
\(A(1+(3/5)u\cdot n_x)\), \(A>0,\ |u|\le1\).
A corner with exactly one internal bond to \(x\) gives
\(A(1+\rho u\cdot n_x)\), \(A>0,\ |u|\le1\), where
\(\rho=1/2\) for status \(\mathrm U\) and \(\rho=1/3\)
for status \(\mathrm D\).
\end{lemma}
""")

add('Appendix D. Operator-only verification of (H1)', 'd:reduction', 'The two allowed representations and vector groups', 'C',
    'kept as is', 'baseline e:hatF and its representation definitions', ['l:leaf','l:Iw'],
r"""
\begin{definition}\label{d:reduction}
Delete tips and corners with no present internal bond, dropping
their common positive factors. Replace every bonded tip by a
single vector and radius \(3/5\).
In the reduced representation also replace each one-bond corner
by a single vector of radius \(1/2\) or \(1/3\) according to
Lemma~\ref{l:leaf}; in the unreduced representation retain its spin
and two slots. Other bonded corners retain their two slots.
Let \(u=(u_1,\ldots,u_k)\) list these remaining vectors, and define
\(\widehat Z_{\rm cur},\widehat Z_{\rm next}\) by these replacements,
\(\widehat F_c=\widehat Z_{\rm cur}-c\widehat Z_{\rm next}\).
A group is one single vector or the two slots of a retained corner.
\end{definition}
""")

add('Appendix D. Operator-only verification of (H1)', 'c:reduce', 'Reduction to unit-vector positivity', 'C',
    'kept as is', 'baseline c:reduce', ['d:reduction','l:leaf'],
r"""
\begin{corollary}\label{c:reduce}
In either representation, \(\widehat F_c\) is real, affine in
each vector and invariant under simultaneous \(\mathrm O(3)\).
If \(\widehat F_c\ge0\) on \((\mathbb S^2)^k\), then
\(F_c\ge0\) on \((\mathbb S^2)^{20}\).
For each original slot assignment there are a common \(K>0\)
and vectors \(\widehat u\) in the closed unit ball such that
\(Z_{\rm cur}=K\widehat Z_{\rm cur}(\widehat u)\) and
\(Z_{\rm next}=K\widehat Z_{\rm next}(\widehat u)\).
\end{corollary}
""")

add('Appendix D. Operator-only verification of (H1)', 'd:Pauli', 'The Pauli operator and product densities', 'C',
    'kept with edits; replaces coherent spinors on the whole sphere', 'baseline e:Fexp/e:OF; OPPORTUNITIES #2', [],
r"""
\begin{definition}\label{d:Pauli}
For a real polynomial affine in each vector, expand uniquely
\[
 F(u)=\sum_{a\in\{0,1,2,3\}^k}f_a\prod_i u_i^{a_i},
 \qquad u_i^0=1,\qquad
 \mathcal O(F)=\sum_a f_a\bigotimes_i\sigma_{a_i},\quad\sigma_0=I.
\]
For \(\mathcal I\subset\{1,\ldots,k\}\), invert those vectors,
writing \(u^{\mathcal I}\) and \(F^{\mathcal I}(u)=F(u^{\mathcal I})\).
For \(|a|\le1\), put \(\rho(a)=(I+a\cdot\sigma)/2\).
Set \(S_z=\frac12\sum_i\sigma_3^{(i)}\) and
\(S_\pm=\sum_i(\sigma_1^{(i)}\pm\mathrm i\sigma_2^{(i)})/2\).
\end{definition}
""")

add('Appendix D. Operator-only verification of (H1)', 'l:inversion', 'Positivity from a supplied inversion', 'C',
    'kept with edits', 'baseline l:inversion; OPPORTUNITIES #2/#21', ['d:Pauli'],
r"""
\begin{lemma}\label{l:inversion}
For \(|u_i|\le1\), each \(\rho(u_i)\) is positive semidefinite
of trace one, and
\[
 F(u)=\operatorname{Tr}\!\left[
      \mathcal O(F^{\mathcal I})
                 \bigotimes_i\rho((u^{\mathcal I})_i)\right].
\]
Thus a single inversion \(\mathcal I\) with
\(\mathcal O(F^{\mathcal I})\ge0\) implies \(F\ge0\)
on the product of closed unit balls, in particular on unit vectors.
\end{lemma}
""")

add('Appendix D. Operator-only verification of (H1)', 'l:Ostruct', 'The retained operator symmetries', 'C',
    'kept with edits (finite polynomial covariance)', 'baseline l:Ostruct; OPPORTUNITIES #2/#5', ['c:reduce','d:Pauli'],
r"""
\begin{lemma}\label{l:Ostruct}
For \(\mathcal I\) a union of vector groups and
\(\mathcal O=\mathcal O(\widehat F_c^{\mathcal I})\),
the matrix in the standard tensor basis is real symmetric.
It commutes with \(U^{\otimes k}\) for every \(U\in\mathrm{SU}(2)\)
and with \(S_z,S_+,S_-\).
For a retained \(\mathrm U\)-corner pair, if \(\Pi\) projects that
pair onto \(\operatorname{Sym}^2\mathbb C^2\), then
\(\mathcal O=\Pi\mathcal O\Pi\).
For a retained \(\mathrm D\)-corner pair, \(\mathcal O\) commutes
with exchange of its two factors.
\end{lemma}
""")

add('Appendix D. Operator-only verification of (H1)', 'd:exchange', 'Exchange sectors and the central weight', 'C',
    'kept as is', 'baseline definitions preceding l:sector and p:certificate', ['d:reduction','d:Pauli'],
r"""
\begin{definition}\label{d:exchange}
Let \(V\) be the tensor product of \(\mathbb C^2\) for singles,
\(\operatorname{Sym}^2\mathbb C^2\) for retained \(\mathrm U\)-pairs,
and \(\mathbb C^2\otimes\mathbb C^2\) for retained \(\mathrm D\)-pairs.
For each assignment \(\epsilon\) of exchange signs to the
\(\mathrm D\)-pairs, let \(V_\epsilon\) replace each of those
pair factors by its symmetric or exterior square.
If there are \(t\) singles, let \(\kappa=0\) for even \(t\),
\(\kappa=1/2\) for odd \(t\), and
\(V_\epsilon^\circ=\ker(S_z-\kappa I)|_{V_\epsilon}\).
The standard sector basis uses \(e_\pm\) for singles and
\(e_+\otimes e_+\), \(e_+\otimes e_-+e_-\otimes e_+\),
\(e_-\otimes e_-\) for symmetric pairs, with
\(e_+\otimes e_--e_-\otimes e_+\) for antisymmetric pairs.
\end{definition}
""")

add('Appendix D. Operator-only verification of (H1)', 'l:sector', 'Ladder-operator detection of every eigenvalue', 'C',
    'kept with edits (weaker concrete commutation hypothesis)', 'baseline l:sector; OPPORTUNITIES #5', ['d:exchange'],
r"""
\begin{lemma}\label{l:sector}
Let \(V'\) be any tensor sector formed from singles and
symmetric or exterior pair factors as above.
If a Hermitian \(\mathcal O'\) on \(V'\) commutes with
\(S_z,S_+,S_-\), then it preserves the central-weight space
\(V'^\circ\), and its restriction there has the same set of
eigenvalues as \(\mathcal O'\).
In particular \(\mathcal O'\) is positive definite if and only if
that restriction is positive definite.
\end{lemma}
""", note='Use S_+^*=S_-, [S_+,S_-]=2S_z and the norm identity for lowering at positive weight (raising at negative weight). A finite ladder reaches 0 or 1/2 without vanishing. Do not assert equality of multiplicities or invoke a decomposition of arbitrary SU(2) representations.')

add('Appendix D. Operator-only verification of (H1)', 'p:certificate', 'The operator-only certificate soundness statement', 'C',
    'kept as is', 'baseline p:certificate; OPPORTUNITIES #21', ['l:Ostruct','l:sector','l:inversion','c:reduce','d:exchange'],
r"""
\begin{proposition}\label{p:certificate}
Choose either allowed representation and an inversion which is a
union of groups. If the Hermitian form of
\(\mathcal O(\widehat F_c^{\mathcal I})\) is positive definite on
every \(V_\epsilon^\circ\), then \(F_c(m)\ge0\) for every
\(m\in(\mathbb S^2)^{20}\).
Positive definiteness is required only on these supported sectors;
the operator may vanish on the discarded antisymmetric
\(\mathrm U\)-pair subspaces.
\end{proposition}
""")

add('Appendix D. Operator-only verification of (H1)', 'l:integercheck', 'Exact integer congruence and positivity', 'C',
    'new explicit consolidation of the retained arithmetic step', 'baseline e:intscale/e:Meps and Bareiss paragraph', ['p:certificate','l:moments'],
r"""
\begin{lemma}\label{l:integercheck}
For \(c=p/q\in(0,1)\) rational with positive integers \(p,q\),
choose a positive integer \(D_0\) clearing the coefficients of
\(3D_0\widehat Z_{\rm cur}\) and \(5D_0\widehat Z_{\rm next}\).
In the integer-coordinate central-sector basis, let \(A_\epsilon\)
and \(A'_\epsilon\) be the Hermitian-form matrices of their
inverted Pauli operators. These are symmetric integer matrices.
The form of \(\mathcal O(\widehat F_c^{\mathcal I})\) on the sector
is positive definite if and only if
\[
 M_\epsilon=5qA_\epsilon-3pA'_\epsilon
\]
is positive definite. This is equivalent to positivity of all its
leading principal minors. More explicitly, for a size-\(t\) matrix
set \(A^{(0)}=M_\epsilon\), \(p_{-1}=1\), and for \(0\le j<t\)
set \(p_j=A^{(j)}_{jj}\) and update the trailing entries by
\[
 A^{(j+1)}_{il}
    =\frac{p_jA^{(j)}_{il}-A^{(j)}_{ij}A^{(j)}_{jl}}{p_{j-1}}
       \quad(i,l>j).
\]
As long as preceding pivots are nonzero, each division is exact
in the integers and \(p_j\) is the leading principal minor of
order \(j+1\). Acceptance requires every division exact and every
pivot positive.
\end{lemma}
""", note='These are congruence/form matrices in an unnormalized basis, not an orthonormal coordinate matrix. Prove exact reconstruction from pattern data and completeness separately; certificate acceptance alone must not become an axiom. The largest corrected selected split block is 179, not the historical combined 245.')

add('3. The quantum model, uniqueness, and positive frames', 'l:qmod', 'The determinant modulus identity', 'A',
    'kept as is (promoted from e:qmod)', 'baseline e:qmod', ['d:poly'],
r"""
\begin{lemma}\label{l:qmod}
For unit spinors \(\zeta,\zeta'\) with
\(\zeta\zeta^*=(I+a\cdot\sigma)/2\) and
\(\zeta'\zeta'^*=(I+a'\cdot\sigma)/2\),
\[
 |\zeta_1\zeta'_2-\zeta_2\zeta'_1|^2=(1-a\cdot a')/2 .
\]
\end{lemma}
""")
S.insert(next(i for i,x in enumerate(S) if x['label']=='d:framemodel'), S.pop())

add('3. The quantum model, uniqueness, and positive frames', 'l:quantumfibre', 'The signed local comparison', 'A',
    'kept as is (promoted from the corrected proof and e:QDcomp)', 'baseline t:QD proof/e:QDcomp; STRENGTHEN-ALL e:cx', ['l:qmod','l:divisibility','l:tight','d:framemodel'],
r"""
\begin{lemma}\label{l:quantumfibre}
Fix \(x\), write \(q_e=\epsilon_{e,x}q_{xy}\) for \(e=\{x,y\}\),
and set
\[
 c_x=\prod_{e\ni x}\epsilon_{e,x},\quad
 \beta_x(t;\sigma)=\prod_{y\sim x}q_{xy}(\zeta(t),\zeta(\sigma_y)),
 \quad \rho_x=c_x\prod_{e\not\ni x}q_e .
\]
All products are evaluated at the corresponding frame spinors.
Then \(\iota B=\beta_x\rho_x\), and if
\(\psi=(\prod_{e\ni x}q_e)\chi\) with \(\chi\) independent of \(z_x\),
then \(\iota\psi=c_x\beta_x\,\iota\chi\).
Let \(\mathcal P_x\) be the fibrewise orthogonal projection in
\(\ell^2(\Omega,\pi)\) onto the span of \(\beta_x\), and put
\(Uf=f\,\iota B/\|B\|\).
The map \(U:L^2(\mu^{\rm af})\to\ell^2(\Omega,\pi)\) is unitary,
\(UE_x=\mathcal P_xU\), and
\[
 \|(I-\mathcal P_x)\iota\varphi\|
            \le\|(I-\Pi_{\mathcal S_x})\varphi\|.
\]
\end{lemma}
""", note='The notation iota chi means evaluation even though the residual polynomial is not itself a full-degree physical state. Its evaluation is multiplicative; no isometry for that residual degree is asserted.')
S.insert(next(i for i,x in enumerate(S) if x['label']=='t:QD'), S.pop())

# Tighten wording at the two otherwise easily confused block-gap occurrences.
for x in S:
    if x['label']=='t:QD':
        x['deps'].append('l:quantumfibre')
    if x['label']=='l:planeenergy':
        x['deps'].append('l:density')
        x['body']=x['body'].replace(
            'every conditional single-site\n+heat-bath law in',
            'the single-site heat bath of every conditional block law in')
        x['body']=x['body'].replace(
            'every conditional single-site\nheat-bath law in',
            'the single-site heat bath of every conditional block law in')
    if x['label']=='t:periodic':
        x['body']=x['body'].replace(
            'all conditional single-site laws on \\(Q\\) have Poincare gap at least',
            'the single-site heat bath of every conditional law on \\(Q\\) has Poincare gap at least')
    if x['label']=='t:cutMOS':
        x['body']=x['body'].replace(
            r"""One may choose \(M_\star\) sufficiently large that, for all
integers \(u\ge M_\star\),
\[
 u^{1/4}\ge s_0,\qquad
 4(2u+1)^2\theta^{u^{1/4}/12-1}\le1.
\]
With this choice the displayed \(p_0\) is valid.""",
            r"""There exists an integer \(M_\star\ge1\) for which (W) holds
with this displayed choice of \(p_0\).""")
        x['note']+=' Choose M_star so that every later u meets the geometric s_0 threshold and 4(2u+1)^2 theta^(u^(1/4)/12-1) <= 1.'
    if x['label']=='l:Mtheta':
        x['interface']=True

BASEMAP = {
't:main':('replace','t:main'),
'l:edge':('keep','l:edge'),
'l:divisibility':('edit','l:divisibility (torus scope)'),
'd:frame':('edit','d:frame'),
'l:tight':('keep','l:tight'),
't:QD':('edit','t:QD and l:quantumfibre'),
'r:QDgeneral':('remove','author scope: no general-graph theorem or extension remark'),
't:K':('remove','replaced by t:periodic; OPPORTUNITIES #1'),
'l:commute':('remove','old Knabe proof no longer used; replaced by finite block contraction'),
'l:fibre':('remove','old Knabe proof no longer used; replaced by l:comparison'),
'l:autocorr':('remove','old Knabe proof no longer used; replaced by periodic placement counts'),
'r:Kpins':('replace','l:boxlift uses two spare sites; its stronger size hypothesis avoids repeated exterior images'),
'l:boxcell':('replace','l:boxlift, without cells'),
'l:compare':('replace','l:density and l:comparison, at physical-site scale'),
't:MOS21':('remove','replaced by l:stopped/l:hamming/t:periodic; no cited mixing theorem'),
't:MO41':('remove','replaced by l:stopped/l:hamming/t:periodic; no compatible-union theorem'),
'r:finiteS':('remove','the finite proof treats site-dependent alphabets directly'),
'l:shellgeom':('edit','l:shellgeom, including clearance'),
'd:W':('edit','d:W, all colourings and physical translates'),
'p:surgery':('edit','p:surgery as corollary of l:stopped'),
'c:gapcell':('replace','t:periodic; no box-gap detour'),
't:mainW':('replace','t:mainW'),
'l:35':('edit','l:35, finite functional and explicit tip range'),
'l:exact':('edit','l:exact'),
'l:cut':('edit','l:cut with common minorization'),
'h:P':('edit','h:P, same quantifiers and distances, finite functional'),
'l:removal':('replace','l:removal with constants 1,4,2 and one seed'),
'l:cutgeom':('replace','l:cutgeom, site scale and thickening'),
'l:Xconn':('replace','l:Xconn and l:thicken; no diagonal-block test'),
't:cutMOS':('replace','t:cutMOS with l_0=64 and p_0=exp(-2E)'),
'r:Pweak':('remove','replaced by the adopted narrowed exponential interface h:P; no polynomial-decay corollary'),
'd:domain':('edit','d:domain, no scalar mass but protected-boundary distinction retained'),
'l:stepid':('replace','l:stepid, U k<=3 and D k<=1 only'),
'p:pairwalk':('edit','p:pairwalk, admissible starts and endpoint degree bound'),
'l:response':('keep','l:response for U departures; D response is zero'),
'l:exposure':('edit','l:exposure; revisit coefficient moved to a_D'),
'd:pattern':('edit','d:pattern, corrected covered rules retained'),
'h:H1':('edit','h:H1, direct inequalities, no infimum'),
'l:local':('edit','l:local, finite polynomial tip covariance'),
'h:H2':('edit','h:H2, positive q and explicit nonreversing convention'),
'l:onepoint':('edit','l:onepoint; preserve the sum of maxima'),
'l:closure':('edit','l:closure; no mass-reset phrase'),
'h:H3':('replace','h:H3, positive-vector/all-partial-sums witness'),
'l:Mtheta':('replace','l:Mtheta, same h and no spectral radius'),
't:rec':('edit','l:recineq, l:renewal, t:rec'),
'r:typedep':('remove','replaced by the narrowed fixed-coefficient kernel contract; unused type-dependent variant omitted'),
't:inputs':('replace','t:inputs, exact semantic input contracts'),
'l:alm':('edit','l:alm, same domination with rational q^k witness'),
't:H1':('edit','t:H1, operator-only proof'),
'r:H1sharp':('remove','replaced by operator-only H1; no c(pi) optimization/closed-form branch'),
'l:boundaryconn':('replace','l:boundaryconn gives star-connectivity; l:thicken gives nearest-neighbour connectivity'),
'l:CW':('remove','replaced by h:H3/l:kernelcontract; no spectral-radius conclusion'),
'l:memdom':('remove','old certificate-specific proof replaced by semantic H3 contract; redesigned tail proof belongs to certificate owner'),
'l:remainder':('remove','old certificate-specific proof replaced by semantic H3 contract; support-aware fallback rules preserved in risk list'),
'p:tail':('replace','h:H3, l:kernelcontract and t:inputs; old row bounds are fallback provenance'),
'r:tailtypedep':('remove','replaced by narrowed fixed-coefficient H3 contract; unused numerical variant omitted'),
'l:Iw':('edit','l:Iw, finite functional'),
'l:leaf':('edit','l:leaf, finite functional'),
'c:reduce':('keep','c:reduce'),
'l:inversion':('edit','l:inversion, product density matrices'),
'l:Ostruct':('edit','l:Ostruct, polynomial covariance and concrete commutators'),
'l:sector':('edit','l:sector, ladder-operator proof'),
'p:certificate':('keep','p:certificate'),
'l:radius':('remove','replaced by operator-only H1; elementary l:35 and l:leaf remain'),
'p:closed':('remove','replaced by operator-only H1; closed-form/pruning/FKG branch omitted'),
}

INTRO = r"""
STATUS: COMPLETE

# Integrated revision contract

This is a complete proof-writing plan, not the revised proof or a Lean verification. Every mathematical assertion to appear in the revised paper is specified below, with an owner, proof source and dependencies. “To be written” assigns a proof obligation; it does not turn an input into an axiom. The final main theorem is unconditional. The separately assigned certificate work must discharge its computational theorems before that theorem is accepted.

The baseline is the corrected manuscript at **9faa0eee768bef27a483cf7469c65c3e9958a84e**. This plan supersedes the incompatible architecture in the strengthening supplement: it keeps the three frames, all-parity torus measure and local gauge, and replaces both its cell/box route and the baseline Knabe route by one periodic block argument on physical sites.

## Sources read and precedence

- [Corrected manuscript main.tex](/home/ubuntu/aklt/manuscript-corrected/main.tex), all eight section files and all four appendix files.
- [STRENGTHEN-ALL proof.tex](/home/ubuntu/aklt/reports/STRENGTHEN-ALL/proof.tex) and [report.md](/home/ubuntu/aklt/reports/STRENGTHEN-ALL/report.md).
- [REF-SA-A](/home/ubuntu/aklt/reports/REF-SA-A/report.md) and [REF-SA-B](/home/ubuntu/aklt/reports/REF-SA-B/report.md).
- [MOSPROOF proof.tex](/home/ubuntu/aklt/reports/MOSPROOF/proof.tex), [report.md](/home/ubuntu/aklt/reports/MOSPROOF/report.md), and [REF-MOS](/home/ubuntu/aklt/reports/REF-MOS/report.md).
- [OPPORTUNITIES](/home/ubuntu/aklt/reports/OPPORTUNITIES/report.md), all entries; the adopted package is the one fixed by the author.

The author's decisions take precedence. The two referee repairs are incorporated: every finite-energy hypothesis explicitly has \(\alpha\in(0,1]\); references to the cut construction use labels, not the incorrect “Section 5.4” locator. All retained baseline corrections remain binding, including those whose replacement proof uses a narrower interface.

## Paper order and file ownership

| Order | Contents | Owner / proposed source file |
|---|---|---|
| 1 | Model, unconditional theorem, roadmap, finite conventions | A: sec1-result.tex |
| 2 | Finite fourth moments, pin/removed-site sums, positivity, three-factor mean, quadrature, (P) | C: sec2-moments.tex |
| 3 | Polynomial space, edge lemma, torus uniqueness, frames, quantum comparison, finite energy, local gauge | A: sec3-quantum-frames.tex |
| 4 | Physical windows, stopped coupling, one square scale, direct periodic criterion, main-theorem assembly | A: sec4-periodic-gap.tex |
| 5 | Shared shell geometry, cut factorization, removal, thickened site cut, (P) implies (W) | B: sec5-window.tex |
| 6 | Mass-free trace, pair identity, response coefficients, covered patterns, H1/H2, one-point bound | C: sec6-walks.tex |
| 7 | Ordinary-domain closure, terminal defect, fixed-order kernel, positive witness, renewal, (P) | C: sec7-recursion.tex |
| 8 | Exact computational theorem statements and certification scope | C: sec8-inputs.tex |
| A | Finite conditional expectations, coupling, density/block comparison, finite contraction | A: app-finite.tex |
| B | Star-connected boundary and connected thickening | B: app-topology.tex |
| C | Semantic growth/tail contracts; optional search implementations are outside the paper contract | C: app-input-contracts.tex |
| D | Operator-only H1 reduction, ladder sector lemma, integer positivity | C: app-local-operator.tex |

The order intentionally permits forward references, as the baseline does. In §4 the final assembly cites §8 and §7, then §5. No proof in §§2 or 5–8 may use a classical or quantum gap conclusion. There is no Knabe section, no cell lattice, no compatible-volume theorem, no rectangular-box-gap detour, and no explicit-constant appendix.

All distances in the analytic part are ambient plane distances. The physical torus is used only in A. Pins in C/B are arbitrary unit vectors on original legs; finite energy in A concerns admissible frame letters. These are different quantifiers and must not be interchanged.

## Mathematical dependency chain and choices

\[
 \text{operator-only H1, open-trail H2, positive-vector H3}_h
 \Longrightarrow (P)
 \Longrightarrow \text{physical-site windows at every translate}
 \Longrightarrow \text{stopped square coupling with small Hamming cost}
 \Longrightarrow \text{periodic block gap}
 \Longrightarrow \text{physical-site gap}
 \Longrightarrow \text{quantum gap}.
\]

Uniqueness for every \(L,N\ge3\) has a separate algebraic proof. It uses neither the numerical inputs nor frames.

The frozen choices are the three 12-letter frames; \(b=(5-\sqrt5)/505\); the physical lower bound \(\alpha=12^{-1}(b/(2-b))^4\); \(l_0=64\); \(c_{\mathrm s}=961/1000,c_{\mathrm t}=187/200\); and \(\bar\alpha=18094/100000,\bar\beta=36751/100000\). The choices proceed as follows:

1. The certificate theorems supply \(C_V,q,h,\rho_0\) and fixed orderings. The shifted-witness and renewal lemmas supply \(\theta,A\).
2. The site cut supplies \(p_0,M_\star\). Independently the frames supply \(\alpha,r_b,g_\star>0\).
3. Choose one integer \(n\) as in l:hamming, and one square radius \(M=n^8\).
4. Only then choose physical torus periods \(L,N\ge2M+3\), any proper colouring, any block placement and any exterior fibre.

The formulas inside statements are proof interfaces and normalization checks. They do not change the author's decision to state the final constants existentially.

# Interface ownership and allowed citations

The companion [interfaces.tex](interfaces.tex) is a standalone amsart statement document, without proofs. Its text is generated from the same statement registry as the inventory below. An export is the entire quantified statement, not a diagram arrow or an informal consequence.

| Boundary | Exact exports / imports |
|---|---|
| Shared notation | d:model, d:moment, d:poly, d:frame, d:framemodel, d:shells; these definitions are frozen before writing |
| C to A | l:moments (for tight frames); t:inputs and t:rec (for final assembly) |
| C to B | d:pinmodel, l:finitefacts, l:35, l:exact, h:P, t:rec |
| A to B | l:threeframes, d:framemodel, l:planeenergy (consistency, positivity and actual alphabets) |
| B to A | l:shellgeom and t:cutMOS, consuming d:W |
| C to computational owner | d:domain, d:pattern, h:H1, d:weights, h:H2, d:kernel, h:H3, t:H1 and t:inputs; l:Mtheta is included to expose exactly how the witness will be consumed |

A may not cite B's cut/removal/topology proofs or C's closure/expansion proofs directly. B may not cite the walk recursion, individual H1 patterns, or A's periodic argument; it consumes (P) and the common moment/positivity interface. C may not cite a window theorem, frame finite energy or gap. Within its own lane a writer may use every assigned internal statement.

The shared definition of (W) belongs to A's consumer contract, and B proves it. The pure shell-geometry lemma belongs to B and is exported explicitly because A's stopped coupling needs it. The common finite moment functional belongs to C; A's design calculation may cite its exact moment theorem. This arrangement allows all three lanes to write independently without waiting for another lane's proof text.

## Lane A — model, frames, uniqueness, quantum/classical comparison, periodic gap

Write §§1, 3, 4 and Appendix A. Supply every A-owned statement in the inventory. In §4 prove the stopped finite coupling for site-dependent alphabets, the one-radius Hamming estimate, the periodic placement counts, the finite eigenfunction contraction and the fibre comparison; then assemble t:main from the exported C and B theorems.

Allowed cross-lane citations: the shared definitions and C's l:moments, t:inputs, t:rec; B's l:shellgeom and t:cutMOS. A can use d:W as an assumed property while proving t:mainW. No cited MO94/MOS94 theorem is allowed; MOSPROOF supplies proof text, not a black box.

Acceptance criteria:

- The final t:main has no parity condition, no hypothesis, uniqueness for every \(L,N\ge3\), and a volume-independent positive gap once both periods exceed one threshold.
- The algebraic uniqueness proof is torus-only and works at period three. Prove divisibility in a UFD with nonassociate edge determinants; do not require comaximal ideals.
- Use the specified three rotated frames and the new exact \(b\), finite monomial norm, finite spinor choices, squared modulus and reference weights. Preserve both local orientation signs.
- Never gauge an odd torus globally. Lift each actual conditional physical square first. \(L,N\ge2M+3\) guarantees the required one-neighbourhood injection.
- Use \(\alpha=12^{-1}r_b^4\), and density comparison with boundary factors in the product reference law. The block gap is \(g_M=r_b^{2(2M+1)(2M)}\); no cell constant or cell heat bath appears.
- The stopped coupling uses conditional success and keeps both full marginals. Treat empty windows, singleton state spaces, zero residual overlap and \(\delta=1\) explicitly.
- Count block labels at rate one: containing count \(T_M\), boundary overcount \(S_M\), block gap \(T_M-S_MK\), site multiplicity \(T_M\). Recover the factor \(499/1000\) after the quantum comparison.

## Lane B — (P) to physical windows

Write §5 and Appendix B. Establish l:shellgeom independently of mixing, including parallel-side clearance. Redo the taper on physical sites with \(l_0=64\), raw boundary \(X_0\), and nearest-neighbour thickening \(X\). Prove finite partition factorization, common minorization, the one-seed removal bound, the exact geometric statement and t:cutMOS.

Allowed cross-lane citations: C's d:moment/d:pinmodel, l:moments, l:finitefacts, l:35, l:exact and h:P; A's shared frame family, l:threeframes and l:planeenergy. Treat \(\mathsf P(A,\theta)\) as the only analytic response premise. The proof of that premise is not needed.

Acceptance criteria:

- The exported window theorem covers every proper plane colouring, every translate, every indicated nonexceptional integer index and every pair of admissible boundaries. No translation invariance is inferred.
- Preserve original-leg pin conventions; new holes have no pins. Distances in removal are to the original \(S(G)\).
- Prove every stated site-scale depth and count. In particular raw near depth is \(\max(t,16)-2\), not the cell-scale doubled expression. Retain the signed-depth argument excluding coincident sides.
- Prove raw boundary star-connectivity and connectedness of its crosses. Do not use or reintroduce the no-diagonal-only-block test.
- The thickened cut is nonempty, connected, disjoint from the window and protected layer, and separates the pieces required by l:cut.
- Keep one seed with its four-spin cost. Constants \(1,4,2\), the factor \(5/\theta\) for thickening and \(p_0=e^{-2E}\) must match the interfaces.
- Transfer only the summed-out partition functions. The common reference window law retains actual frame weights and is strictly positive.

## Lane C — walk, recursion, (P), operator-only H1, computational contracts

Write §§2, 6–8 and Appendices C–D. Prove the finite moment identities, restricted insertion/covariance statements, positivity, three-factor bound and covering-tip range. Rewrite traces without scalar masses and prove the narrowed pair expansion and all ordinary-domain/terminal-defect closure statements. Keep the numerical lattice kernel exactly. Prove the shifted positive witness and finite-iteration renewal bound. State the exact certificate theorems and coordinate their eventual proofs with the separately assigned computational owner; do not run a new H2/H3 search.

Allowed cross-lane citations: only the frozen common definitions. C proves (P) before and independently of any use of the physical frame specification, windows or a gap. The explicit base icosahedron coordinates are part of the shared definition, not an imported mixing fact.

Acceptance criteria:

- No surface measure, all-orders moment theorem, continuous-spin disintegration or arbitrary-function rotational invariance is needed. Every used inserted observable meets the separate degree-four bound.
- Only U starts with at most three factors or D starts with at most one present bond are expanded. The second target \(e\in S\) has already lost an arrival bond. There is no silent initial two-bond D case.
- Show the exact equivalence between coefficients \(3^{-n}(3/5)^r\) and the new \(3^{-N_U}5^{-N_D}\). D departures have ratio one and response zero. Do not change H2 weights or the closed-trail kernel.
- Preserve the corrected kept-set condition, full U kept sets, covering U tips, both corner slots, the protected boundary, the live endpoint, and the sole terminal boundary defect.
- Ordinary response suprema remain uniform over all consistent domains and arbitrary unit pins. Auxiliary networks are used only in the two stopped expansions.
- Preserve the absent incoming bond and forbidden initial reversal in every open-trail application, the common sum-of-maxima bound, and the at-most-twelve exceptional U departures anywhere in the second trail.
- The same fixed orderings and positive vector must work at \(\theta=1\) and after shifting. No Perron–Frobenius theorem, spectral-radius continuity or truncated-supremum fixed-point construction is needed.
- Appendix D has one operator path for every corrected pattern. Keep l:35 and elementary leaf bounds; omit general FKG radii, pruning and closed-form minimization. Use product density matrices and the ladder proof.
- The H1 checker must establish coverage of the corrected raw rules and exact threshold/type agreement, not merely the reported record count. Preserve exact form-matrix reconstruction, integer congruence, all exchange sectors, exact division and positive pivots.
- Computational inputs must conclude the actual all-length mathematical H2 and H3_h contracts in t:inputs. Approximate diagnostics, a finite prefix or an unchecked tail summary cannot discharge them. No new certificate-search implementation is assigned to these proof-writing lanes.

# Full statement inventory

Each entry gives the exact LaTeX text intended for the paper. The “Interface” flag means it is reproduced in interfaces.tex; permitted consumers are specified above. The rest are internal lane statements. Source locators use baseline labels, not historical PDF numbers.
"""

EQUATIONS = r"""
## Equation-only material and unnumbered baseline assertions

The following mapping supplements the numbered-statement audit; it prevents losing corrected definitions that happened not to be theorem environments.

| Baseline material | Revised location / disposition |
|---|---|
| e:H, e:B | d:model; nonzero B and frustration-freeness in p:toruskernel |
| e:zeta, e:Vinner | d:poly; finite spinor choices and monomial norm replace the sphere definition |
| e:star | l:star |
| e:icodod, old ico/dodeca design proof | replaced by d:moment, l:moments and l:threeframes |
| e:qmod | l:qmod, with no global spinor selection |
| e:mucirc, e:lambdaHB | d:framemodel and t:QD; reference pi remains unnormalized |
| e:QDcomp and corrected c_x factorizations | l:quantumfibre |
| e:muD, e:QDrot | removed global gauge; replaced by the antiferromagnetic torus law and l:boxlift |
| e:muDW | d:framemodel, all proper plane colourings |
| all §3 criterion equations e:MRF–e:Lsquare | removed with Knabe, including t(ell), kappa_ell and weighted/flat autocorrelations; the positive torus product law remains d:framemodel |
| cell definitions, offsets and compatible scales; e:SM/e:MOS22 | removed; no cells, compatible volumes or strong-mixing assertion remain |
| e:shells/e:W | d:shells/d:W, now physical sites |
| e:prop21 | p:surgery, retained as a short corollary; l:stopped is the consumed stronger statement |
| e:Zpin, original S(G), positivity/conditional independence | d:pinmodel, l:finitefacts; pins stay unit vectors |
| e:moments and arbitrary-order free positivity | replaced by l:moments and degree-admissible l:finitefacts; no assertion for arbitrary high-degree inserted observables |
| e:cutcost/e:windowlaw/e:cutratio | l:cut, including actual W_B, factorization, full support and common minorization |
| e:P | h:P |
| e:removal/e:Ij/e:telescope | l:removal; same integration/telescoping with coarser constants and seed retained |
| e:Ucut/e:Xcut/e:Ualt/e:cutsum | d:thickcut/l:cutgeom; no U-prime expansion to cells |
| e:ZD and scalar trace mass | d:domain/d:trace; mass field replaced by a_D |
| e:pairwalk/e:IJ/e:lambda/e:exposure | p:pairwalk/d:ratios/l:response/l:exposure |
| e:cpi and numerical minimization claims | removed; h:H1 is the direct pointwise inequality |
| unlabelled covered-pattern/terminal-defect remark in §6 | l:terminalcover, with the twelve-exception correction retained |
| e:FX/e:kernel/e:recineq | d:pairenv/d:kernel/l:recineq |
| fixed-point/truncated Phi_N calculation | replaced by l:renewal |
| e:mT, phase weights, old memory quotient implementation | no fixed certificate architecture in the revised paper; semantic contracts in d:kernel/h:H3/Appendix C replace it |
| tab:tail and its exact assembly | replaced as a required assertion by t:inputs; historical row bounds are fallback provenance only |
| e:Fc/e:Zw/e:IcJ/e:hatF | l:Iw/d:reduction |
| e:Fexp/e:OF/e:inversion | d:Pauli/l:inversion, using product density matrices |
| e:intscale/e:Meps | l:integercheck; positive scale is 15 D_0 q |
| e:rhoUD/e:ZVbeta/e:subsets/e:FKGstep/e:closed/e:Rmu/e:5469 | removed with the closed-form/FKG branch; not needed to prove operator-only H1 |
| tab:H1, selected minima/margins, sharpness diagnostics | omit from the revised proof; no global optimum was certified. If ever restored as remarks, all baseline qualifications must be restored verbatim |
| app-constants.tex | removed; useful constants are defined at their point of use; no explicit-constant appendix |
| historical arithmetic/provenance paragraphs | replace by exact mathematical input targets plus the eventual certificate reconstruction/coverage/soundness account; do not label archived floating computations as kernel-checked |

The supplement's general-graph kernel/dimension theorem, general-graph QD clause, small sizes below three, classical rectangle corollaries, and open-boundary dimensions are not imported. Neither are infinite-volume, thin-torus, skew-quotient, clustering, perturbation or explicit-numerical-gap additions. These omissions implement the author's scope, not contrary mathematical claims.

## Baseline statements removed as separate assertions

The audit table above gives the replacement for every removed numbered statement. In particular the removed set comprises t:K, l:commute, l:fibre, l:autocorr, r:Kpins, l:boxcell, l:compare, t:MOS21, t:MO41, r:finiteS, c:gapcell, r:QDgeneral, r:Pweak, r:typedep, r:H1sharp, l:CW, l:memdom, l:remainder, p:tail, r:tailtypedep, l:radius and p:closed. Some have direct replacement statements under new labels; the table distinguishes replacements from omissions.

No other baseline theorem, lemma, definition, hypothesis or corollary is silently dropped. “Kept with edits” means exactly the statement printed in this inventory, with the specified finite-functional or narrowed-domain change. Unused closed forms and type-dependent numerical variants stay archived rather than becoming an unassigned second proof branch.
"""

RISKS = r"""
STATUS: COMPLETE

# Integration risks and resolutions

All adopted items fit after the changes below. The principal new proof obligation is the physical-site cut geometry, which was proposed but not written out in the refereed supplements. Its exact target is in PLAN.md; it is assigned to B rather than assumed.

| Adopted item / risk | Recommendation and required resolution |
|---|---|
| #1 + #16: the refereed material proves a cell/box route, not the chosen periodic site route | Use the proved stopped finite coupling, rederive the site window and count physical periodic translates. Prove t:periodic directly. Do not cite a rectangular-box theorem, remove “cell” by a word substitution, or retain Knabe as a hidden premise. |
| #3 + #16: losing the factor two in geometric distances | Fix l_0=64. Prove raw near depth max(t,16)-2, raw depth at least 14, thickened depth at least 13, the 48-per-level count and the stated far term. These conservative bounds leave clearance for every original pin and for the window. The exact count and signed-depth exclusion still require a written site-scale proof. |
| #3: raw boundary need not be nearest-neighbour connected | Export only star-connectivity from the planar topology lemma. Prove the crosses are nearest-neighbour connected, and remove the crosses from both cut-side pieces. Do not reuse the old G_1 unchanged after thickening, or assume the discarded no-diagonal-only-block property. |
| #2: finite support has no full rotational invariance | Use covariance only for polynomials of separate degree at most four. In tip covering, prove the range of the explicit three-field mean by moment identities, not rotation invariance of a discrete probability law. There is no claim about arbitrary functions on the support. |
| #2: inserted observables can exceed fourth degree | Restrict U departures to at most three factors and D departures to at most one present bond. Require the pair target’s degree bound. The second target e in S has already lost its arrival bond. Delete the unused k=4 step identity and all-orders inserted-observable positivity. |
| #2: arbitrary unit pins can zero individual finite weights | Prove positive normalizers by a finite sequential choice avoiding at most four forbidden letters per site. Use finite conditional identities only on positive fibres. Never infer a uniform letter lower bound for arbitrary unit pins; alpha is for the separated physical frames only. |
| #4: mass movement is not a literal replacement in the general old pairwalk statement | Narrow the starts as specified; delete the initial two-bond D case. Ratios at admissible D departures become one, their response is zero, and 1/5 moves into the coefficient. Prove the coefficient identity before comparing to the old lattice kernel. Auxiliary terminal networks and original legs remain essential. |
| #7: the adopted four-site comparison has no cell to act on | Repurpose its density lemma for each whole physical square. Absorb fixed boundary fields into a product reference law and compare only internal bonds. Use alpha=12^(-1) r_b^4 and g_M=r_b^[2(2M+1)(2M)]. Do not retain the old 9^(-4), old gamma_+, beta^5/4, or any cell factor in the final constant. |
| #9/#20: a spectral-radius number or a rounded test vector is not the new premise | Require the exact all-partial-sums positive-vector inequality with rational witnesses, fixed orderings and the unchanged dead-pair kernel. The old dyadic h_C is 2769713770832855/2251799813685248, not literally 123/100; use the dyadic fallback or prove the replacement with its slack. Shift the same witness to theta<1. |
| #9: renewal must control negative shifts and the remainder | Extend F constantly to negative integers, use source 2 there, and bound the finite-iteration remainder in the unweighted h norm. Only then pass to a geometric series. The source exponent is q^(2d) and the safe C_T remains 2(12/5)^24(C_V/(1-q))^2. |
| #20: narrowing the numerical inputs must not weaken domain closure | Keep the supremum over all ordinary consistent domains and all unit pins. Retain full U kept sets, two kept D bonds, covering U tips, filled missing corner slots, the absent incoming bond, the common maximum majorant and twelve exceptional departures anywhere in the second trace. No supremum over terminal auxiliary networks is needed or justified. |
| #21/#5: operator-only H1 must preserve the corrected pattern coverage and zero sectors | The archived operator-only route covers all 7,962 representatives; prove that those represent the corrected raw class. Keep every exchange sector and discard U antisymmetric sectors only after proving two-sided annihilation. The ladder lemma detects eigenvalues as a set, not with multiplicity. The corrected largest selected split block is 179; 245 is a historical combined diagnostic. No highest-weight compression is assumed. |
| #6: Cartan multiplication still needs identification of the physical projector | Prove diagonal evaluation is onto V_8, its kernel is the determinant image, and the adjoint image is exactly total spin 4 with the chosen monomial norms. If library convenience later favours the baseline Clebsch–Gordan proof, its edge-kernel statement is unchanged; this is an internal proof choice, not a new interface. |
| All parity sizes and uniformity | Keep the torus measure antiferromagnetic and the gauge local to a lift. Prove windows for every plane colouring and translate. Choose constants before periods, placement or boundary. Period three is needed for algebraic uniqueness, while the periodic gap proof uses its larger fixed threshold. |
| Redesigned H2/H3 certificates are separately owned and not yet delivered here | Keep the semantic t:inputs theorem fixed and leave production search to its owner. The current plan makes no claim that a new small certificate or a kernel check has succeeded. Acceptance of the eventual unconditional theorem requires actual proofs of these inputs; a finite prefix, numerical diagnostic or unsupported Bellman vector is insufficient. |
| Reusing any old tail implementation during redesign | Preserve the corrected old validity ranges: mode A only through 107 (only even lengths through 106 are used); mode B for lengths above 53; the 108-and-up contribution cannot use mode A. With a nonnegative sub-invariant vector, verify zero support of V_T where z=0 and divide only on z>0. Use exact rational assembly with the exact dyadic denominator and correct production provenance. None of these old implementation facts is a replacement for a redesigned proof. |
| Scope and constants | Omit the general-graph ground-space theorem, all infinite-volume and thin-torus results, and the explicit-constant appendix. Keep only symbolic internal bounds needed for comparison and positivity. Do not advertise a contraction witness such as 0.91825 as a quantum gap. |

The REF-MOS repair is mandatory in every standalone probability/gap lemma using a reciprocal of alpha or a positive derived gap. The REF-SA-B repair is addressed by stable source-label references. These are incorporated requirements, not outstanding questions.
"""

def write_files():
    labels={x['label'] for x in S}
    assert len(labels)==len(S), 'duplicate labels'
    for x in S:
        missing=set(x['deps'])-labels
        assert not missing, (x['label'],missing)
    # Reject hidden circular dependencies in the complete theorem graph.
    bylabel={x['label']:x for x in S}
    done=set()
    def visit(label, path):
        assert label not in path, ('cycle',path,label)
        if label in done:
            return
        for dep in bylabel[label]['deps']:
            visit(dep,path+[label])
        done.add(label)
    for label in labels:
        visit(label,[])
    fence=chr(96)*3
    out=[INTRO.strip()+'\n']
    sections=list(dict.fromkeys(x['section'] for x in S))
    for sec in sections:
        out.append('\n## '+sec+'\n')
        for x in S:
            if x['section']!=sec:
                continue
            out.append('\n### '+x['label']+' — '+x['title']+'\n')
            out.append('\n**Owner:** '+x['owner']+'. **Status:** '+x['status']+'.')
            out.append('\n**Proof source:** '+x['source']+'.')
            out.append('\n**Dependencies:** '+(', '.join(x['deps']) or 'definitions and finite elementary algebra only')+'.')
            out.append('\n**Interface:** '+('yes' if x['interface'] else 'internal')+'.\n')
            out.append('\n'+fence+'latex\n'+x['body']+'\n'+fence+'\n')
            if x['note']:
                out.append('\nWriting constraint / short proof sketch: '+x['note']+'\n')
    out.append('\n# Exhaustive baseline statement audit\n')
    out.append('\nEach labelled theorem-like environment in the baseline is covered below; the sole unlabelled §6 remark is handled separately. Removed assertions are replaced or omitted for the adopted package, not silently reverted to an earlier version.\n')
    out.append('\n| Baseline label | Disposition | Exact revised target / reason |\n|---|---|---|\n')
    found=[]
    pattern=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition|hypothesis|remark)\}(.*?)\\end\{\1\}',re.S)
    for file in sorted(Path('/home/ubuntu/aklt/manuscript-corrected').glob('*.tex')):
        for match in pattern.finditer(file.read_text()):
            labs=re.findall(r'\\label\{([^}]+)\}', match.group(2))
            if not labs:
                assert file.name=='sec6-walks.tex' and match.group(1)=='remark', (file.name,match.group(1))
                continue
            label=labs[0]
            assert label in BASEMAP, ('unmapped baseline',label)
            disposition,target=BASEMAP[label]
            found.append(label)
            out.append('| '+label+' | '+disposition+' | '+target+' |\n')
    assert set(found)==set(BASEMAP), ('unused mapping',set(BASEMAP)-set(found))
    out.append(EQUATIONS)
    out.append('\n# Risks and completion checks\n\nThe adopted-item risk register is [RISKS.md](RISKS.md). It assigns every architectural mismatch a resolution; no permission or scope choice is pending.\n')
    out.append('\nThis plan is accepted when the inventory and exported statements agree, all baseline environments have a disposition, all lane boundaries are explicit, the theorem graph is acyclic, and interfaces.tex compiles without unresolved references. Proof acceptance is a later milestone: each lane must meet its criteria, and the computational inputs must be proved, before t:main is published or formalized as unconditional.\n')
    (ROOT/'PLAN.md').write_text('\n'.join(out))
    # Interface order follows definition dependencies where practical;
    # theorem forward references are intentional and resolved by LaTeX.
    exports=[x for x in S if x['interface']]
    preamble=r"""\documentclass[11pt,reqno]{amsart}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,amsthm}
\usepackage[margin=1in]{geometry}
\usepackage[colorlinks=true,linkcolor=blue]{hyperref}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{hypothesis}[theorem]{Hypothesis}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\emergencystretch=3em
\title{REV-PLAN: exact shared interfaces for the AKLT gap revision}
\date{}
\begin{document}
\maketitle
\noindent These are mathematical statements for parallel proof writing.
No proof or certificate verification is asserted by this interface file.
All expectations and functionals below are finite sums.
The statements with hypotheses are internal implications; the target
main theorem is unconditional after the computational input theorems
are proved. Labels are shared with the complete inventory in PLAN.md.
"""
    tex=[preamble]
    last=None
    for x in exports:
        if x['section']!=last:
            tex.append('\n\\section{'+x['section'].split('. ',1)[1]+'}\n')
            last=x['section']
        tex.append('% Owner: '+x['owner']+'\n'+x['body']+'\n')
    tex.append('\n\\end{document}\n')
    (ROOT/'interfaces.tex').write_text('\n'.join(tex))
    (ROOT/'RISKS.md').write_text(RISKS.strip()+'\n')
    print(f'Wrote {len(S)} exact statements, {len(exports)} exports, and audited {len(found)} baseline labelled environments.')

if __name__=='__main__':
    write_files()
