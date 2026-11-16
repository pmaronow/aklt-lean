STATUS: PASS
BLOCKING: 0

DECL: V PASS

Lean `Main.lean:41–45` gives an exact orthonormal coordinate realization of the manuscript's spin space (`sec1-intro-statement.tex:5`; `sec2-frames-Q.tex:11–15`, equation (e:Vinner)). For the monomials $m_k=z_1^{4-k}z_2^k$, that integral gives

$$
\langle m_j,m_k\rangle_V=\delta_{jk}\frac{1}{\binom4k}.
$$

Indeed, phase rotation makes different monomials orthogonal, and $t=|\zeta_1|^2=(1+a_3)/2$ is uniform on $[0,1]$, so the diagonal entry is $5\int_0^1t^{4-k}(1-t)^k\,dt=1/\binom4k$. Thus $e_k=\sqrt{\binom4k}\,m_k$, for $k=0,\ldots,4$, is orthonormal. The coordinate-to-polynomial map $v\mapsto\sum_k v_k e_k$ is a unitary identification with precisely the manuscript's inner product and its polynomial spin-2 representation.

Mathlib checked: `Mathlib/Analysis/InnerProductSpace/PiL2.lean:84–115` defines `EuclideanSpace ℂ (Fin 5)` as `PiLp 2` on the five-element index type, with inner product equal to the sum of coordinate inner products. `Mathlib/Analysis/InnerProductSpace/Basic.lean:914–927` gives the scalar inner product as $\overline{x}y$. `PiL2.lean:202–209` gives dimension five. There is no averaging factor or unweighted-monomial interpretation.

DECL: spinZ PASS

Lean `Main.lean:49–50` is the diagonal matrix $\operatorname{diag}(2,1,0,-1,-2)$. In the preceding polynomial coordinates it represents $J_z=(z_1\partial_{z_1}-z_2\partial_{z_2})/2$, which acts on $e_k$ by $2-k$. This supplies a spin-2 component for the irreducible representation in `sec1-intro-statement.tex:5` and `sec2-frames-Q.tex:15`; the manuscript does not separately prescribe matrices for its components. The pullback-action convention is addressed below.

Both operands of `2 - (i.val : ℂ)` are complex numbers: this is genuine subtraction, including the negative entries for $i=3,4$. It is not natural-number truncated subtraction. Mathlib checked: matrices have row and column coordinates (`Mathlib/Data/Matrix/Basic.lean:23`), and `Mathlib/Data/Matrix/Mul.lean:692–708` makes their action the usual column-vector action, with output row $i$ equal to $\sum_j A_{ij}v_j$. Hence the displayed entries have the stated eigenvalues and orientation.

DECL: spinPlus PASS

Lean `Main.lean:54–56` has its only nonzero entries in positions $(k-1,k)$, $k=1,\ldots,4$, with values $2,\sqrt6,\sqrt6,2$. Accordingly $J_+e_k=\sqrt{k(5-k)}e_{k-1}$, and $J_+e_0=0$. In the polynomial realization of `sec2-frames-Q.tex:11–15`, this is $z_1\partial_{z_2}$: applying that derivative to the normalized monomials gives exactly these coefficients.

The condition `i.val + 1 = j.val` uses natural-number values, so it does not wrap at the boundary of `Fin 5`. The subtraction `5 - j.val` is natural-number subtraction, but $0\le j.val\le4$, so it equals ordinary subtraction throughout this domain. The product is formed in $\mathbb N$, cast to $\mathbb R$, square-rooted there, then embedded in $\mathbb C$. Mathlib checked: `Mathlib/Analysis/Real/Sqrt.lean:109–113,144–150,178` defines the nonnegative real square root and its square on nonnegative inputs. No negative input or complex square-root choice occurs. The column convention is `Mathlib/Data/Matrix/Mul.lean:692–708`, as above.

DECL: spinMinus PASS

Lean `Main.lean:59` is exactly the adjoint of `spinPlus` in these orthonormal coordinates. Thus $J_-e_k=\sqrt{(k+1)(4-k)}e_{k+1}$ for $k<4$, and $J_-e_4=0$. This is $z_2\partial_{z_1}$ in the degree-four polynomial space of `sec2-frames-Q.tex:11–15`, with the same inner product.

Mathlib checked: `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:35–37,128–135` defines conjugate transpose by swapping the indices and applying `star`. `Mathlib/Analysis/InnerProductSpace/Adjoint.lean:1059–1063` explicitly identifies this operation, through `toEuclideanLin`, with the adjoint for Euclidean inner products. Since all the raising coefficients are real, the entries here are their transpose, with the required lowering direction. Exact computation also verified $[J_z,J_\pm]=\pm J_\pm$, $[J_+,J_-]=2J_z$, and $J_z^2+(J_+J_-+J_-J_+)/2=6I$.

DECL: Configuration PASS

Lean `Main.lean:61–62` uses all functions from sites to `Fin 5` as labels of tensor-product basis vectors. Under the identification for `V`, a label $\sigma$ denotes $\bigotimes_x e_{\sigma(x)}$. This is exactly a basis index set for the tensor product in `sec1-intro-statement.tex:5` and the polynomials of degree four separately at every site in `sec2-frames-Q.tex:15`. It imposes no restriction to symmetric states, fixed magnetization, or classical frame configurations.

The site dependency is sound: `Main.lean:17–23` restricts both side lengths to natural numbers at least three. Mathlib checked: `Mathlib/Data/ZMod/Defs.lean:137–166` defines `ZMod 0` as $\mathbb Z$, but positive `ZMod n` as the finite residue type with exactly $n$ elements. The lower bound excludes the infinite zero-modulus case. `Mathlib/Data/ZMod/Basic.lean:651–654` confirms addition modulo the modulus. Consequently there are exactly $LN$ sites and $5^{LN}$ configurations, matching the manuscript's full domain $L,N\ge3$.

DECL: Hilbert PASS

Lean `Main.lean:64–66` is the full complex Hilbert space with one orthonormal coordinate for each configuration. The map

$$
f\longmapsto \sum_\sigma f(\sigma)\prod_x e_{\sigma(x)}(z_x)
$$

is a unitary identification with $\mathcal H_\Lambda=\bigotimes_x V$ in `sec1-intro-statement.tex:5` and with the product inner product specified in `sec2-frames-Q.tex:15`. Its dimension is $5^{LN}$, and its inner product is $\sum_\sigma\overline{f(\sigma)}g(\sigma)$, with no normalization by the number of configurations.

Mathlib checked: `Mathlib/Analysis/InnerProductSpace/PiL2.lean:84–115,202–205` defines this sum inner product and identifies the dimension with the cardinality of the index type. In particular, the second argument of `EuclideanSpace` is an index type, and here it is correctly the whole tensor-product basis index type. Finite-dimensionality follows also from `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean:95–100` and the transfer through `WithLp` in `Mathlib/Analysis/Normed/Lp/WithLp.lean:235–254`.

DECL: atSite PASS

Lean `Main.lean:70–73` is exactly $A$ on site $x$, tensored with identities at the other sites. Its matrix coefficient is

$$
A_{\sigma(x),\tau(x)}\prod_{y\ne x}\delta_{\sigma(y),\tau(y)}.
$$

Equivalently, on a vector $f$, its $\sigma$-coordinate is $\sum_{k=0}^4 A_{\sigma(x),k}f(\sigma[x:=k])$. Thus each spectator configuration is preserved, and no multiplicity factor appears. This is the single-site embedding required by the tensor-product model and identity extension in `sec1-intro-statement.tex:5` and `sec2-frames-Q.tex:15`.

Mathlib checked: `Mathlib/Analysis/InnerProductSpace/PiL2.lean:1241–1248` defines `Matrix.toEuclideanLin` as `toLpLin 2 2`, agreeing with the orthonormal coordinate bases. `Mathlib/Analysis/Normed/Lp/Matrix.lean:29–45` shows that its action is precisely matrix multiplication on coordinates; `Mathlib/Data/Matrix/Mul.lean:698–708` gives the sum over input columns. It does not transpose or conjugate the supplied matrix. `Module.End` is a linear endomorphism by `Mathlib/Algebra/Module/LinearMap/End.lean:30–33`.

DECL: onBond PASS

Lean `Main.lean:76–78` is $A_x+A_y$, where $y=\mathrm{nextSite}(x,d)$. For each of the three spin components used below, this is the corresponding component of total spin on the two endpoints. That is the total-spin convention underlying the projection in `sec1-intro-statement.tex:5` and the diagonal SU(2) decomposition in `sec2-frames-Q.tex:32`.

The endpoints are distinct: a positive coordinate step cannot be zero modulo a side length at least three. The other site coordinates remain unchanged under each summand, by the checked meaning of `atSite` and `toEuclideanLin` (`Mathlib/Analysis/Normed/Lp/Matrix.lean:29–45`). Addition of the linear endomorphisms adds their actions, so this realizes total spin, including its cross terms when squared. The modular-step convention is checked in `Mathlib/Data/ZMod/Basic.lean:640–654`.

DECL: bondCasimir PASS

Lean `Main.lean:83–87` is the quadratic Casimir of total spin on precisely the two endpoints:

$$
C_{xy}=(J_{z,x}+J_{z,y})^2+
\tfrac12\bigl((J_{+,x}+J_{+,y})(J_{-,x}+J_{-,y})+
(J_{-,x}+J_{-,y})(J_{+,x}+J_{+,y})\bigr).
$$

Writing $J_1=(J_++J_-)/2$ and $J_2=(J_+-J_-)/(2i)$, this equals $(\mathbf J_x+\mathbf J_y)^2$, where the bold symbols refer to the endpoint spin vectors $(J_1,J_2,J_z)$. It therefore measures the total-spin summands in `sec1-intro-statement.tex:5` and `sec2-frames-Q.tex:32`. The one-site Casimir is $2(2+1)I=6I$, so the normalization is the intended spin normalization.

Mathlib checked: `Mathlib/Algebra/Module/LinearMap/End.lean:47–59` makes `*` composition, with $(fg)(v)=f(g(v))$. Thus the products are operator products. The scalar `(1 / 2 : ℂ)` is complex division and scalar multiplication, giving exactly one half. `Mathlib/Analysis/Normed/Lp/Matrix.lean:54–64` confirms compatibility of matrix multiplication and composition. All spectator factors are identities because each component has that property. An exact two-site calculation gave eigenvalues $0,2,6,12,20$ with eigenspace dimensions $1,3,5,7,9$, respectively, agreeing with spins $0,1,2,3,4$.

DECL: spin4Space PASS

Lean `Main.lean:91–92` is exactly $\ker(C_{xy}-20I)$ in the full Hilbert space. Mathlib checked: `Mathlib/LinearAlgebra/Eigenspace/Basic.lean:422–429,468–469` defines `Module.End.eigenspace f μ` as the ordinary eigenspace, with membership exactly $f(v)=\mu v$. Here `20` is a complex scalar, not an index or a generalized-eigenspace exponent.

The intended local subspace is the spin-4 summand of `sec1-intro-statement.tex:5`; the decomposition into spins $0,\ldots,4$, once each, is explicitly stated in `sec2-frames-Q.tex:32`. Their Casimir eigenvalues $s(s+1)$ are $0,2,6,12,20$, all distinct. Therefore selecting 20 selects precisely spin 4, of dimension nine. There is no empty-eigenspace degeneration.

More explicitly, fix every spectator basis label and vary only the two endpoint labels. Each resulting 25-dimensional coordinate block carries the same local Casimir, and the blocks are orthogonal. Hence the full eigenspace is the local spin-4 space tensored with the entire spectator space, of dimension $9\cdot5^{LN-2}$. It does not constrain the total spin of the whole torus or restrict spectator states. This block description works for every permitted size, since $LN\ge9$.

DECL: P PASS

Lean `Main.lean:96–97` is exactly the orthogonal projection required in `sec1-intro-statement.tex:5`: projection onto the bond's local spin-4 subspace, extended by the identity on every spectator factor.

Mathlib checked: `Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:120–133` defines `starProjection` as the orthogonal projection onto the submodule followed by its inclusion in the full ambient space. Its characterization is explicit at `:156–186`: its value lies in the submodule and the residual is orthogonal to that submodule, uniquely. Thus it projects onto `spin4Space`, rather than its orthogonal complement. `.toLinearMap` retains this same map while forgetting continuity. Projection exists here because the subspace is finite-dimensional and hence complete (`Mathlib/Topology/Algebra/Module/FiniteDimension.lean:509–520`), and complete subspaces have orthogonal projections (`Projection/Basic.lean:47–60`). There is no extra assumption selecting only some sizes or bonds.

The orthogonal block decomposition established for `spin4Space` shows that this ambient projection is $P^{(4)}_{xy}\otimes I_{\mathrm{spectators}}$. In particular, spectator factors carry identity operators, not additional projections. On the two-site factor, an independent exact description is

$$
P^{(4)}_{xy}=\frac{C_{xy}(C_{xy}-2I)(C_{xy}-6I)(C_{xy}-12I)}{40320},
\qquad 40320=20\cdot18\cdot14\cdot8.
$$

Exact rational computation verified that this operator is orthogonal, idempotent, and rank nine, and that its kernel is precisely the 16-dimensional image of multiplication by $q_{xy}$ from bidegree $(3,3)$. This also agrees with the manuscript's independent characterization in `sec2-frames-Q.tex:27–32` (the edge lemma). Exchanging the endpoints leaves the total components, Casimir, eigenspace, and projection unchanged, so the orientation chosen to enumerate bonds does not alter $P_e$.

DECL: H PASS

Lean `Main.lean:100` is exactly $H_{L,N}=\sum_{e\in E}P_e$, with coefficient one for each unoriented nearest-neighbour bond, as in `sec1-intro-statement.tex:5–8`, equation (e:H).

Mathlib checked: `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:28–30,61–68` identifies a sum over a finite type with `Finset.sum` over `Finset.univ`. Here that type is `Site L N × Fin 2` (`Main.lean:23–34`), so there are $2LN$ terms. Each site contributes the positive horizontal and positive vertical edge, using modular addition (`Mathlib/Data/ZMod/Defs.lean:137–166`; `Mathlib/Data/ZMod/Basic.lean:651–654`).

This is a bijective indexing of the manuscript's unordered bonds for every $L,N\ge3$. There are no loops, since one is nonzero modulo either side length. If two bonds in the same direction represented the same unordered pair with reversed endpoints, two steps in that direction would be zero modulo the side length, impossible when that length is at least three. Horizontal and vertical edges cannot coincide because two distinct horizontal endpoints have the same second coordinate, whereas two distinct vertical endpoints have the same first coordinate. Every nearest-neighbour edge is represented in one of the positive directions. This includes side length three: opposite directed steps are different neighbours, and the three edges around a coordinate cycle are each counted once. Consequently no factor of two or omitted wraparound edge appears.

The declarations define the model on all side lengths at least three, including odd lengths, as does `sec1-intro-statement.tex:5`. The later evenness restriction belongs to the theorem (`sec1-intro-statement.tex:12`) and the checkerboard frame argument (`sec2-frames-Q.tex:71`), not to the Hamiltonian's definition.

Non-blocking remarks.

1. The component labels involve a harmless choice of spin axes. For the manuscript's pullback action $U_g f(z)=f(g^{-1}z)$ (`sec2-frames-Q.tex:15`), take $g_a(t)=\exp(-it\sigma_a/2)$ and define $U_{g_a(t)}=\exp(-itS_a)$. With the usual Pauli matrices, differentiating gives $S_x=-J_x,\ S_y=J_y,\ S_z=-J_z$ for the polynomial operators used above, where $J_x=(J_++J_-)/2$ and $J_y=(J_+-J_-)/(2i)$. This is a common rotation of the spin axes, and its diagonal two-site Casimir is exactly the one defined in Lean. Thus the inverse in the manuscript's action introduces no mismatch in its spin-4 subspace or Hamiltonian. The manuscript does not specify component matrices that would make the particular magnetic-label choice an additional requirement.

2. The calculations used Python 3 with exact `fractions.Fraction` arithmetic, without numerical tolerances. The positive diagonal basis change $T_{kk}=\sqrt{\binom4k}$ takes the displayed orthonormal matrices to monomial-coordinate matrices $J_+m_k=k m_{k-1}$, $J_-m_k=(4-k)m_{k+1}$. This allows all 25-dimensional calculations to be rational. Orthogonality was checked against the exact monomial Gram matrix $G_{(i,j),(i,j)}=1/(\binom4i\binom4j)$. The calculated eigenspace dimensions sum to 25; the projector satisfied $P^2=P$, $P^TG=GP$, $(C-20I)P=0$, and rank nine. Multiplication by $q_{xy}$ had rank 16 and was annihilated by $P$. Bond enumeration also passed for sizes $(3,3),(3,4),(4,3),(4,4),(5,6)$; the argument in the `H` entry establishes the result for all permitted sizes. No Lean processes were used.

3. The whole Lean file (`Main.lean:1–142`) and both manuscript sections were read. For the context beyond this declaration group, the meanings of the following Mathlib operations were also checked: `Finsupp.equivFunOnFinite` preserves the pointwise values when passing between functions and finitely supported functions (`Mathlib/Data/Finsupp/Defs.lean:204–216`); `MvPolynomial` is the additive monoid algebra on natural exponent vectors, and `.coeff` extracts the ordinary monomial coefficient (`Mathlib/Algebra/MvPolynomial/Basic.lean:80–94,581–584`; `Mathlib/Algebra/MonoidAlgebra/Defs.lean:60–69`); `WithLp.toLp` is the inverse of the coordinate linear equivalence, with no coordinate rescaling (`Mathlib/Analysis/Normed/Lp/WithLp.lean:235–245`); and `HasEigenvalue` requires a nonzero eigenspace (`Mathlib/LinearAlgebra/Eigenspace/Basic.lean:435–448,481–483`). These checks support the coordinate interpretation used in this review. The twelve verdicts above are the assigned scope.
