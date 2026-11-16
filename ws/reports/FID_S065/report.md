STATUS: PASS
BLOCKING: 0

DECL: torusNeighbours PASS

The four entries in `AKLT/Defs/Quantum.lean:10–11` are exactly the displacements defining the paper's torus neighbours (`paper/sec1-result.tex:7–9,23–27`). Their distinctness, including at period three, is the calculation in `paper/sec3-quantum-frames.tex:147–152`, used in Proposition `p:toruskernel` at lines 191–201.

`Size` is the subtype of natural numbers at least three, and `Site L N` is `ZMod L.val × ZMod N.val` (`AKLT/Challenge/Main.lean:16–23`). Thus both subtraction expressions are subtraction in the modular rings, not truncated natural subtraction. Mathlib's `Data/ZMod/Defs.lean:137–180` supplies these modular types and operations; the local `size_neZero` instance excludes the infinite `ZMod 0` case and supplies finite instances. The `Finset` literal denotes a set, discarding repetitions (`Data/Finset/Insert.lean:365–407`), but no repetitions occur: equality of opposite neighbours would require the relevant period to divide two; a neighbour equal to the centre, or equality between horizontal and vertical neighbours, would require a period to divide one. The size bounds exclude all these cases. These are also exactly the other endpoints of the incident bonds defined by `nextSite` and `bondSites`; there are no diagonal neighbours, loops, parity assumptions, or missing wraparound neighbours. This is the required object both for `TorusKernelStatement` and for the exterior-neighbour condition in `PlaneEnergyStatement`.

DECL: polynomialState PASS

This auxiliary conversion implements Definition `d:poly`, which makes the monomials `m_j = z₁^(4-j) z₂^j` orthogonal with squared norm `1 / choose(4,j)` (`paper/sec3-quantum-frames.tex:14–18`), and its tensor-product realization at lines 74–76. Accordingly `e_j = sqrt(choose(4,j)) m_j` is orthonormal. If an ordinary monomial has coefficient `a_σ`, its orthonormal tensor coordinate must be `a_σ / ∏ₓ sqrt(choose(4,σₓ))`, exactly the definition at `AKLT/Defs/Quantum.lean:14–16`.

The coefficient is an ordinary polynomial coefficient, without factorial or binomial normalization: Mathlib defines `MvPolynomial` as an additive monoid algebra on finitely supported exponent vectors (`Algebra/MvPolynomial/Basic.lean:80–94`), with ordinary coefficient extraction (`:582–584`). `monomialDegree` uses `Finsupp.equivFunOnFinite.symm`, which preserves each exponent value (`Data/Finsupp/Defs.lean:204–216`). Its exponents are precisely `(4-σₓ, σₓ)` because the variable index is `Fin 2` (`AKLT/Challenge/Main.lean:117–121`). Since `σₓ : Fin 5`, its natural value is at most four: the natural subtraction never truncates an intended negative exponent, and every degree-four binary monomial is represented exactly once.

`Nat.choose` is the ordinary binomial coefficient (`Data/Nat/Choose/Basic.lean:50–53`). The five possible values are `1,4,6,4,1`; its positivity also follows from `choose_pos` at line 117. Each is cast to the reals before taking the nonnegative real square root, then embedded in the complexes. Mathlib's `Real.sqrt_pos` (`Analysis/Real/Sqrt.lean:286–289`) therefore makes every divisor factor strictly positive before embedding and nonzero afterwards. The product is finite and nonzero. Division is complex division, with no division-by-zero case or unintended integer division. `WithLp.toLp 2` only packages the coordinate function (`Analysis/Normed/Lp/WithLp.lean:47–54,97–98`); it does not normalize the vector. The resulting `Hilbert` uses the sum inner product (`Analysis/InnerProductSpace/PiL2.lean:84–115`), so the conversion has exactly the paper's tensor norm.

The only caller is `reorientedB`, whose input is homogeneous of degree four at every site, so no physical coefficients are discarded. On `vbsPolynomial`, this conversion agrees definitionally with the frozen `B` (`AKLT/Challenge/Main.lean:123–129`), and it is inverse to the coordinate conversion used in `physicalEval` (`AKLT/Defs/Polynomial.lean:31–37`) on physical polynomials.

DECL: reorientedB PASS

The paper fixes an arbitrary orientation of each unoriented edge and defines the unnormalized product of determinants (`paper/sec1-result.tex:13–28`). Reversing one orientation negates its determinant (`paper/sec3-quantum-frames.tex:125–126`); reversing any collection multiplies the product by `(-1)^k` and preserves its span (`:191–195,218–220`).

At `AKLT/Defs/Quantum.lean:19–20`, `ε e = true` retains `singlet e`, and `ε e = false` negates it. Thus every edge orientation assignment is represented independently. The Boolean test has no extra hypothesis or quantifier restriction. `singlet` is exactly `z_(x,1) z_(y,2) - z_(x,2) z_(y,1)` with zero-based variable indices (`AKLT/Challenge/Main.lean:105–110`); commutativity of the polynomial ring makes its negative exactly the reversed determinant.

The product is over the finite type `Bond = Site × Fin 2`, using each positive-coordinate bond once. For periods at least three, this indexes the paper's unordered edge set bijectively, including the three-cycle in a coordinate of period three. Every site has four incident factors, hence the product has the required degree four at each site and lies in the domain where `polynomialState` is the physical coordinate identification. If `k` counts the edges with `ε e = false`, the resulting vector is exactly `(-1)^k • B L N`, with no additional normalization or phase. Each edge determinant is nonzero and their product is nonzero in the complex polynomial integral domain; the nonzero coordinate divisors preserve this fact. Consequently the span equality in `TorusKernelStatement` cannot hold merely because this definition accidentally produced zero.

DECL: StarHilbert PASS

Lemma `l:star` uses `V₄` at five sites labelled centre `0` and leaves `1,2,3,4` (`paper/sec3-quantum-frames.tex:223–236`). Definition `d:poly` fixes the five-dimensional factor and its monomial normalization (`:14–18`).

`EuclideanSpace ℂ (Fin 5 → Fin 5)` at `AKLT/Defs/Quantum.lean:23` is the complex coordinate space indexed by all five-site assignments of five local basis labels. Mathlib defines `EuclideanSpace` as `PiLp 2`, with inner product the sum of the coordinate inner products, not the supremum norm on an ordinary function space (`Analysis/InnerProductSpace/PiL2.lean:84–115,148–154`). In particular its inner product is `∑σ conj(u_σ) v_σ`, as required by the convention in `paper/sec1-result.tex:111–113`. The indexing type is finite and has `5^5 = 3125` elements (`Data/Fintype/Pi.lean:134–136`; `Data/Fintype/BigOperators.lean:133–140`). These coordinates identify it isometrically with `V₄` tensor-powered five times in the orthonormal basis checked above. There is no restriction to symmetric site configurations, no missing tensor factors, and no empty or singleton indexing case. This is the correct space for its consumers `starAtSite`, `starCasimir`, and `starHamiltonian`.

DECL: starAtSite PASS

This auxiliary definition supplies the one-factor operators needed for the central/leaf projections of `h_★ = ∑ⱼ₌₁⁴ P_{\{0,j\}}` in Lemma `l:star` (`paper/sec3-quantum-frames.tex:223–247`); the intended bond projection is specified in `paper/sec1-result.tex:10–12`.

Mathlib's `Matrix.toEuclideanLin` is `Matrix.toLpLin 2 2` (`Analysis/InnerProductSpace/PiL2.lean:1239–1247`). Its action is ordinary matrix multiplication by a column vector (`Analysis/Normed/Lp/Matrix.lean:30–45`), with no transpose or complex conjugation. Therefore `AKLT/Defs/Quantum.lean:26–27` gives, for any output configuration `σ`,

`(starAtSite A x ψ)(σ) = ∑ k : Fin 5, A (σ x) k * ψ (Function.update σ x k)`.

Indeed, the condition requires equality of input and output labels at every site other than `x`, while leaving their labels at `x` unrestricted. There is exactly one such input configuration for each `k`. This is precisely `A` on factor `x` tensored with identities on the other four factors; it introduces neither a dimension multiplier nor a diagonal restriction on `A`. `Module.End ℂ StarHilbert` means a complex-linear endomorphism, and finite dimension supplies continuity without imposing additional hypotheses on `A`.

The consumer `starCasimir` uses centre `0` and leaf `j.val+1` for `j : Fin 4`, giving exactly four distinct leaves in `Fin 5`, with no wraparound (`AKLT/Defs/Quantum.lean:30–35`). Its matrices are the frozen `spinZ`, `spinPlus`, and `spinMinus` (`AKLT/Challenge/Main.lean:49–59`): diagonal entries `2-k`, raising entries `sqrt(k(5-k))`, and the conjugate-transpose lowering matrix. Their indices run from zero to four, so the natural subtraction in `5-k` is within its intended range and the raising boundary is correctly zero. Lifting these matrices by the checked formula gives the same bond Casimir used for the torus projectors, hence the central/leaf total-spin-four projections in `starHamiltonian`. Edges between leaves on small tori add no terms, in agreement with the paper's explicit observation at lines 245–249.

Non-blocking remarks:

- `polynomialState` is defined on the entire polynomial ring. On a polynomial with other multidegrees it extracts only the component of degree four at every site; it is not injective on that larger domain. This is harmless for its actual use, where every input has the required multidegree. No assertion of injectivity on arbitrary polynomials is made.
- The Boolean convention is “true retains, false reverses.” The paper does not prescribe a Boolean encoding, and the consumer quantifies over every Boolean assignment, so this convention loses no orientation choices.
- Read the complete assigned file and its recursive local imports: `FrameModel`, `Polynomial`, `Probability`, `Frame`, `Moment`, `Geometry`, and `Challenge/Main`. Also inspected the consumers in `Blueprint/Top/Quantum.lean`. Judgments above concern only the five assigned declarations.
- Supplemental Python sanity checks verified the neighbour/incident-bond correspondence and absence of repeated bonds at every site for all 36 period pairs with both periods in `3..8`, including modular boundaries. They also checked the five binomial values, the 3125 star coordinates, and the off-site equality condition. The general conclusions above follow from the definitions and stated size bounds; these finite checks are supporting evidence. No Lean process was launched, and inputs were not modified.

Source paths: `paper/` denotes `/home/ubuntu/aklt/review/FID_S/paper/`; `AKLT/` denotes `/home/ubuntu/aklt/review/FID_S/lean/AKLT/`; Mathlib paths are relative to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`.
