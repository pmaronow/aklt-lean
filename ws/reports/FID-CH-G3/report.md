STATUS: PASS
BLOCKING: 0

DECL: SpinorPolynomial PASS

[Main.lean:103](/home/ubuntu/aklt/review/FID-CH/Main.lean:103) defines the ambient complex polynomial ring with two independent commuting variables per site. This matches the polynomial representation in [sec2-frames-Q.tex:11](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:11), its many-site version at line 15, and the ring explicitly used at line 25. The ambient ring need not itself impose degree four: `vbsPolynomial` has that multidegree, and `B` changes its coordinates into `Hilbert`.

Mathlib meaning checked: [Mathlib/Algebra/MvPolynomial/Basic.lean:82](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean:82) defines `MvPolynomial σ R` as `AddMonoidAlgebra R (σ →₀ ℕ)`. Thus exponents are finitely supported natural-valued functions on the variable labels, with ordinary polynomial multiplication, not an exterior algebra or a ring modulo relations. [Mathlib/Algebra/MonoidAlgebra/Defs.lean:64](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/MonoidAlgebra/Defs.lean:64) stores ordinary coefficients in `coeff : M →₀ R`.

The site domain also matches [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5): `Size` requires each side to be at least three. [Mathlib/Data/ZMod/Defs.lean:139](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Data/ZMod/Defs.lean:139) defines `ZMod 0 = ℤ` and `ZMod (n+1) = Fin (n+1)`; the zero-modulus branch is excluded here. Its finite instance is at line 155, and its addition uses modular `Fin` addition at line 173. Hence this is precisely the finite torus, with two variables at each of its `L*N` sites.

DECL: singlet PASS

[Main.lean:107](/home/ubuntu/aklt/review/FID-CH/Main.lean:107) is exactly `z_(x,1) z_(y,2) - z_(x,2) z_(y,1)` from [sec2-frames-Q.tex:17](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:17), with manuscript indices 1,2 represented by `Fin 2` indices 0,1. Mathlib's `MvPolynomial.X`, [Mathlib/Algebra/MvPolynomial/Basic.lean:126](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean:126), is the coefficient-one monomial whose exponent vector is `Finsupp.single n 1`. Multiplication adds exponents (line 101), and subtraction here is subtraction in the complex polynomial ring. There is no complex conjugation, identification of variables, or extra normalization such as `1/√2`.

`nextSite` chooses the positive horizontal or vertical endpoint, including periodic wraparound. Because both sides are at least three, its endpoint differs from its initial site, so the two terms are distinct monomials and the factor is nonzero. Reversing an edge replaces this factor by its negative. The manuscript explicitly permits any fixed edge orientation at [sec2-frames-Q.tex:21](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:21); this choice is therefore faithful.

DECL: vbsPolynomial PASS

[Main.lean:114](/home/ubuntu/aklt/review/FID-CH/Main.lean:114) matches the unnormalized product in (e:B), [sec2-frames-Q.tex:23](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:23). Mathlib's finite-type product notation means a product over `Finset.univ`, as documented in [Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:184](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:184). Thus every element of `Bond = Site × Fin 2` contributes once.

These labels enumerate precisely the unoriented nearest-neighbour bonds once. There are no loops. Two labels in one direction could give the same unordered edge with opposite orientations only if that side length divided two, excluded by `Size`; a horizontal and a vertical edge cannot coincide. This remains true when a side equals three: its three positively oriented edges enumerate the triangle's three distinct unordered edges. Each site belongs to the two outgoing and two incoming edges, all distinct. Consequently every product term has degree four at every site, exactly as asserted at [sec2-frames-Q.tex:25](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:25).

Each singlet is nonzero and this complex polynomial ring is an integral domain; Mathlib supplies `NoZeroDivisors` and `IsDomain` at [Mathlib/Algebra/MvPolynomial/Basic.lean:196](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean:196) and line 203. Therefore the product is nonzero. An alternative manuscript orientation changes the complete product only by a global sign, a permitted nonzero scalar.

DECL: monomialDegree PASS

[Main.lean:118](/home/ubuntu/aklt/review/FID-CH/Main.lean:118) indexes the ordinary monomial `∏_x z_(x,1)^(4-k_x) z_(x,2)^k_x`, where `k_x = (σ x).val`. These are exactly the monomials spanning the separately degree-four polynomial Hilbert space of [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15).

Mathlib meaning checked: [Mathlib/Data/Finsupp/Defs.lean:207](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Data/Finsupp/Defs.lean:207) defines `equivFunOnFinite` with forward map the underlying function and inverse the same function equipped with its finite support. Line 216 confirms that coercing the inverse back to a function gives the original function definitionally. Its inverse neither permutes the variables nor changes their values.

Since `σ x : Fin 5`, `0 ≤ k_x ≤ 4`. Although `4 - k_x` is truncated natural subtraction, no truncation changes the intended exponent. The two exponents sum to four. Conversely, every pair of natural exponents summing to four has this form for exactly one `k_x : Fin 5`; the coefficient extraction therefore covers every possible monomial of `vbsPolynomial`. The branch `p.2 ≠ 0` denotes exactly variable 1, since `p.2 : Fin 2`.

DECL: B PASS

[Main.lean:126](/home/ubuntu/aklt/review/FID-CH/Main.lean:126) gives exactly the coordinates of (e:B) in the orthonormal tensor basis specified by `V` and `Hilbert`, for the chosen edge orientations. In particular, the division by square-root binomial factors is correct.

To check this against the manuscript rather than relying on the Lean comments, write `m_k = z_1^(4-k) z_2^k`. From (e:zeta) and (e:Vinner), [sec2-frames-Q.tex:9](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:9) and line 13, `t = |ζ_1|² = (1+a_3)/2` is uniform on `[0,1]`. Axial rotation invariance makes distinct `m_k` orthogonal, and

```text
||m_k||² = 5 ∫₀¹ t^(4-k) (1-t)^k dt
          = 5 (4-k)! k! / 5!
          = 1 / choose(4,k).
```

Thus `e_k = √choose(4,k) m_k` is orthonormal. If `a_σ` is the ordinary coefficient of `∏_x m_(σ x)` in the product polynomial, its coordinate in `⊗_x e_(σ x)` is `a_σ / ∏_x √choose(4,σ x)`, precisely the Lean formula. Mathlib's coefficient is the stored ordinary monomial coefficient, not a derivative or a divided-power coefficient; see `AddMonoidAlgebra.coeff` cited above and [Mathlib/Algebra/MvPolynomial/Basic.lean:582](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Basic.lean:582), where the coefficient of `monomial n a` at `m` is `a` when `n = m` and zero otherwise.

The denominator cannot vanish: [Mathlib/Data/Nat/Choose/Basic.lean:50](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Data/Nat/Choose/Basic.lean:50) defines the usual binomial coefficients, and `choose_pos` at line 117 applies because `k ≤ 4`. [Mathlib/Analysis/Real/Sqrt.lean:112](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/Real/Sqrt.lean:112) is the nonnegative real square root (zero on negative inputs); `sqrt_pos` at line 286 makes each factor strictly positive. The natural-to-real cast is taken before the square root. The subsequent real-to-complex cast is the injective inclusion `r ↦ (r,0)`, [Mathlib/Basic/Complex/Basic.lean:83](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Basic/Complex/Basic.lean:83), with injectivity at line 103 and compatible natural casts at lines 340–346. Complex division here consequently preserves all nonzero coefficients.

Mathlib's `EuclideanSpace ℂ ι` is `PiLp 2 (fun _ : ι => ℂ)`, [Mathlib/Analysis/InnerProductSpace/PiL2.lean:114](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:114), with the sum inner product at lines 84–105. Its inner product is conjugate-linear in the first argument and linear in the second, agreeing with (e:Vinner); see [Mathlib/Analysis/InnerProductSpace/Defs.lean:53](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Defs.lean:53). `WithLp.toLp` merely wraps the given coordinate function, [Mathlib/Analysis/Normed/Lp/WithLp.lean:50](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean:50); [Mathlib/Analysis/Normed/Lp/PiLp.lean:141](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:141) confirms that evaluation returns the unchanged coordinate. There is no hidden normalization or conjugation. Since `vbsPolynomial` is nonzero and all its supported monomials are indexed by `monomialDegree`, `B` is nonzero as well.

Compatibility with the spin model used by `P` was also checked. In the basis `e_k`, the polynomial operators

```text
J_z = (z_1 ∂_1 - z_2 ∂_2)/2,
J_+ = z_1 ∂_2,
J_- = z_2 ∂_1
```

have exactly the matrices `spinZ`, `spinPlus`, and `spinMinus`: `J_z e_k = (2-k)e_k` and `J_+ e_k = √(k(5-k)) e_(k-1)`. The subtraction in `spinZ` occurs in ℂ, so negative magnetic labels remain negative; the natural subtraction `5-k` in `spinPlus` is harmless for `k ≤ 4`. Mathlib's conjugate transpose is transpose followed by entrywise conjugation, [Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:36](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:36).

The manuscript uses the inverse-substitution action `f(z) ↦ f(g⁻¹z)` at sec2-frames-Q.tex:15. With the group convention `g_a(t) = exp(-it σ_a/2)` and `U_(g_a(t)) = exp(-it K_a)`, its generators in these same polynomial coordinates satisfy `K_z = -J_z`, `K_+ = -J_-`, `K_- = -J_+`. Their quadratic Casimir is exactly the same `J_z² + (J_+J_- + J_-J_+)/2`, also on two sites. Thus the generator convention does not alter the total-spin-4 subspace or require any change of coordinates in `B`.

There is no matrix transpose hidden in `atSite`: `Matrix.toEuclideanLin` is `toLpLin 2 2`, [Mathlib/Analysis/InnerProductSpace/PiL2.lean:1242](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:1242), and [Mathlib/Analysis/Normed/Lp/Matrix.lean:44](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/Matrix.lean:44) identifies its action with ordinary matrix times column vector. `Module.End` multiplication composes maps, [Mathlib/Algebra/Module/LinearMap/End.lean:49](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Algebra/Module/LinearMap/End.lean:49). `eigenspace C 20` means precisely the vectors satisfying `C v = 20 • v`, [Mathlib/LinearAlgebra/Eigenspace/Basic.lean:424](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean:424) and line 468. `starProjection` is the orthogonal projection back into the ambient space, [Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:132](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:132), not a complementary projection. Consequently the coordinate map above identifies the manuscript's projector in sec1-intro-statement.tex:5 with `P`, and its edge-kernel characterization at sec2-frames-Q.tex:28 applies to this `B`.

Non-blocking remarks:

- Domain and parity: all five definitions are appropriately available for every `L,N ≥ 3`. The VBS definition precedes the restriction to even sides, which begins only at sec2-frames-Q.tex:71. Even members of `Size` have sides at least four. The threshold and parity restrictions of `MainStatement` do not change the meaning of these definitions. No claim about declarations outside the assigned group is being graded here.
- The staggered change of variables at sec2-frames-Q.tex:125 transforms the classical measure into the rotated frame convention. It does not redefine (e:B), so no staggered transformation is missing from the Lean vector.
- Verification: exact rational Python calculations in the unnormalized two-site monomial basis gave Casimir eigenvalues `0,2,6,12,20` with eigenspace dimensions `1,3,5,7,9`. Multiplication by `q_xy` from bidegree `(3,3)` had rank 16 and was annihilated exactly by `C(C-2)(C-6)(C-12)/(20·18·14·8)`, the spin-4 orthogonal projector for the manuscript's monomial Gram matrix. This confirms the local normalization and projector compatibility independently of the comments. Small tori `3×3`, `3×4`, `4×3`, `4×4`, and `4×6` also had the expected distinct bonds and degree four at every site; the general argument is given above. No Lean processes or sub-agents were launched, and the input files were not modified.
