STATUS: COMPLETE

| Definition in `AKLT/Challenge/Main.lean` (namespace `AKLT.Challenge`) | Paper text, with source file:line | Correspondence |
| --- | --- | --- |
| `Size` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | The domain L,N ≥ 3. |
| `size_neZero` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | An instance derived from that bound, needed for finite modular coordinates. |
| `Site` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | Λ = ℤ_L × ℤ_N, literally a product of `ZMod`s. |
| `Direction` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | The two positive coordinate directions used to enumerate E. |
| `Bond` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | One index per nearest-neighbour unordered edge. |
| `nextSite` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | Addition of one in the chosen modular coordinate, including wraparound. |
| `bondSites` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5), [sec2-frames-Q.tex:21](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:21) | The unordered pair underlying the chosen orientation. |
| `V` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5), [sec2-frames-Q.tex:11](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:11), [sec2-frames-Q.tex:13](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:13) | Spin 2 as orthonormal coordinates of homogeneous binary quartics, with inner product (e:Vinner). |
| `spinZ` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5), [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15) | Standard spin-2 J_z matrix; an explicit coordinate realization of the representation specified there. |
| `spinPlus` | [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15) | Standard spin-2 raising matrix in the same basis. |
| `spinMinus` | [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15) | The adjoint lowering matrix in that basis. |
| `Configuration` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5), [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15) | Labels for the tensor-product basis, one element of `Fin 5` per site. |
| `Hilbert` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5), [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15) | ℋ_Λ = ⊗_x V, in finite ℓ² coordinates. |
| `atSite` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | A matrix at one site, extended by the identity on all other factors. |
| `onBond` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | A component of the total spin of the two endpoints. |
| `bondCasimir` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5), [sec2-frames-Q.tex:32](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:32) | Total-spin Casimir Z² + (J₊J₋ + J₋J₊)/2. This explicit formula realizes the spin decomposition invoked by the paper. |
| `spin4Space` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5), [sec2-frames-Q.tex:32](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:32) | The total-spin-4 summand, characterized as Casimir eigenvalue 4·5 = 20. |
| `P` | [sec1-intro-statement.tex:5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:5) | The orthogonal projection P_e onto that space. |
| `H` | [sec1-intro-statement.tex:7](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:7) | (e:H), Σ_e P_e, with coefficient one for every edge. |
| `SpinorPolynomial` | [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15) | The ambient polynomial ring in the two spinor variables per site. |
| `singlet` | [sec2-frames-Q.tex:19](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:19), [sec2-frames-Q.tex:21](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:21) | q_xy = z_{x,1}z_{y,2} − z_{x,2}z_{y,1}, with a fixed orientation. |
| `vbsPolynomial` | [sec2-frames-Q.tex:23](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:23) | The literal product ∏_e q_e in (e:B). |
| `monomialDegree` | [sec2-frames-Q.tex:15](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:15), [sec2-frames-Q.tex:23](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:23) | The exponents of a tensor-product monomial of degree four at every site. |
| `B` | [sec2-frames-Q.tex:13](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:13), [sec2-frames-Q.tex:23](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex:23) | The same VBS polynomial, converted to the orthonormal coordinates of `Hilbert`. |
| `MainStatement` | [sec1-intro-statement.tex:9](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:9), [sec1-intro-statement.tex:12](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec1-intro-statement.tex:12) | Theorem 1.1: eventual uniqueness of the ground state and a uniform positive bound on every nonzero eigenvalue. |

The deliverables are [Main.lean](/home/ubuntu/aklt/wt/ARCH-CH/AKLT/Challenge/Main.lean) (142 lines) and [Sanity.lean](/home/ubuntu/aklt/wt/ARCH-CH/AKLT/Challenge/Sanity.lean). Completion here means the requested statement, sanity propositions, inexpensive proofs, and audit are delivered. `BNonzero`, `BondRank`, and their combined `FourByFourNondegenerate` proposition remain unproved, as permitted by the task. They are definitions of propositions, never assumptions or inputs to the other proofs. No proof of the ground-state equation or of Theorem 1.1 is supplied.

The following table covers every additional definition and the supporting sanity theorems. Source paths in this table are relative to `/home/ubuntu/aklt/manuscript/bundle/manuscript/`.

| Definition or supporting theorem in `Sanity.lean` | Paper file:line / content | Proof status |
| --- | --- | --- |
| `PIsOrthogonalProjection` | `sec1-intro-statement.tex:5`: orthogonal P_e | Proved by `p_isOrthogonalProjection`. |
| `PHasCorrectRange` | `sec1-intro-statement.tex:5`: specified total-spin-4 range | Proved by `p_hasCorrectRange`. |
| `PPositive` | `sec1-intro-statement.tex:5`: orthogonal projections are positive | Proved by `p_positive`. |
| `HPositive` | `sec1-intro-statement.tex:7`: sum of positive projections | Proved by `h_positive`. |
| `HSelfAdjoint` | `sec1-intro-statement.tex:7`: sum of self-adjoint projections | Proved by `h_selfAdjoint`. |
| `HEigenvaluesReal` | `sec1-intro-statement.tex:9`: real eigenvalues used to define the gap | Proved by `h_eigenvaluesReal`. |
| `SiteDimension` | `sec1-intro-statement.tex:5`: dim_ℂ V = 5 | Proved by `site_dimension`. |
| `SiteCount` | `sec1-intro-statement.tex:5`: Λ has LN sites | Proved by `site_count`. |
| `BondCount` | `sec1-intro-statement.tex:5`: E has 2LN edges | Proved by `bond_count`, with uniqueness established separately below. |
| `HilbertDimension` | `sec1-intro-statement.tex:5`: dim_ℂ ⊗_x V = 5^(LN) | Proved by `hilbert_dimension`. |
| `BondsHaveTwoSites` | `sec1-intro-statement.tex:5`: bonds have distinct endpoints | Proved by `bonds_haveTwoSites`. |
| `small_natCast_ne_zero` | `sec1-intro-statement.tex:5`: L,N ≥ 3, so residues 1 and 2 are nonzero | Proved helper. |
| `nextSite_ne` | `sec1-intro-statement.tex:5`: moving one step changes the site | Proved helper. |
| `BondsAreDistinct` | `sec1-intro-statement.tex:5`: E is a set of unordered bonds | Proved by `bonds_areDistinct`. |
| `BasisNormalizationNonzero` | `sec2-frames-Q.tex:13`: nonzero factors in the orthonormal coordinate change | Proved by `basis_normalization_nonzero`. |
| `BNonzero` | `sec2-frames-Q.tex:25`: B ≠ 0 | Stated only. A proof needs multihomogeneity and coefficient reconstruction to transfer the integral-domain argument to `B`. |
| `BondRank` | `sec1-intro-statement.tex:5`, `sec2-frames-Q.tex:32`: rank 9·5^(LN−2) | Stated only. A proof needs the finite Casimir decomposition and the dimension of the spectator factors. |
| `EvenSizesUnbounded` | `sec1-intro-statement.tex:12`: even sizes above an arbitrary threshold | Proved by `even_sizes_unbounded`, using size 2(K+3). |
| `four` | `sec1-intro-statement.tex:5`, `sec2-frames-Q.tex:92`: a permitted even side length | Explicit size 4, with its bound proved by kernel reduction. |
| `FourByFourSizes` | `sec1-intro-statement.tex:5`: the concrete 4 × 4 instance | Proved by `four_by_four_sizes`: 16 sites, 32 bonds, dimension 5^16. |
| `FourByFourNondegenerate` | `sec2-frames-Q.tex:25`, `sec2-frames-Q.tex:32`: nonzero VBS and rank at 4 × 4 | Stated only. The two bond-structure conjuncts are already proved generally; the remaining conjuncts are B ≠ 0 and rank 9·5^14. |

The modelling choices and their mathematical checks are as follows.

| Choice | Justification | Alternative considered |
| --- | --- | --- |
| Side lengths are a subtype of ℕ with bound ≥ 3. | Exactly the domain in §1; the finite `ZMod` instances follow from the bound. This still admits odd sizes for the model definitions; evenness is required only by `MainStatement`. | Arbitrary natural moduli would admit `ZMod 0` and need repeated finite-instance hypotheses. Positive naturals alone would retain the exceptional sizes 1 and 2. |
| Edges are indexed by site × positive direction. | This enumerates horizontal and vertical unordered edges once when both moduli are ≥ 3. `bondSites` is proved injective, its values have two sites, and the index count is proved to be 2LN. Every nearest-neighbour pair differs by ±1 in one coordinate, so choosing its positive endpoint orientation supplies such an index. | Using all four directed neighbours would count every term twice. An unordered-edge quotient is possible but adds machinery to a short statement. |
| Positive directions also fix the signs of q_e. | This is a fixed orientation as allowed at §2:21, including wraparound edges. Reversing any edge changes the product only by a global sign. | A checkerboard orientation would need evenness already in the model definitions. The paper defines B also for odd sizes ≥ 3. |
| `V` uses an orthonormal basis of binary quartics. | Write m_k = z₁^(4−k)z₂^k. Equation (e:Vinner) gives ∥m_k∥² = 1 / choose(4,k), with distinct monomials orthogonal. Indeed, 5 times the sphere integral is 5(4−k)!k!/5!. Hence e_k = √choose(4,k) m_k is orthonormal. This is the standard five-dimensional irreducible symmetric-power model, and the three explicit matrices fix its spin operators. | Raw polynomial coefficients with the standard Euclidean metric would give the wrong inner product. An abstract unspecified SU(2) representation would make the projection difficult to check. |
| Spin components use magnetic labels 2−k and ℏ = 1. | J_z e_k = (2−k)e_k; J₊e_k = √(k(5−k))e_{k−1}; J₋ = J₊*. These are the usual spin-2 matrices. In polynomial coordinates the raising formula is the action of z₁∂/∂z₂. Their Casimir is 6I. The overall Lie-algebra sign convention for the inverse substitution action does not change the Casimir. | Writing J_x and J_y as additional complex matrices would add definitions without changing Z² + (J₊J₋ + J₋J₊)/2. |
| `Hilbert` is `EuclideanSpace ℂ (Site → Fin 5)`. | Its inner product is the sum of conjugate(first coordinate) times second coordinate. The tensor products of the e_k give exactly these orthonormal coordinates. Its complex dimension 5^(LN) is proved. | A bare function type has the usual sup-norm instances; a literal iterated tensor product would require extra transport maps without making the statement easier to review. |
| `atSite` uses explicit matrix entries with off-site Kronecker deltas. | The entry is A(σ_x,τ_x) when σ and τ agree away from x, and zero otherwise: exactly A ⊗ I on the other sites. Matrix rows are output coordinates and columns are input coordinates. | Repeated tensor-product transports or arbitrary chosen bases would obscure the identity on spectator factors. |
| The spin-4 projector is specified by Casimir eigenvalue 20. | In V₂ ⊗ V₂ the spins are 0,1,2,3,4, with distinct Casimir values 0,2,6,12,20. `bondCasimir` acts as the two-site Casimir tensored with identity; thus its 20-space is the local spin-4 space tensored with the full spectator space. Its orthogonal projection is consequently P_local ⊗ I. The range and orthogonal-projection properties are proved; the rank formula is stated separately. This correspondence uses the explicit matrices and the standard decomposition, not any hypothesis from the main theorem. | A free parameter called a spin projection would under-specify the model. Defining it from the spectrum of H would be circular. A polynomial in the Casimir or explicit Clebsch–Gordan coefficients would be equivalent, but require additional constants. |
| `H` sums one copy of each orthogonal projection. | This is the coefficient-one normalization of (e:H). There is no extra factor from counting both orientations. | A sum over directed neighbours, or a differently scaled interaction, would change the claimed gap constant's normalization. |
| B is obtained from the actual polynomial product. | Each of the four incident q factors has degree one at a given site. Therefore ∏_e q_e has degree four there, and all its monomials occur among `monomialDegree σ`. If a_σ is its ordinary monomial coefficient, its e-basis coordinate is a_σ / ∏_x √choose(4,σ_x). This is exactly the definition of `B`. The denominator is proved nonzero. No unit-vector normalization or additional scalar is inserted. | Choosing an arbitrary kernel vector would lose (e:B). Using unweighted monomial coefficients as Euclidean coordinates would mismatch the Hamiltonian's metric. Merely naming the polynomial without converting coordinates would not define a vector in this Hilbert model. |
| `MainStatement` quantifies real eigenvalues through `HasEigenvalue (μ : ℂ)`. | Self-adjointness and reality of every complex eigenvalue are proved. Thus every eigenvalue has this form. `HasEigenvalue` requires a nonzero eigenvector; μ ≠ 0 excludes precisely the zero eigenvalue. A uniform lower bound on all of these is exactly the gap bound in §1:9. | A variational statement would need an equivalence proof. Quantifying every vector satisfying Hψ = μψ without requiring ψ ≠ 0 would accidentally test all scalars using the zero vector. |
| The exact kernel is the span of the singleton `{B}`. | This is the complex line ℂB, including the precise designated state. No extra assumptions about B or H appear in the statement. | An inclusion of this span in the kernel would omit uniqueness. A dimension-only condition would omit identification with B. |
| The quantifiers are ∃c>0, ∃L₀≥3, then all even L,N above L₀. | Both constants are independent of the two dimensions. Replacing any threshold by its maximum with 3 proves that the explicit lower bound on L₀ is equivalent to the paper's eventual statement on its stated domain. `EvenSizesUnbounded` rules out an empty eventual domain. | Requiring all sizes, removing evenness, fixing a square torus, or allowing c to depend on L,N would change the theorem. |
| Finite-dimensional orthogonal projections are defined noncomputably. | Mathlib supplies these canonical maps for every subspace of the concrete finite Hilbert space. All definitions are transparent Lean definitions; no computation on the full 5^16-dimensional space is required. | Explicitly enumerating a huge projection matrix would make the specification less readable and the sanity checks needlessly expensive. |

These checks explain the identification of the concrete model with the paper. A formal equivalence to an independently defined SU(2) representation, the Clebsch–Gordan decomposition, and polynomial coefficient reconstruction have not been proved in Lean here; the task allows a concrete standard model and explicitly stated, unproved expensive sanity facts.

The Lean traps checked are recorded below.

| Trap | Check and result |
| --- | --- |
| Degenerate L or N | `Size` excludes 0, 1, and 2 at construction. The proof of distinct bonds explicitly uses non-vanishing of residues 1 and 2. Sizes 3 and larger remain in the model. |
| Duplicate bonds | `bonds_areDistinct` handles both equal and reversed endpoint pairs. Two successive positive steps cannot return to the initial site for the allowed moduli. Together with `bond_count`, this gives 2LN actual unordered bonds. |
| `ZMod 0` | Impossible for `Size`; `size_neZero` is derived, not assumed. The accidental infinite type `ZMod 0` cannot enter `Hilbert`. |
| Coercions | Moduli and bounds use `.val : ℕ`; matrix entries use explicit ℂ casts; square roots are taken in ℝ and then embedded in ℂ. The Casimir coefficient is `(1 / 2 : ℂ)`, and its eigenvalue is a complex 20. The gap constant and ordered eigenvalue variables are real. |
| Real versus complex inner products | All spaces and linear maps use ℂ. `EuclideanSpace` supplies the Hermitian sum inner product. `LinearMap.IsPositive` means symmetry together with nonnegative real part of the quadratic form; `IsSelfAdjoint` uses the corresponding adjoint on finite-dimensional linear maps. Complex eigenvalues are proved fixed by conjugation. |
| `LinearMap.ker` versus eigenvalue 0 | The kernel equality is the actual linear-map kernel. The gap quantifier uses Mathlib's nonzero-eigenvector notion and excludes scalar zero. A zero vector therefore cannot create a spurious eigenvalue. The kernel is not replaced by an assertion that 0 occurs in the spectrum. |
| `finrank` assumptions | Every dimension is over ℂ. Finite-dimensional instances come from finite `EuclideanSpace` indices, and ranges are finite-dimensional submodules. The proved dimensions are 5 and 5^(LN). In the rank proposition LN ≥ 9, so the natural subtraction LN−2 does not truncate a negative integer. |
| Implicit `Fintype` and `DecidableEq` | The nonzero moduli supply finite `ZMod` types. Products, `Fin 2`, `Fin 5`, and functions on finite sites inherit the required finite/equality instances. All parameterized definitions and proofs compile, rather than relying only on a closed 4 × 4 example. |
| Polynomial basis and division | Variable 0 means z₁, variable 1 means z₂; configuration k means z₁^(4−k)z₂^k. Since k < 5, the natural subtraction and binomial indices are valid. `basis_normalization_nonzero` proves the product of square roots is nonzero. |
| Hidden hypotheses and unproved propositions | None of the sanity propositions is an argument to `MainStatement`. The unproved propositions have no supplied inhabitants and are unused by all 17 sanity proofs. |
| Vacuous size quantification | `even_sizes_unbounded` constructs a permitted even size above each natural threshold. Both L and N can be chosen this way independently. |
| Imports and proof dependencies | `Main.lean` imports only `Mathlib`; `Sanity.lean` imports only `AKLT.Challenge.Main`. Every proved sanity theorem has a printed dependency audit below. |

Validation used Lean 4.35.0-rc2 (commit `11acb17ec6b07a8f9e9173e6845197929540936b`) and the existing Mathlib revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Both files compiled successfully with the project's implicit-variable checks enabled. Commands, run from the worktree, were:

```bash
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake/build/lib/lean/AKLT/Challenge
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -o .lake/build/lib/lean/AKLT/Challenge/Main.olean AKLT/Challenge/Main.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -o .lake/build/lib/lean/AKLT/Challenge/Sanity.olean AKLT/Challenge/Sanity.lean
```

Only the requested Lean modules were compiled. Mathlib was imported from the prebuilt installation; its dependency checkout and build were not changed. Lean processes were run sequentially, and no sub-agents were launched. The source audit found no prohibited declarations or proof shortcuts in either delivered Lean file.

The complete successful output of the 17 `#print axioms` commands in `Sanity.lean` is reproduced verbatim below and saved separately in [sanity-axioms.txt](/home/ubuntu/aklt/reports/ARCH-CH/sanity-axioms.txt). Each dependency is among the three permitted axioms.

```text
'AKLT.Challenge.p_isOrthogonalProjection' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.p_hasCorrectRange' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.p_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.h_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.h_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.h_eigenvaluesReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.site_dimension' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.site_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.bond_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.hilbert_dimension' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.small_natCast_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.nextSite_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.bonds_haveTwoSites' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.bonds_areDistinct' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.basis_normalization_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Challenge.even_sizes_unbounded' depends on axioms: [propext, Quot.sound]
'AKLT.Challenge.four_by_four_sizes' depends on axioms: [propext, Classical.choice, Quot.sound]
```
