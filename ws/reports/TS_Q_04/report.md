STATUS: COMPLETE

| Leaf in `AKLT.Blueprint.Q` | Module | Paper label | Verdict | Difficulty |
| --- | --- | --- | --- | --- |
| [SpectatorDivisibilityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesPolynomial.lean:44) | NodesPolynomial | l:edge | TRUE | hard |
| [SingletNonassociateStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesPolynomial.lean:57) | NodesPolynomial | l:divisibility | TRUE | medium |
| [IncidentKernelStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesPolynomial.lean:70) | NodesPolynomial | l:quantumfibre | TRUE | easy |
| [PairDiagonalRankStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:15) | NodesSplits | l:edge | TRUE | medium |
| [PairTopInclusionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:19) | NodesSplits | l:edge | TRUE | hard |
| [PairTopDimensionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:25) | NodesSplits | l:edge | TRUE | hard |
| [FourVariableDeterminantPrimeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:31) | NodesSplits | l:divisibility | TRUE | medium |
| [DeterminantPrimeEmbeddingStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesSplits.lean:38) | NodesSplits | l:divisibility | TRUE | medium |

All eight leaves are true and self-sufficient as written. No fixes or additional hypotheses are required. None depends on an empty domain or a contradictory premise. The two implication leaves explicitly supply their pair-divisibility and four-variable-primality premises; both premises are themselves mathematically true.

The machine-readable results are in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_Q_04/verdicts.jsonl). Difficulty estimates concern formalization from the stated definitions with Mathlib, without assuming sibling leaves.

**Definitions and paper checked.**

The dependency read covered the relevant definitions in [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:72), [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:17), and [Defs/Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:49), through their imported statement layer. The paper arguments are [l:edge](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:78), [l:divisibility](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:137), and [l:quantumfibre](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:546).

In particular, the following meanings were checked rather than inferred from names:

- `Size = {n : ℕ // 3 ≤ n}`; `Site L N = ZMod L.val × ZMod N.val`; `Direction = Fin 2`; `Bond L N = Site L N × Direction`. `nextSite` adds one in the selected coordinate, and `bondSites` is its unordered endpoint finset.
- `Configuration L N = Site L N → Fin 5`; `Hilbert L N` and `PairHilbert` are standard complex Euclidean spaces on configuration labels and `Fin 5 × Fin 5`, respectively. Their coordinates are orthonormal.
- `spinZ` has diagonal entries `(2 : ℂ) - (j.val : ℂ)`. `spinPlus` sends basis vector `j` to `j-1` with coefficient `sqrt(j*(5-j))`, and `spinMinus` is its conjugate transpose. `atSite` and `pairAt` lift these matrices with the appropriate off-factor Kronecker deltas. `onBond` sums the two endpoint lifts. Both Casimirs use `Z*Z + (1/2 : ℂ) • (U*D + D*U)`.
- `spin4Space e` is the eigenvalue-20 eigenspace of `bondCasimir e`. `P e` and `pairProjector` are the corresponding **orthogonal** projections. `siteHamiltonian x` is the sum over all bond indices with the incident-edge indicator.
- `SpinorPolynomial L N` is the complex polynomial ring on `Site L N × Fin 2`. `singlet e` is exactly `X(x,0)*X(y,1) - X(x,1)*X(y,0)`. `statePolynomial` uses the monomial exponents `4-σ(x)` and `σ(x)`, encoded by `monomialDegree`, and coefficient multiplier `∏x sqrt(choose 4 (σ x).val)`.
- `PairPolynomial` has variables `Fin 2 × Fin 2`. `pairPolynomial` uses the same endpoint normalization. `pairDiagonal` renames variables by `Prod.snd`, identifying the two site coordinates. `pairSinglet` has the matching determinant orientation.

Mathlib's underlying meanings were also checked: `Matrix.toEuclideanLin` uses orthonormal coordinate bases; `eigenspace C 20 = ker(C - 20 • 1)`; `starProjection` is the full-space orthogonal projection. Standard finite-dimensionality and `HasOrthogonalProjection` instances follow from the Euclidean spaces. Lean printed all eight declarations as closed propositions with the expected quantifiers, with no omitted section parameters; see [inspection.txt](/home/ubuntu/aklt/reports/TS_Q_04/inspection.txt).

**SpectatorDivisibilityStatement — TRUE; hard.**

Distinct endpoints permit a coordinate permutation into endpoint pairs and configurations of the remaining sites. This permutation is an isometry for the actual Euclidean inner product. In these coordinates the global bond Casimir is a direct sum of copies of `pairCasimir`. Its eigenvalue-20 space, and hence its orthogonal projection, decompose fibre by fibre. The assumed pair implication therefore applies to every spectator coefficient. The product of spectator binomial factors belongs in the spectator monomial coefficient, giving exactly `statePolynomial`, with no global rescaling.

Route, line 1: Split configurations at the endpoints and transport the Casimir eigenspace and its orthogonal projection through the finite isometric coordinate permutation.  
Route, line 2: Apply the supplied pair implication on every fibre, rename `pairSinglet` to `singlet e`, and sum the quotients against the normalized spectator monomials.

Lean traps: transporting the Casimir alone does not immediately transport its projection; use the isometry and uniqueness of orthogonal projection. Preserve the endpoint order and spectator square-root factors. Finite choice of quotients is allowed classically. No separate representation or tensor-transport premise is needed because the operators are explicitly defined. The conclusion asks only for divisibility, so no quotient-degree premise is missing. The pair premise is nonvacuous: its projector has a 16-dimensional kernel, and the two-site diagonal-kernel division argument establishes the implication.

**SingletNonassociateStatement — TRUE; medium.**

The period bounds rule out loops and repeated unordered endpoint sets, including when a period is three. A nonzero singlet depends on both spinor variables of each endpoint. Association in this polynomial ring means multiplication by a nonzero complex constant, which preserves that variable set. Equal variable sets would give equal endpoint sets and hence equal positive-direction bond indices.

Route, line 1: Derive injectivity of `bondSites` from the period bounds and compute the four-variable set of each singlet.  
Route, line 2: Express a polynomial unit as a nonzero constant and use invariance of the variable set under that scalar to contradict distinct bonds.

Lean traps: `Bond` is an oriented index type, so injectivity of its unordered endpoint representation must be established. Reversing an arbitrary ordered pair changes a determinant by a unit; the positive-direction indexing and `Size` bounds prevent such a duplicate here. `MvPolynomial.isUnit_iff_eq_C_of_isReduced` applies because ℂ is reduced. Existing independent corroboration is [Uniq.singletNonassociate](/home/ubuntu/aklt/repo/AKLT/Uniq/BondAlgebra.lean:76); the verdict does not assume that theorem as a hypothesis.

**IncidentKernelStatement — TRUE; easy.**

The real quadratic form of `siteHamiltonian x` at `ψ` is the finite sum of `‖P e ψ‖²` over incident edges. Each summand is nonnegative because `P e` is definitionally an orthogonal projection. Vanishing of the Hamiltonian vector forces that sum to be zero and hence each incident projection vector to vanish.

Route, line 1: Take a real inner product with `ψ`, expand the finite sum, and use the orthogonal-projection norm identity.  
Route, line 2: Extract each zero summand using nonnegativity, then conclude from its squared norm that `P e ψ = 0`.

Lean traps: use real parts of complex inner products; ℂ has no ordered positivity argument. `Submodule.re_inner_starProjection_eq_normSq` uses the projection in the first inner-product argument; conjugate symmetry handles the other order. The definition sums over `Fintype Bond` with an indicator, while incidence is membership in `bondSites e`; simplify those indicators before extracting a summand. Neither commuting projectors nor spectral information about the Casimir is required.

**PairDiagonalRankStatement — TRUE; medium.**

The image of coordinate `(j,k)` is a nonzero multiple of `X0^(8-j-k)*X1^(j+k)`. Every sum from zero through eight occurs, so the range has dimension nine and the 25-dimensional domain has kernel dimension sixteen. All normalization factors are strictly positive because `j,k : Fin 5`.

Route, line 1: Identify the range with the span of the nine degree-eight monomials, using `j = max(0,s-4)` and `k = s-j` to exhibit preimages.  
Route, line 2: Apply finite-dimensional rank-nullity to the domain and the range to obtain `25 - 9 = 16`.

Lean traps: the stated codomain is the entire `MvPolynomial (Fin 2) ℂ`, which is infinite-dimensional. Do not apply a theorem requiring that whole codomain to be finite-dimensional; use the range or a nine-coordinate coefficient map. Natural subtraction is safe because each endpoint exponent index is at most four. Reciprocal normalizations require explicit nonzero square-root facts.

**PairTopInclusionStatement — TRUE; hard.**

Put `a_j = sqrt(choose 4 j)`. The orthogonal complement of the diagonal kernel is spanned by the nine vectors `w_s(j,k) = a_j*a_k` for `j+k=s`, with zero entries elsewhere. Their supports are disjoint. Applying the exact frozen spin matrices gives `pairCasimir w_s = 20 • w_s` for every `s`. The rationalized exact checks below confirm all nine identities, including the square-root normalization.

Route, line 1: Extract the nine coefficient functionals of `pairDiagonal` and identify their representing vectors `w_s` as a spanning set of the kernel orthogonal complement.  
Route, line 2: Verify eigenvalue twenty on those vectors using the explicit spin matrices, then extend linearly to their span.

Lean traps: the polynomial codomain has no supplied inner product, so the paper's adjoint of diagonal evaluation cannot be used directly on this `pairDiagonal`. First pass to its nine coefficient coordinates, or work with the representing vectors directly. Inner products conjugate the first argument; the coefficient vectors here are real, so the required conjugation leaves them unchanged. The diagonal rescaling used in the diagnostics is not unitary and must not be used to preserve orthogonal complements.

**PairTopDimensionStatement — TRUE; hard.**

The Casimir preserves `j+k`, giving block sizes `1,2,3,4,5,4,3,2,1`. In block `s`, its eigenvalues are `ℓ*(ℓ+1)` for `ℓ = |4-s|,...,4`, each once. In particular, the eigenspace at twenty has one dimension in every block, for total dimension nine. Exact row reductions independently compute these geometric nullities, so the conclusion does not rely on assuming diagonalizability from a characteristic polynomial alone.

Route, line 1: Decompose the pair space into the nine `j+k` blocks and remove square roots by an invertible diagonal similarity.  
Route, line 2: Calculate the rank of `C-20I` as `block_size-1` in each block and add the nine kernel dimensions.

Lean traps: `finrank` is over ℂ, and the eigenvalue numeral is a complex scalar. An exact rational matrix computation transfers through the explicit similarity and the field embedding into ℂ; a numerical floating-point rank would not suffice. This leaf can be established independently of the top-inclusion leaf.

**FourVariableDeterminantPrimeStatement — TRUE; medium.**

The determinant is `X0*T - X1*X2` in `A[T]`, where `A = ℂ[X0,X1,X2]` and `T = X3`. Its coefficients are relatively prime: the prime variable `X0` divides neither `X1` nor `X2`. The primitive linear polynomial is irreducible over the fraction field and hence irreducible in `A[T]`; the UFD property gives primality in the stated ring.

Route, line 1: Single out variable three and establish `IsRelPrime X0 (-X1*X2)`, with variable three absent from both coefficients.  
Route, line 2: Use primitive linear-polynomial irreducibility, then irreducible-implies-prime in the multivariate polynomial UFD.

Lean traps: the leading coefficient is a variable, so this is not a monic-polynomial argument. Use `IsRelPrime`, meaning no common nonunit divisor; the stronger Bezout/comaximal assertion `IsCoprime X0 (X1*X2)` is false. The local Mathlib has `MvPolynomial.irreducible_mul_X_add`, which directly packages the needed linear step. All four numeral indices are distinct in `Fin 4`.

**DeterminantPrimeEmbeddingStatement — TRUE; medium.**

For endpoints `x ≠ y`, the variable map is `0 ↦ (x,0)`, `1 ↦ (x,1)`, `2 ↦ (y,0)`, `3 ↦ (y,1)`. It is injective and maps the displayed four-variable determinant exactly to `singlet e`. The ambient ring adjoins the other site variables freely; prime elements remain prime under that polynomial extension. Endpoint distinctness is already guaranteed by `Size`.

Route, line 1: Identify `Fin 4` with the subset of the four endpoint spinor variables, using the period bounds to prove endpoint distinctness.  
Route, line 2: Rename through that equivalence and apply `MvPolynomial.prime_rename_iff` for inclusion of the variable subset into the full ring.

Lean traps: an arbitrary injective ring homomorphism need not preserve primes. The needed fact concerns inclusion of independent polynomial variables. Mathlib's `prime_rename_iff` is stated for a subtype inclusion, so factor the four-variable injection through its image. No factoriality premise needs to be added: all rings here are explicitly polynomial rings over ℂ, and the primality premise is already written out.

**Validation and limits.**

[checks.py](/home/ubuntu/aklt/reports/TS_Q_04/checks.py) ran successfully using only Python's standard library. Its exact-arithmetic output is saved in [checks.json](/home/ubuntu/aklt/reports/TS_Q_04/checks.json). With `D_(j,k) = sqrt(choose(4,j)*choose(4,k))`, the similar matrix `D C D⁻¹` has rational entries: diagonal `12 + 2*(2-j)*(2-k)` and off-diagonal coefficients `j*(4-k)` and `(4-j)*k` for moves `(j,k) → (j-1,k+1)` and `(j,k) → (j+1,k-1)`. Positivity and exact squared identities verify the change of coordinates without approximate radicals. The script checks all nine eigenvector identities, rank nine of diagonal evaluation, each shifted block rank, and each block characteristic polynomial.

| Weight blocks `s=j+k` | Size per block | Rank after subtracting `20I` | Nullity per block | Eigenvalues |
| --- | --- | --- | --- | --- |
| 0, 8 | 1 | 0 | 1 | 20 |
| 1, 7 | 2 | 1 | 1 | 12, 20 |
| 2, 6 | 3 | 2 | 1 | 6, 12, 20 |
| 3, 5 | 4 | 3 | 1 | 2, 6, 12, 20 |
| 4 | 5 | 4 | 1 | 0, 2, 6, 12, 20 |

The script also checked every bond of all 36 tori with `3 ≤ L,N ≤ 8` for endpoint distinctness, unique unordered endpoint sets, four distinct endpoint variables, distinct determinant scalar classes, and four incident bonds per site. These finite tests corroborate the general period-bound arguments; the all-size verdicts use those arguments rather than extrapolation from tests. The zero state causes no exception to either divisibility or the incident-kernel statement.

[Inspect.lean](/home/ubuntu/aklt/reports/TS_Q_04/Inspect.lean) completed with exit status zero under `leanprover/lean4:v4.35.0-rc2`, importing the existing two statement modules and printing their declarations and relevant Mathlib interfaces. It contains no theorem declarations or proofs. One Lean process was used; no repository modules were rebuilt. The scratch Mathlib package path is a symlink to the supplied packages. All generated files are in the assigned report directory, and the repository was not modified. This is a mathematical truth audit with exact finite diagnostics, not a claim that new Lean proofs of these leaves were constructed.
