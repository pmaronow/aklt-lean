STATUS: COMPLETE

All eight assigned leaves are **TRUE** as written and sufficient for their stated conclusions. No missing premise or correction was found. Difficulty estimates refer to the expected Lean work, including finite-index bookkeeping.

All names below have prefix `AKLT.Blueprint.H1.`. The repository examined was branch `main`, commit `c5280ad0093d975dad9fda355e71acd980b74c65`.

| Leaf | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| [PauliExpansionStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Pauli.lean:12) | TRUE | hard | Supported whole-vector-affine exponents correspond bijectively to labels, including the constant label. |
| [PauliProductTraceStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Pauli.lean:22) | TRUE | medium | Finite tensor-index sums factor using the supplied one-slot trace equation. |
| [InversionPolynomialStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Pauli.lean:32) | TRUE | medium | Sign substitution preserves exponents and cancels vector inversion. |
| [ProductDensityPositiveStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Pauli.lean:42) | TRUE | medium | The matrix is a finite tensor product of the assumed PSD factors. |
| [InversionBallStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Pauli.lean:48) | TRUE | easy | Pointwise negation preserves the explicitly defined squared norm. |
| [RationalEmbeddingStructureStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Reduction.lean:20) | TRUE | easy | Coefficient embedding introduces no exponent. |
| [RationalEmbeddingEvaluationStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Reduction.lean:29) | TRUE | easy | This is `MvPolynomial.eval_map` after unfolding. |
| [DifferenceStructureStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Reduction.lean:36) | TRUE | easy | Scalar subtraction preserves degree, support, and the assumed invariances. |

The exact declarations and their relevant definitions were read, including the following dependencies:

| Definitions | Source and semantics checked |
| --- | --- |
| `RealVectorPolynomial`, `VectorAffineReal`, `SupportedVectorsReal` | [RealOperator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/RealOperator.lean:12): real multivariate polynomials; the **sum** of a vector's three coordinate exponents is at most one; every exponent outside `J` is zero. |
| `invertPolynomialReal`, `evaluateRealPolynomial`, `pauliExponentReal`, `pauliOperatorReal`, `productDensityReal`, `invertVectorsReal` | [RealOperator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/RealOperator.lean:23): actual sign substitution and polynomial evaluation; explicit coefficient selection; tensor entries indexed by functions on the subtype `J`. |
| `VectorPolynomial`, `pauliCoordinate` | [H1/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:14), [coordinate definition](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:155): rational coefficients on `Fin 20 × Fin 3`; label zero means one, and nonzero labels select coordinate `a.val - 1`. |
| `VectorAffine`, `SupportedVectors`, `evaluateReduced` | [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:117), [OperatorContracts.lean](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:36), [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:59): the same exponent predicates over rational coefficients, and evaluation by `eval₂ (Rat.castHom ℝ)`. |
| `OrthogonalInvariantV2` | [NodesV2Reduction.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Reduction.lean:13): evaluation is unchanged by the same real matrix `R` at every vector, provided `R.transpose * R = 1`. |
| `Vec3`, `dot`, `normSq` | [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9): functions `Fin 3 → ℝ`, with squared norm equal to the sum of coordinate squares. |
| `pauli`, `spinDensity` | [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:52): identity and the three displayed Pauli matrices in x/y/z order; density `(I + u·σ)/2`. |

The library definitions of coefficient/support, `C`, `X`, `eval`, `eval₂`, `eval₂Hom`, coefficient `map`, `Rat.castHom`, `Finsupp.equivFunOnFinite`, matrix multiplication, trace, Hermitian symmetry, `PosSemidef`, and `ComplexOrder` were also checked. In particular, `PosSemidef` requires Hermitian symmetry and nonnegative star quadratic forms; over these finite index types its finitely supported vectors cover all vectors.

**PauliExpansionStatementV2 — TRUE.**

For each exponent in `p.support`, nonnegative integer exponents and the whole-vector degree bound permit either no coordinate or exactly one coordinate of exponent one at each token. The support hypothesis excludes tokens outside `J`. This gives exactly one label function, and each label function has a different exponent. Zero coefficients may be added to the finite sum. This is the expansion argument at [d:Pauli](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:248).

Proof route, two steps:

1. Expand `MvPolynomial.eval` into supported monomials and construct the unique label function for each supported exponent.
2. Reindex by all `a : J → Fin 4`, insert zero-coefficient terms, and identify the coordinate products with the evaluated monomials.

Lean traps: `J` in a function type is its membership subtype, not `Fin J.card`. The exponent comparison uses `coordinate.val + 1`; the inverse coordinate uses guarded natural subtraction `a.val - 1`. For `a = 0` the coordinate is one. `Finsupp.equivFunOnFinite.symm` preserves the pointwise exponent function. The real coefficients need no rationality premise.

**PauliProductTraceStatementV2 — TRUE.**

Expanding the trace gives factors `pauli (a j) (σ j) (τ j) * spinDensity (u j) (τ j) (σ j)`, so the local sum has precisely the orientation of `trace (pauli (a j) * spinDensity (u j))`. The supplied equation determines every local factor, including label zero. Its premise is consistent: the imported theorem `singlePauliTrace` establishes that same equation from the displayed matrices. The tensor argument is [l:inversion, trace calculation](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:290).

Proof route, two steps:

1. Expand the matrix product and trace, interchange the finite sums, and factor the sums over tensor-index functions into products of local traces.
2. Apply the given one-slot equation and move the real-to-complex ring hom through the finite sum and products.

Lean traps: matrix multiplication sums over the full function type `J → Fin 2`; both indices must be summed. The conclusion involves only the coefficients selected by `pauliOperatorReal`, so it is valid for arbitrary `p`, even with higher degrees or variables outside `J`. No affineness, ball, PSD, or trace-one hypothesis needs to be added.

**InversionPolynomialStatementV2 — TRUE.**

On every monomial, substitution multiplies the coefficient by a sign and keeps the exponent unchanged. The sign is nonzero, so even support equality holds, though inclusion is enough here. Evaluating at `invertVectorsReal I u` applies the same sign twice. Inversions outside `J` affect variables absent from the polynomial. This is the double-inversion argument in [l:inversion](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:303).

Proof route, two steps:

1. Compute sign substitution on monomials and transfer the unchanged exponent degree and support conditions.
2. Compose evaluation homomorphisms and check constants and variables; the two signs on each inverted coordinate cancel.

Lean traps: the substitution's `-1` and `1` are polynomial constants. Membership tests and pointwise function negation must match those in `invertVectorsReal`. Neither `I ⊆ J` nor a norm restriction is necessary.

**ProductDensityPositiveStatementV2 — TRUE.**

The assumed factors are exactly the factors in the entry formula for `productDensityReal`. Finite Kronecker products of complex PSD matrices remain PSD, and simultaneous reindexing of rows and columns preserves PSD. This supplies the paper's [positive tensor-product step](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:307). The hypothesis already supplies one-slot PSD; proving it from a ball condition is a separate task.

Proof route, two steps:

1. Induct on `J`, identifying the empty density with the identity on the singleton function-index type.
2. Split off an inserted token, identify a reindexed Kronecker product, and apply `Matrix.PosSemidef.kronecker` followed by transport with `PosSemidef.submatrix`.

Lean traps: the index equivalence is between functions on the inserted subtype and a pair consisting of one spin and a function on the remaining subtype. The empty index **domain** gives one function and a 1×1 matrix `[1]`. The complex order is the intended real-part order with equal imaginary parts; Hermitian symmetry is part of PSD.

**InversionBallStatementV2 — TRUE.**

The chosen vector is either unchanged or negated in all coordinates, and `normSq` is the sum of their squares. This is the norm preservation used when the paper substitutes the inverted vectors in [l:inversion](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:271).

Proof route, two steps:

1. Unfold `invertVectorsReal` and split on `j ∈ I`.
2. Unfold `normSq` and `dot` in the negative branch and simplify each product of two negatives; the other branch is reflexive.

Lean traps: `Vec3` is an ordinary function type, so use the explicit `normSq`, rather than its default function-space norm. There is no division or nonzero-vector premise. The `n = 0` specialization has no `j`, as intended; the statement over all `n` is not vacuous.

**RationalEmbeddingStructureStatementV2 — TRUE.**

The rational and real predicates constrain precisely the same exponent functions. A coefficient map cannot create an exponent outside the original support. Thus the structural facts transfer without any new moment, geometry, or invariance premise. This is the coefficient-field compatibility used for the real polynomial of [c:reduce](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:172).

Proof route, two steps:

1. Apply `MvPolynomial.support_map_subset` to each exponent in the mapped polynomial's support.
2. Use the two original hypotheses at that exponent, then unfold the corresponding real predicates.

Lean traps: only coefficients change, while the exponent type stays `Fin 20 × Fin 3 →₀ ℕ`. The actual rational embedding is injective, but only support inclusion is needed. Decidability of real coefficient equality is a classical proof convenience, not a missing mathematical hypothesis.

**RationalEmbeddingEvaluationStatementV2 — TRUE.**

After unfolding, the two sides are `eval g (map (Rat.castHom ℝ) p)` and `eval₂ (Rat.castHom ℝ) g p`, with the identical coordinate function `g`. These are exactly the sides of the library's `MvPolynomial.eval_map`. This is the algebraic evaluation compatibility underlying the real reduction polynomial in [c:reduce](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:172).

Proof route, two steps:

1. Unfold the two evaluation definitions and expose their common coordinate function `v ↦ u v.1 v.2`.
2. Apply `MvPolynomial.eval_map` with `Rat.castHom ℝ`.

Lean traps: all vector coordinates already lie in `ℝ`; they are not rationalized or approximated. No degree, support, or unit-ball hypothesis is needed for this ring-hom identity.

**DifferenceStructureStatementV2 — TRUE.**

The support of `p - C c * q` is contained in the union of the supports of `p` and `q`. Consequently both exponent predicates are inherited. Evaluation sends this difference to `eval p - c * eval q`; the supplied invariances of `p` and `q` therefore imply its invariance. This matches the linearity step in [c:reduce](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:196).

Proof route, two steps:

1. Use `MvPolynomial.C_mul'`, `support_smul`, and `support_sub` to transfer degree and supported-token conditions.
2. Expand evaluation as a ring hom and rewrite with the two given invariance equations for the same orthogonal matrix.

Lean traps: cancellation can shrink support, so support equality is unnecessary. `C c` has degree zero. The implicit `n` in `OrthogonalInvariantV2` is fixed to 20 by the polynomial type. Zero, negative, and irrational `c` are all allowed; structural preservation needs no threshold inequalities.

Boundary cases were checked explicitly in the audit. At `J = ∅`, the expansion and product-trace formulas retain the constant coefficient and the product density is `[1]`. The first five leaves permit `n = 0`; the polynomial and matrix claims retain their intended empty-family meanings. Zero polynomials, zero scalar multipliers, complete cancellation, arbitrary real coefficients, zero vectors, and inversions outside `J` do not invalidate any leaf. The hypotheses are satisfiable, and none of the eight leaves merits a `VACUOUS` verdict.

Validation used one Lean process at a time and existing repository/package build artifacts. [Inspect.lean](/home/ubuntu/aklt/reports/TS2_H1M_01/scratch/Inspect.lean) imported the exact modules, printed all eight declarations as closed propositions, checked the relevant library lemma signatures, and evaluated the four empty-domain function cardinalities to one; the Lean run exited successfully. Its output is in [inspect.log](/home/ubuntu/aklt/reports/TS2_H1M_01/scratch/inspect.log). No additional or silently dropped instance hypotheses appeared.

The exact-arithmetic finite diagnostics in [check_indexing.py](/home/ubuntu/aklt/reports/TS2_H1M_01/scratch/check_indexing.py) passed for `n = 0,…,4`: 31 token subsets, 781 distinct exponent/coordinate cases, 11,111 double-inversion cases, and 98 squared-norm sign cases. The output is in [indexing.log](/home/ubuntu/aklt/reports/TS2_H1M_01/scratch/indexing.log). These checks target indexing and degenerate cases; the general verdicts use the mathematical arguments above.

[verdicts.jsonl](/home/ubuntu/aklt/reports/TS2_H1M_01/verdicts.jsonl) contains exactly one record per assigned leaf, including a two-line proof route and difficulty. No Lean proofs were written, no sub-agents were launched, and the repository was not modified.
