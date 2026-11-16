STATUS: PASS
BLOCKING: 0

Scope and source conventions: `lean/` means `/home/ubuntu/aklt/review/FID_S/lean/`; `paper/` means `/home/ubuntu/aklt/review/FID_S/paper/`; `Mathlib/` means `/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`. I read all of `lean/AKLT/Defs/OperatorContracts.lean` and its transitive AKLT imports: `FiniteNetwork`, `Probability`, `Operator`, `Pattern`, `Frame`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. I also inspected the callers in `lean/AKLT/Blueprint/Top/Operator.lean` and the relevant Mathlib definitions. Only the five assigned declarations are judged below.

DECL: symmetricPairProjection PASS

The matching object is the projection onto a retained pair's symmetric square in Lemma `l:Ostruct`, `paper/app-local-operator.tex:324–326`, with the ambient Hilbert realization specified at lines 432–440. The paper also tensors these pair projections with identities on other factors at lines 863–868.

Here `J` as a type is the subtype of tokens belonging to the finite set, and `J → Fin 2` indexes all elementary tensor basis vectors. Its finiteness comes from `Mathlib/Data/Fintype/Sets.lean:226` and `Mathlib/Data/Fintype/Pi.lean:134`; membership proofs do not introduce extra basis coordinates. `EuclideanSpace ℂ` uses the usual sum Hermitian inner product, rather than the sup norm on an unwrapped function space (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:84–115`).

Writing `S = exchangeOperator J j k`, its matrix sends the elementary vector indexed by `τ` to that indexed by `τ ∘ Equiv.swap j k`. The swap exchanges exactly the two designated tokens, fixes the others, and is its own inverse (`Mathlib/Logic/Equiv/Basic.lean:636–673`). `Matrix.toEuclideanLin` is ordinary column-vector matrix action with the Euclidean wrapper (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:1242`; `Mathlib/Analysis/Normed/Lp/Matrix.lean:44–45`; `Mathlib/Data/Matrix/Mul.lean:707`). Thus `S` is a self-adjoint involution and `(I + S)/2` is precisely the orthogonal projection onto symmetric pair tensors, acting identically on other factors. In `Module.End`, `1` is the identity map and multiplication is composition (`Mathlib/Algebra/Module/LinearMap/End.lean:44–59`); addition and scalar multiplication are pointwise (`Mathlib/Algebra/Module/LinearMap/Defs.lean:744,830`). The explicit `ℂ` annotation makes `1 / 2` the nonzero complex scalar one half, with no natural-number division (`Mathlib/Basic/Complex/Basic.lean:712,732`).

The actual caller, `lean/AKLT/Blueprint/Top/Operator.lean:85–88`, selects the leader and second token of a retained corner pair. `groupIsPair` forces a corner; its leader is one of 0, 2, 4, 6 and its second token is respectively 1, 3, 5, 7 (`lean/AKLT/Defs/Operator.lean:35–46`). Consequently the call always has distinct tokens, and the `min 19` in `groupSecond` never clamps these values. No intended pair projection degenerates to the identity.

DECL: tensorPowerMatrix PASS

This is the matrix of `U` raised to a tensor power in `paper/app-local-operator.tex:322`, explicitly used by conjugation at lines 343–358. In the elementary tensor basis, its row `σ`, column `τ` entry is exactly the product of `g (σ j) (τ j)` over the tensor slots. The paper's corresponding Pauli tensor entry formula at lines 716–722 uses the same row/column convention, as does `pauliOperator` in `lean/AKLT/Defs/Operator.lean`.

The product is over every member of `J` once (`Mathlib/Data/Fintype/Sets.lean:226–230`), not over all twenty possible tokens. Products of complex entries are commutative, so a choice of enumeration adds no ordering convention or permutation sign. There is no transpose, complex conjugation, symmetrization, or normalization in this definition. Matrix multiplication is ordinary composition through its summed intermediate index (`Mathlib/Data/Matrix/Mul.lean:298`), consistent with the tensor action above.

Allowing arbitrary two-by-two complex `g` is appropriate for this auxiliary construction. Its caller restricts `g` by `g.conjTranspose * g = 1` and `g.det = 1` (`lean/AKLT/Blueprint/Top/Operator.lean:82–83`), exactly the unitary determinant-one matrices in the paper. Conjugate transpose means transpose followed by entrywise star (`Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:36,133`). If `J` is empty, there is one function `J → Fin 2`, and its single matrix entry is the empty product 1. This is the identity on ℂ, matching the paper's explicit empty tensor convention at `paper/app-local-operator.tex:16–18`.

DECL: leadingMinor PASS

The paper defines `Δ_j` as the determinant of the leading `j × j` block, with `Δ_0 = 1`, at `paper/app-local-operator.tex:790–800`; its positivity criterion is at lines 594–595 and 766–788.

`Matrix.submatrix` has entry `M (r i) (c j)` (`Mathlib/LinearAlgebra/Matrix/Defs.lean:476–483`). Both index maps here send `i : Fin k` to the same numeric value in `Fin n`. The hypothesis `k ≤ n` makes these maps valid and injective, and selects precisely indices 0 through `k - 1` in their original order on both axes. The proof argument supplies only the bounds, with no effect on entries. No permutation sign or off-by-one shift is introduced. `Matrix.det` is the signed Leibniz determinant over the commutative ring ℤ (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:55–68`), so all arithmetic is exact. Its empty determinant is 1 (`:94,795`), including when `n = k = 0`.

The caller quantifies over exactly `0 < k ≤ n` for the positivity criterion (`lean/AKLT/Blueprint/Top/Operator.lean:131–132`). The size-zero case consequently has no positivity conditions, as the paper explicitly requires at line 786. Integer symmetry there means transpose equality (`Mathlib/LinearAlgebra/Matrix/Symmetric.lean:35`), and `PosDef` means Hermitian with strictly positive quadratic form on every nonzero vector (`Mathlib/LinearAlgebra/Matrix/PosDef.lean:164–165`). The real cast therefore tests the intended positive definiteness; no symmetry or positivity hypothesis belongs in the minor's own definition.

DECL: bareissState PASS

This implements the optional recurrence in Lemma `l:integercheck`, `paper/app-local-operator.tex:595–606`, with its bordered-minor invariant and exact-division argument at lines 790–821. At stage zero the pair is exactly `(A⁽⁰⁾, p₋₁) = (M, 1)`. Before the update at stage `j < n`, the first component is `A⁽ʲ⁾` and the second is 1 for `j = 0`, otherwise the preceding pivot `p_(j−1)`. The new second component is the old entry `A⁽ʲ⁾_(j,j)`, not an already updated entry.

For precisely `i,l > j`, the new entry is `(A⁽ʲ⁾_(j,j) A⁽ʲ⁾_(i,l) − A⁽ʲ⁾_(i,j) A⁽ʲ⁾_(j,l)) / p_(j−1)`, with the paper's sign and row/column order. Every right-hand entry comes from `old`, making this a simultaneous update. Other entries are retained; the paper specifies only the trailing update, and later pivots and numerators never consult entries outside the required trailing block. The stored previous pivot avoids representing the paper's index −1 using truncated natural subtraction; there is no natural subtraction in this declaration.

The division is integer Euclidean division, not rational division (`Mathlib/Algebra/EuclideanDomain/Int.lean:21–25`). On a nonzero divisor dividing the numerator it equals the exact integer quotient (`Mathlib/Algebra/EuclideanDomain/Basic.lean:85–101`), including for negative pivots. The caller supplies `∀ k < j, bareissPivot M k ≠ 0` and concludes divisibility for every pair of trailing indices (`lean/AKLT/Blueprint/Top/Operator.lean:133–138`). This is precisely the paper's preceding-pivot condition; at `j = 0` the divisor is 1. A zero current pivot is still permitted when calculating that pivot and performing the current update, just as in the paper.

The state freezes after the last valid stage. Its values after a zero preceding pivot are merely a total extension: Lean's division by zero returns zero, and nonexact integer division can round. Neither behavior enters the guarded paper correspondence or can satisfy a requirement that every valid pivot be positive. No extra nonzero or positive hypothesis is silently imposed by this auxiliary definition.

DECL: bareissPivot PASS

The paper sets `p_j = A⁽ʲ⁾_(j,j)` for `0 ≤ j < t` at `paper/app-local-operator.tex:596–597` and identifies it with the leading minor of order `j + 1` at lines 603–605 and 799–800. This definition reads exactly that diagonal entry from the state before the `j`-th update. Natural `j` already supplies the lower bound, and the dependent branch `j < n` supplies the correct finite index on both axes. There is no shift to the next state, no absolute value, and no loss of the determinant's sign.

The zero returned for `j ≥ n` is outside the paper's pivot range. In the caller, `j < n`, and all preceding indices `k < j` also satisfy `k < n` (`lean/AKLT/Blueprint/Top/Operator.lean:133–134`). Thus neither the pivot identity nor its nonzero hypotheses sees this sentinel. For `n = 0` there are no valid pivots, matching the paper's size-zero convention. The previous pivot at stage zero is separately stored as 1, so this out-of-range zero never substitutes for `p₋₁`.

Non-blocking remarks:

- The equal-token extension of `symmetricPairProjection` is the identity. The caller's retained-pair construction guarantees distinct tokens, so this adds no degenerate reading to the paper contract.
- The unrestricted Bareiss helpers should continue to be used with their current range and nonzero-pivot guards. Their totalized values alone do not assert exact division or a successful certificate.
- As supplemental checks, Python exhaustively tested 15,756 symmetric integer matrices of sizes 0–3 with independent upper-triangle entries in −2 through 2. All 39,355 applicable pivot/minor identities and 75,125 applicable exact divisions passed. A rational-coordinate projection check verified self-adjointness, idempotence, symmetric fixed vectors, and antisymmetric kernel vectors for two nonadjacent slots among three factors. Tensor entries matched independently iterated Kronecker products for powers 0–3, including power zero. These checks support the source-level analysis; they are not Lean proofs. No Lean processes were launched, and no inputs were modified.
