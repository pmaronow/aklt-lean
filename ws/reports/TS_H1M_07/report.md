STATUS: COMPLETE

| Leaf | Verdict | Difficulty |
| --- | --- | --- |
| `AKLT.Blueprint.H1.TensorLinearCoefficientStatement` | TRUE | medium |
| `AKLT.Blueprint.H1.SpinGeneratorTransferStatement` | TRUE | easy |
| `AKLT.Blueprint.H1.MomentPauliInterchangeStatement` | TRUE | hard |
| `AKLT.Blueprint.H1.PairExpansionFromRealizationStatement` | TRUE | hard |
| `AKLT.Blueprint.H1.UnitPairSupportStatement` | TRUE | medium |
| `AKLT.Blueprint.H1.EqualPairExchangeStatement` | TRUE | medium |
| `AKLT.Blueprint.H1.PairExpansionTransferStatement` | TRUE | easy |

All seven leaves are **TRUE as written and self-sufficient**. No missing premises, counterexamples, or unintended vacuity were found. Difficulty estimates concern writing the Lean argument from these definitions. No proofs were written.

Audited the exact statements on repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, against [Lemma l:Ostruct and its proof](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:320), including the preceding reduction and Pauli definitions. The repository was read only; all audit artifacts are in this report directory.

**Definitions followed.** In addition to the [seven statements](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:71), the audit followed these local dependency chains:

- [H1 auxiliary definitions](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:14): polynomial and tensor-space aliases, `InternalAdmissible`, `MonomialMoments`, `nextStatus`, `blochMatrix`, specialization, the real inversion and Pauli maps, `rawPauliFunctional`, `pairTerm`, and every clause of `PairExpansion`.
- [Operator definitions](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:9): both representations, degrees and replacement rules, retained sites, groups and token indices, radii and leaf neighbour, local variables and formal scalar products, rational moments and contraction, both reduced polynomials and their difference, inversion, `GroupInversion`, `pauliExponent`, and `pauliOperator`.
- [Tensor lifts and generators](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:87) and [support, pair, and tensor operators](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:9): zero extension of internal spins, leader and second-token subtypes, the actual exchange matrix, `(1 + exchange)/2`, and the tensor power.
- [Pattern data and coveredness](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:9), [geometry](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:9), [moment atoms and weights](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9), and [Pauli matrices](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:52), through their concrete finite sets, coordinates, statuses, and bond definitions.
- Mathlib's `Commute` is the equation `a * b = b * a`. `Matrix.toEuclideanLin` abbreviates `toLpLin 2 2`; [the multiplication lemma and algebra equivalence](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/Matrix.lean:55) confirm that matrix multiplication transports to composition in the same order.

**TensorLinearCoefficientStatement — TRUE, medium.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:71). The coefficient of degree one in the tensor power of `1 + t A` is exactly the sum of the one-token lifts of `A`. The universal real-parameter commutation premise therefore supplies the desired commutator coefficient. No Hermitian, unitary, or Pauli-specific assumption on `M` or `A` is required.

Proof route, line 1: Form the complex polynomial for each entry of the commutator, and use its vanishing on the infinite embedded real line to identify it with zero.  
Proof route, line 2: Extract coefficient one and identify the singleton terms of the product expansion with `tokenMatrix J j A`.

Lean traps: the polynomial coefficients are complex while `t` is real; use injectivity of `ℝ → ℂ`, rather than a polynomial identity theorem over a finite test set. Tensor slots are elements of the subtype `J`. At `J = ∅`, the function type `J → Fin 2` has one element, the tensor power is the scalar identity, and the generator sum is zero. This intended boundary case does not make the whole statement vacuous.

**SpinGeneratorTransferStatement — TRUE, easy.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:79). The token lift is complex linear, so the premise says `M` commutes with `-Complex.I` times each Pauli sum. This scalar is nonzero. The definitions of the three total-spin maps then give exactly the combinations asserted in the conclusion.

Proof route, line 1: Pull `-Complex.I` out of each sum and cancel it in the commutator, obtaining commutation with all three Pauli sums.  
Proof route, line 2: Take the defining complex linear combinations for `Z`, `Plus`, and `Minus`, and transport through `Matrix.toEuclideanLin`.

Lean traps: cancellation uses a complex scalar. `toEuclideanLin` is presented as a linear equivalence, so multiplication preservation must be invoked through `toLpLin_mul_same` or the corresponding algebra equivalence. In the empty tensor case all three generators are zero. There are no dropped instance arguments or additional representation-theoretic premises.

**MomentPauliInterchangeStatement — TRUE, hard.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:89). Both necessary restrictions on internal variables are present: `InternalAdmissible` forbids support outside `V` and bounds the total coordinate degree at each site by four. `MonomialMoments` applies to each internal factor, because every site in `V` is explicitly U or D. The contraction and raw finite sum then give the same coefficient before the Pauli transform.

Proof route, line 1: Expand the finite monomial support, separate each internal site's powers from the external vector monomial, and apply `MonomialMoments` site by site.  
Proof route, line 2: Interchange the finite sums and move sign substitution, coefficient extraction, and the rational/real/complex casts through them.

Lean traps: `Finsupp.comapDomain Sum.inr` restricts the exponent to external vector variables; it does not itself validate omitted internal sites, which is why the support half of `InternalAdmissible` matters. Keep `0^0 = 1` for constant monomials and the D zero atom. `Plane` is infinite, but the spin sum is over assignments on the finite subtype `V`. Arbitrary external degree and external variables outside `J` cause no defect: both Pauli maps select the same `pauliExponent J a` coefficients. Thus vector affineness, `SupportedVectors`, and `I ⊆ J` are unnecessary premises here. For `V = ∅`, admissibility removes all internal variables and the single empty assignment has weight one.

**PairExpansionFromRealizationStatement — TRUE, hard.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:99). The hypotheses already give both raw Pauli realizations, so a separate moment or degree assumption is unnecessary. A paired member `x` of `reductionGroups` is a positive-degree corner with `¬ SingleReplacement`. A bond incident to `x` makes it active, and the retained-site definition then puts it in `reducedSpinSites`. The four possible pairs have indices `(0,1)`, `(2,3)`, `(4,5)`, `(6,7)`; the other groups use separate tokens. Hence the selected pair factors are the only occurrences of those two vector variables.

`GroupInversion` forces those factors to share one sign, fixed across all spin assignments and both values of `next`. With spins specialized, internal bonds are scalars and all remaining vector factors avoid the selected pair. Their operators consequently commute with exchange and its symmetric projection. Since a corner is never `(0,0)`, its status is unchanged by `nextStatus`. At a U corner the `none` atom has weight zero in both sums and must be omitted. Every remaining pair spin is unit by the explicit icosahedron-norm hypothesis. At a D corner `none` gives the allowed zero vector. No positivity of the threshold, weights, or auxiliary operators is needed.

Proof route, line 1: Factor the selected pair in each supplied raw realization, construct the operator on the remaining tokens, and discard assignments with zero weight at the selected U corner.  
Proof route, line 2: Reindex the remaining current and next summands together by `Fin t`, retaining the common sign and absorbing scalar factors and `-(c : ℂ)` into their weights.

Lean traps: the witness's unit-spin condition quantifies **every** summand, including any with weight zero; retaining the U zero atom would fail that condition. Filter the finite index set before choosing its `Fin t` enumeration. An explicitly decidable filter can use `classical`; this requires no mathematical hypothesis. `secondToken` depends on a proof of the Boolean pair flag, but proof irrelevance preserves its underlying index. The `min 19` totalization is harmless for corners, whose leaders are at most six. The statement quantifies the expansion separately for each selected pair, so it requires no common enumeration across different corners.

**UnitPairSupportStatement — TRUE, medium.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:125). Put `B = 1 + eta • blochMatrix n`. The real hypotheses give `det B = 1 - eta^2 * normSq n = 0`, while `B` is Hermitian and has trace two. Thus it has rank one. For distinct slots, the product of token lifts is `B ⊗ B` with identities elsewhere, supported on the symmetric pair space on both sides.

Proof route, line 1: Use the explicit two-by-two Pauli matrices and the sign/unit equations to obtain a Hermitian rank-one matrix `B`.  
Proof route, line 2: Identify the distinct token lifts with its tensor square and apply the actual symmetric projection to its range and adjoint range.

Lean traps: establish the distinct-slot identification before using tensor-square reasoning; `pairTerm` is defined through matrix multiplication. Preserve the order when moving to endomorphisms. The projection's `1/2` is complex division. Empty and singleton slot sets have no distinct pair, but the ordinary two-slot case is nontrivial. Neither a zero norm nor division by it occurs in this argument.

**EqualPairExchangeStatement — TRUE, medium.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:133). A swap conjugates the lift at the first slot to the equal lift at the second slot. Distinct-slot lifts commute, so their product commutes with the swap. This works for every real `eta` and vector `n`; the zero vector gives the identity pair factor. When the two slots coincide, the exchange itself is the identity.

Proof route, line 1: For distinct slots, conjugate the two token lifts by exchange and commute the resulting disjoint equal-factor lifts.  
Proof route, line 2: Handle coincident slots using `exchangeOperator = 1`, and transport the matrix equation through `toEuclideanLin`.

Lean traps: the statement deliberately allows `j = k`, so that case must precede any lemma requiring disjoint slots. The absence of unit-norm and sign assumptions is correct; those assumptions belong only to the support assertion.

**PairExpansionTransferStatement — TRUE, easy.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesStructure.lean:139). Unfolding `PairExpansion` provides a single sign with square one, finite complex weights, spins satisfying the conditional unit clause, and both required commutations for every auxiliary factor. Under `unitOnly`, the supplied two-sided pair support applies to every summand. The auxiliary factor's projection commutation handles the projection on the right. Exchange commutation holds for every summand regardless of `unitOnly` and survives finite summation.

Proof route, line 1: Unpack the expansion and, under `unitOnly`, apply the supplied unit support termwise, moving the right projection past the auxiliary factor.  
Proof route, line 2: Distribute support and exchange commutation over the finite complex weighted sum to get both conclusions.

Lean traps: `unitOnly` is an explicitly quantified proposition, not an instance; introduce its proof before invoking the unit-spin clause. No assumption that an auxiliary factor commutes with `pairTerm` is needed. No positivity, nonempty expansion, or `j ≠ k` premise is needed. With `t = 0`, the expansion equation forces `O = 0`. For coincident slots the actual exchange and projection are identities. The non-unit norm bound is present in the expansion but is not needed by this algebraic transfer.

**Verification and scope.**

[Lean inspection source](inspect.lean) contains only imports, options, `#print`, and `#check`. It ran successfully with Lean `v4.35.0-rc2` against existing compiled modules; [the output](inspect.txt) confirms all seven closed propositions retain the stated parameters and hypotheses. Mathlib packages were linked into this working directory. One Lean process was used, and no library was rebuilt.

[Supplementary checks](checks.py), run with `python3 checks.py`, independently exercise small cases. [Recorded results](checks.json) include 12 exact normalized-icosahedron checks in rational quadratic arithmetic, all 70 U/D monomial moments of degree at most four, all 16 corner-pair token partitions, and four explicit covered-pattern/representation instances with a retained U or D corner. These instances use outgoing east, a removed arrival site, and the retained corner `(1,1)`, so the pair clauses have concrete nonvacuous cases.

The matrix checks cover tensor sizes zero through four, the degree-one tensor coefficient, exchange and projection identities, equal and distinct slots, both signs, unrestricted extra sign values, unit/non-unit/zero spins, signed complex weights, an auxiliary operator that need not commute with the pair term, and an empty expansion. All 384 matrix equalities passed with maximum residual about `8.96e-16` at tolerance `1e-10`. These are supplementary checks, not formal proofs of the leaves; the verdicts rest on the definition and hypothesis analysis above. The exact moment checks also show that the explicit moment premise is consistent with the intended atom laws.

Rational moment and replacement fractions are inferred in `ℚ`, atom weights in `ℝ`, and the symmetric projection scalar in `ℂ`; there is no natural-number division. No selected leaf uses natural-number subtraction. All finite tensor and assignment types have the required `Fintype` instances; any noncomputable finite filtering is handled with classical decidability. No additional mathematical fact is hidden in a dropped instance binder.
