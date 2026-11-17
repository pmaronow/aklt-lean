STATUS: COMPLETE

All eight assigned leaves are **TRUE** and self-sufficient as written. No missing premises or corrected statements are needed. None is globally vacuous; the empty cases described below are intended special cases.

| Leaf (`AKLT.Blueprint.H1.` prefix) | Verdict | Difficulty |
| --- | --- | --- |
| [`SectorWeightBasisStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:19) | TRUE | hard |
| [`SpanWeightLatticeStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:29) | TRUE | medium |
| [`SpinAdjointStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:39) | TRUE | medium |
| [`SpinCommutatorStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:46) | TRUE | medium |
| [`WeightLadderTransferStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:56) | TRUE | medium |
| [`CommonWeightEigenvectorStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:70) | TRUE | medium |
| [`LadderWalkStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:83) | TRUE | medium |
| [`PositiveSpectrumStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:96) | TRUE | medium |

Audited repository: branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository was read only and its working tree was clean at the final check. No proofs were written and no sub-agents were launched.

**Definitions and paper trace.**

| Source | Definitions or argument checked |
| --- | --- |
| [H1 auxiliary definitions](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:16) | TensorSpace = EuclideanSpace Complex (J → Fin 2); sectorVector is the integer coefficient vector cast to Complex; SpinStable preserves S under all three generators; WeightLadder contains two weight shifts and two strict-sign nonvanishing implications. Relevant definitions are at lines 16 and 181–194. |
| [FiniteNetwork definitions](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:71) | PositiveOn, eigenvaluesOn, tokenMatrix, and totalSpinZ/Plus/Minus (lines 71–100). These use ambient Euclidean inner products, nonzero eigenvector witnesses, and actual tensor-coordinate matrices. |
| [Operator definitions](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:9) | Representation; patternDegree; SingleReplacement; reductionGroups; groupLeader/Second; groupIsPair; reductionVectors (lines 9–51); ExchangeSigns, GroupBasis and its Fintype instance, ExchangeBasis, exchangeWeight, centralWeight, and exchangeBasisVector (lines 159–210). |
| [Pattern definitions](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:8) | templateSites/Tips/Corners, PatternData, statusAt, keptAt, and bonds (lines 8–37 and 59–63). Coveredness is a separate predicate and is not needed for these weight identities. |
| [Geometry](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8), [Status](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:50), [Pauli matrices](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:53) | Plane = Integer × Integer; latticeDist, Compass.step, positiveNeighbours, internalBonds, and square; Status = U/D/X; pauli 1/2/3 with the actual imaginary signs. These settle the geometric and local matrix definitions used above. |
| [Paper preparation](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:418) | Definition d:exchange and the following paragraphs, lines 418–470: singles, symmetric/exterior pairs, parity lattice, local matrices, adjoints, and commutators. |
| [Paper lemma](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:472) | Lemma l:sector and proof, lines 472–522: a common weight eigenvector, norm identity, ladder walk, and positivity via a finite orthonormal eigenbasis. The current TeX line numbers differ from the historical numbers in Lean docstrings. |

**Shared Lean and boundary checks.**

- All eight declarations elaborate as closed `Prop`s. There are no dropped section-instance hypotheses. In particular, SpanWeightLatticeStatement explicitly retains its quantified `[Fintype beta]`.
- A token is an element of the subtype of the Finset J; the tensor-coordinate index type is the finite function type `J → Fin 2`. For J empty, that function type has one element and TensorSpace has complex dimension one. All three spin endomorphisms are then zero.
- For an empty spanning index type beta, its span is bottom and cannot contain the required nonzero eigenvector. For S = bottom, CommonWeightEigenvector has no eigenvalue to consider, LadderWalk has no nonzero starting vector, and both sides of PositiveSpectrum hold. These do not make the universal leaves vacuous.
- The full eight-group slot sets are `{0,1}`, `{2,3}`, `{4,5}`, `{6,7}`, `{8}`, `{11}`, `{14}`, `{17}`. A single corner uses only its leader. Thus raw PatternData cannot cause overlapping factors. With no groups, ExchangeBasis has one element, sectorVector is the scalar 1, and both weights are zero.
- Rational weights cast exactly to Real and Complex. In particular, `1 - (b.val : Rational)` does not use natural subtraction, the central `1/2` is rational, and the ladder target `1/2` is real. The usual local `classical` mode handles finite-set and real-equality decidability; it is not an extra premise.

**Per-leaf reasons, routes, and traps.**

**SectorWeightBasisStatement — TRUE; hard.**

reductionGroups is a subset of the eight fixed corner/tip sites. Their groupLeader slots are distinct; corner second slots are 1,3,5,7 and disjoint from every other group's slots, so no coveredness assumption is needed. exchangeBasisVector is the genuine tensor product of single e_0/e_1, symmetric (00,01+10,11), or exterior (01-10) vectors, whose Z weights are respectively 1/2-b, 1-b, and 0. The rational exchangeWeight is their sum. If t is the number of singles, that sum differs from t/2 by an integer, and centralWeight is 0 or 1/2 according to the parity of t. The empty-group vector is the scalar 1 of weight 0.

Route, line 1: Establish disjointness and coverage of the defined token groups; apply diagonal Z to the tensor-coordinate product and sum the stated local weights.<br>
Route, line 2: Separate singles from pairs and split the parity of their count to exhibit exchangeWeight - centralWeight as an integer, then cast the rational equality into Real.

Lean traps: The basis index is a dependent function over the subtype of reductionGroups. GroupBasis is Fin 2, Fin 3, or Fin 1; its value bounds matter in the coefficient case splits. Cast b.val into Rational before subtracting. The exterior vector has a minus sign but weight zero. groupSecond uses min 19, but for actual pairs its leader is at most 6, so no truncation or slot collision occurs. ExchangeSigns includes unused single/U-pair signs; these do not change this conclusion.

**SpanWeightLatticeStatement — TRUE; medium.**

The span lies in the sum of the eigenspaces with eigenvalues (w b : Complex). Distinct eigenspaces of any linear endomorphism form an independent family, so a nonzero m-eigenvector in that sum forces m = w b for some b. The supplied lattice premise then applies. Repeated weights, dependent or zero spanning vectors, and empty beta cause no counterexample; empty beta has zero span and cannot contain the required nonzero vector.

Route, line 1: Put the span inside the sum of eigenspaces indexed by the distinct values of w, and use independence of eigenspaces to show m is one of those values.<br>
Route, line 2: Use injectivity of Real-to-Complex coercion to obtain m = w b and substitute the given integer lattice witness.

Lean traps: The explicit [Fintype beta] binder survives elaboration. Do not assume the spanning vectors are independent or nonzero: group equal weights before using independence of distinct eigenspaces. Use classical decidability when forming finite sets of real weights, and injectivity of the Real-to-Complex coercion when identifying m with a basis weight.

**SpinAdjointStatement — TRUE; medium.**

The fixed Pauli definitions give s_z = diag(1/2,-1/2), s_+ = [[0,1],[0,0]], and s_- = s_+*. The tokenMatrix condition is exactly the identity on every other tensor coordinate; it preserves conjugate transpose. Matrix.toEuclideanLin uses the standard Euclidean inner product. Thus the global Z is self-adjoint and Plus is adjoint to Minus, including J empty.

Route, line 1: Check the three 2x2 matrices and show tokenMatrix(A)* = tokenMatrix(A*).<br>
Route, line 2: Sum over j : J and transfer conjugate transpose to the Euclidean adjoint, yielding both inner-product identities.

Lean traps: Mathlib inner products are conjugate-linear in the first argument. Matrix.toEuclideanLin uses the orthonormal coordinate basis, and its conjugate-transpose/adjoint theorem applies. The sector pair vectors are deliberately unnormalized; no change of inner product is justified or needed.

**SpinCommutatorStatement — TRUE; medium.**

With the concrete Pauli signs, [s_z,s_+] = s_+, [s_z,s_-] = -s_-, and [s_+,s_-] = 2s_z. tokenMatrix lifts multiply correctly at a common token and commute at distinct tokens, so all off-diagonal terms in the commutators of sums cancel. The empty-token case has three zero endomorphisms.

Route, line 1: Verify the local 2x2 commutators and the same-token multiplication/distinct-token commutation rules.<br>
Route, line 2: Expand the finite double sums, cancel distinct-token terms, and transfer the remaining identities through Matrix.toEuclideanLin.

Lean traps: The order is Plus(Minus psi) minus Minus(Plus psi), so the sign is +2Z. tokenMatrix has identity factors in every other slot: keep the condition on all k different from j. Matrix multiplication and endomorphism composition must be transferred in the same order.

**WeightLadderTransferStatement — TRUE; medium.**

The supplied commutators and complex linearity give the two shifted-weight equations. The adjoint relation, its conjugate counterpart, and [Plus,Minus] = 2Z give ||Minus v||^2 - ||Plus v||^2 = 2*m*||v||^2 for a real m-eigenvector. For v nonzero its norm square is positive, which excludes Minus v = 0 when m > 0 and Plus v = 0 when m < 0. The definition of WeightLadder requires neither nonvanishing at m = 0 nor a nonzero vector for the weight-shift identities.

Route, line 1: Rearrange the first two commutators using linearity to prove the shifted eigenvector equations.<br>
Route, line 2: Take real parts of the inner-product identity from the third commutator and adjoints, then use norm-square positivity for each strict-sign nonvanishing claim.

Lean traps: WeightLadder requests the shifted-weight identities even for v = 0, and requests nonvanishing only when v is nonzero and m has the stated strict sign. Derive the reverse adjoint identity using conjugate symmetry. Take real parts before real inequalities; m is already real.

**CommonWeightEigenvectorStatement — TRUE; medium.**

Membership of mu in eigenvaluesOn S O supplies a nonzero vector in T = S intersect eigenspace(O,mu). The explicit Z-invariance of S and commutation on S make T Z-invariant. Z is Hermitian on T by restriction of the stated inner-product identity, and T inherits a finite-dimensional complex inner-product space structure from TensorSpace J. Its spectral theorem therefore gives a nonzero Z-eigenvector in T with real weight. No Hermiticity outside S, global commutation, or extra completeness premise is required; O-invariance and O-Hermiticity are harmless extra premises here.

Route, line 1: Form the nontrivial subspace T = S intersect eigenspace(O,mu) and use commutation to restrict Z to T as a symmetric linear endomorphism.<br>
Route, line 2: Choose an eigenvector from its finite-dimensional orthonormal eigenbasis, whose eigenvalues are real, and coerce it back to the ambient space.

Lean traps: eigenvaluesOn uses an ambient nonzero eigenvector, so its witness makes the restricted eigenspace nontrivial. Restrict Z to S intersect eigenspace(O,mu), not just to S, to retain the selected O-eigenvalue. Obtain the local Nontrivial instance from that witness. Finite dimension, completeness, and the inherited inner product require no additional mathematical premises.

**LadderWalkStatement — TRUE; medium.**

Write m = kappa + z with z an integer. If z > 0, apply Minus z times: each preceding weight is at least kappa+1 > 0. If z < 0, apply Plus -z times: each preceding weight is at most kappa-1, which is -1 or -1/2. WeightLadder guarantees both the shifted weights and nonvanishing at every such step. SpinStable preserves membership in S; the two stated commutation hypotheses preserve the O-eigenvalue mu. If z = 0 the initial vector suffices. Neither O-invariance of all S nor Hermiticity is needed for this leaf.

Route, line 1: Induct on the nonnegative integer distance to the target, using Minus for positive displacement and Plus for negative displacement; prove the required strict weight sign before every step.<br>
Route, line 2: At each step propagate S-membership, nonvanishing, the O-eigenvector equation, and the shifted Z-weight, terminating at kappa.

Lean traps: The target kappa and its 1/2 are real. Split the integer displacement by sign before converting its distance to a natural iteration count; avoid truncated natural subtraction. The commutation equations are available only on S, so carry membership at every step. No O-invariance premise is missing: the eigenvector equation is propagated directly.

**PositiveSpectrumStatement — TRUE; medium.**

The explicit O-invariance and Hermitian inner-product identity give a symmetric endomorphism of the finite-dimensional Hilbert subspace S. For a nonzero eigenvector, the real quadratic form equals mu.re times its positive norm square, proving the forward implication. Conversely, its orthonormal eigenbasis expresses the quadratic form as a finite sum of positive real eigenvalues times squared coordinate norms, with some nonzero coordinate for each nonzero vector. For S = bottom, PositiveOn is true and eigenvaluesOn is empty, so both sides hold as intended; this does not make the universal leaf vacuous.

Route, line 1: Restrict O to S; test strict quadratic-form positivity on each nonzero eigenvector to obtain positivity of its eigenvalue's real part.<br>
Route, line 2: For the converse expand a nonzero vector in the symmetric restriction's orthonormal eigenbasis and use a nonzero coordinate to make the weighted sum of squared norms strictly positive.

Lean traps: Restrict O using the explicit invariance premise and retain the inherited inner product. PositiveOn is strict positivity only for nonzero vectors, and eigenvaluesOn is a set of complex eigenvalues with nonzero witnesses. The comparison 0 < mu.re is in Real; Hermiticity of the restriction makes its eigenvalues real. An empty eigenbasis when S is bottom must be handled without assuming S is nontrivial.

**Verification artifacts.**

- [Inspect.lean](/home/ubuntu/aklt/reports/TS_H1M_05/scratch/Inspect.lean) imports the existing compiled statement module and uses only `#print`, `#check`, and `#synth`. Its [log](/home/ubuntu/aklt/reports/TS_H1M_05/scratch/lean-inspection.log) records successful inspection of all eight definitions and synthesis of the finite-dimensional subspace and inherited inner-product instances. A single Lean process was used; no proof or theorem was added. A symlink supplies packages from the repository; those packages were only read.
- [check_small_cases.py](/home/ubuntu/aklt/reports/TS_H1M_05/scratch/check_small_cases.py) checks both adjoint identities and all three commutators for 0–4 tokens with exact rational matrices after checking the local Pauli signs. It also checks disjoint slot assignments, every one of 4,096 abstract layouts (a superset of layouts arising from actual raw patterns), 194,481 tensor basis vectors, and 531,441 nonzero support coordinates for the weight equation and parity lattice. It checks both kappa values for displacements from -50 through 50, covering 202 walks and 5,100 steps. All assertions passed; [counts](/home/ubuntu/aklt/reports/TS_H1M_05/scratch/small-cases.json) are saved. These are finite diagnostics in support of the mathematical audit, not formal proofs of the leaves.
- The JSONL has eight unique assigned names, all required fields, valid verdicts/difficulties, and exactly two lines in each proof-route string.
