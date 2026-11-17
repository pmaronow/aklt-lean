STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Correction needed |
| --- | --- | --- | --- |
| AKLT.Blueprint.H1.DifferenceEvaluationStatementV2 | TRUE | easy | none |
| AKLT.Blueprint.H1.AffineEvaluationStatementV2 | TRUE | medium | none |
| AKLT.Blueprint.H1.RealDifferencePauliInterpolationStatementV2 | TRUE | medium | none |
| AKLT.Blueprint.H1.OperatorStructureLinearCombinationStatementV2 | TRUE | medium | none |
| AKLT.Blueprint.Top.H1FiniteDataStatementV2 | TRUE | hard | none |

All five statements are self-sufficient as mathematical propositions. The finite-data verdict uses the complete certificate bundle, exhaustive coverage testing, and matrix reconstruction. A conditional certificate soundness theorem alone would not settle that leaf. No proofs were written and the repository was not modified.

**DifferenceEvaluationStatementV2 — TRUE, easy.** The exact statement is at [NodesV2Reduction.lean:46](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Reduction.lean:46). Its immediate definitions are [reducedPolynomialReal and reducedDifferenceReal](/home/ubuntu/aklt/repo/AKLT/Defs/RealOperator.lean:53), [evaluateRealPolynomial](/home/ubuntu/aklt/repo/AKLT/Defs/RealOperator.lean:29), and [evaluateReduced](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:59).

Writing P and Q for the exact rational current and next polynomials, the left side evaluates map(P) − C(c) map(Q). Evaluation preserves subtraction and multiplication, evaluates C(c) to c, and evaluation following the coefficient map is exactly rational-to-real evaluation. The identity therefore holds even for an uncovered pattern, arbitrary real c, and vectors outside the unit ball. This is the difference identity used in [c:reduce](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:172).

Proof route:

1. Unfold the real difference and distribute evaluation over subtraction, multiplication, and constants.
2. Apply evaluation/map composition to identify the two rational-to-real evaluations.

Lean details: normalize Rat.castHom followed by real evaluation; c remains a real coefficient throughout. No real-to-rational conversion occurs. The internal construction of reducedPolynomial introduces no condition for this algebraic identity.

**AffineEvaluationStatementV2 — TRUE, medium.** The exact statement is at [NodesV2Reduction.lean:55](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Reduction.lean:55). Its premise is [VectorAffineReal](/home/ubuntu/aklt/repo/AKLT/Defs/RealOperator.lean:15), and its conclusion unfolds to [SeparatelyAffine](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:126).

The premise bounds the sum of all three exponents at each whole vector by one in every supported monomial. Each monomial is therefore constant in the updated vector or contains exactly one of its coordinates to exponent one. Its evaluation satisfies the Function.update affine identity, and finite sums preserve that identity. All real a, b and t are allowed. This matches the affineness and convex-extension argument in [c:reduce](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:172).

Proof route:

1. Expand the polynomial into supported monomials and classify their exponents at the updated vector.
2. Establish the affine evaluation identity in the constant and single-coordinate cases, then sum.

Lean details: a separate bound on each scalar-coordinate exponent would not suffice, but the actual sum bound excludes products of two different coordinates of one vector. No natural subtraction occurs in that bound. Decidable equality for Function.update on Fin 20 is available. Zero and constant polynomials give the intended identity. Neither a support nor a ball premise is missing.

**RealDifferencePauliInterpolationStatementV2 — TRUE, medium.** The exact statement is at [NodesV2Structure.lean:29](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Structure.lean:29). I traced both versions of inversion, exponent encoding, and the Pauli coefficient sum in [RealOperator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/RealOperator.lean:23) and [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:112), including the explicit [Pauli matrices](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:53).

Set α = 2 − 3c and β = 3c − 1. Then α + β = 1 and α/3 + 2β/3 = c, exactly the coefficient identities needed to interpolate P − cQ from P − Q/3 and P − 2Q/3. Embedding coefficients, substituting signs, extracting coefficients, and taking the finite Pauli sum preserve real linear combinations. The two exponent encodings agree at n = 20. This uses the real linearity described after d:Pauli and at the end of [l:Ostruct](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:320).

Proof route:

1. Establish the polynomial interpolation identity after embedding rational coefficients into the reals.
2. Apply inversion linearity and the Pauli coefficient formulas, normalizing rational/real/complex casts.

Lean details: elaboration confirms that 1/3 and 2/3 have type ℚ, while α and β have type ℝ before casting into ℂ. Negative weights are permitted; no spectral inequality is interpolated. Coveredness, groupwise inversion, vector affineness and supportedness are unnecessary for this identity because coefficient extraction remains linear even when it discards monomials. In particular I need not be contained in the active tokens. Empty token sets obey the same scalar identity.

**OperatorStructureLinearCombinationStatementV2 — TRUE, medium.** The exact statement is at [NodesV2Structure.lean:41](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Structure.lean:41), and its complete predicate is [OperatorStructureAtV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesV2Structure.lean:11). I also unfolded the fixed tensor power, pair exchange and symmetric projection in [OperatorContracts.lean](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:55), and the total-spin maps in [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:88).

Hermiticity is preserved because real scalars are fixed by complex conjugation. Entry reality is real linear. Each commutation identity with a fixed tensor power or spin/exchange map distributes over addition and scalar multiplication. The fixed-projection identity O = Π O Π is also linear in O. Matrix.toEuclideanLin is a complex-linear equivalence, so the same combination passes to the endomorphism clauses. This is the final linear-combination observation of [l:Ostruct](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:320).

Proof route:

1. Unfold the seven outer fields and move the matrix combination through Matrix.toEuclideanLin.
2. Distribute commutator and sandwich identities; use conjugation-fixed real casts for Hermiticity and reality.

Lean details: after Matrix.toEuclideanLin, multiplication is endomorphism composition. Pair tokens and projections depend only on π, r, x and the pair proof, so the same maps occur in both hypotheses and the conclusion. Preservation of the sandwich requires no extra projection premise. No sign condition on a or b is needed. The hypotheses are consistent: the zero matrix has all the structural properties for any pattern.

**H1FiniteDataStatementV2 — TRUE, hard.** The exact leaf is [Top/Operator.lean:203](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Operator.lean:203). Its witness predicate and threshold functions are [OperatorContracts.lean:110](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:110). The quantifier order requires one representation, one group inversion and one positive clearing denominator for each covered pattern, followed by a basis bijection and positive-scale lower-triangular Gram witness for every exchange-sign assignment. The certificate choices supply this order of dependence.

The complete reconstruction chain was read: [Covered, bonds and active sites](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:41); [degrees, retained sites, groups, tokens, radii and contracted polynomials](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:17); [inversion and exact Pauli entries](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:121); [group bases, central weights and integer-coordinate basis vectors](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:159); [clearing denominators, sector entries, threshold matrices and residual rows](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:218); and [explicit reindexing](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:49). I also checked their lattice, status and moment definitions.

Independent enumeration directly translated Covered and bonds without importing a historical enumerator. It found 2,048,000 option assignments, 106,101 consistent assignments, 184,914 marked assignments, and 123,339 marked north/east assignments. Keeping incident statuses and present bonds and identifying horizontal reflections gives exactly the supplied 7,962 effective keys, with no missing or extra keys. Arbitrary kept sets at tips and removed sites are irrelevant to Covered/bonds. Isolated retained spins contribute their zeroth moment one, while isolated peripheral sites are already deleted by reducedSpinSites. See [coverage results](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/coverage.json) and the [independent script](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/check_coverage.py).

The complete [H1 data bundle](/home/ubuntu/aklt/data/h1/README.md) supplies Gram factors for every sector, including those handled by Bareiss in the manuscript. The independent unbounded-integer checker passed all 12,173 blocks and 144,554 dominance rows: 8,439 use zero factors and 3,734 use nonzero factors. The smallest residual margin is 195 and the largest block dimension is 179. All 12,173 saved matrices also passed fresh reconstruction using the bundled exact constructor, including denominator scales, slot metadata, inversion choices, basis indices, symmetry and sector decoupling. Residual checking uses the saved integers; reconstruction separately rebuilds the matrices. See [Gram verification](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/gram-verification.json), [reconstruction result](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/reconstruction.json), and the [full reconstruction log](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/reconstruction.log).

The constructor formulas match the Lean definitions up to explicit token and basis bijections. Summing the central spin first gives the paper's I/J factors. Every used local moment has degree at most four and agrees with rationalStatusMoment. Tip fields and reduced corners have the same radii; retained corners have both slots. Rational Pauli entries and unnormalized symmetric/exterior basis vectors match entrywise. Hence the reconstructed matrix is the required 5q A − 3p A′. The denominator and coefficient/basis justification is precisely [l:integercheck](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:582).

Proof route:

1. Exhaustively cover effective records, remove isolated zeroth-moment factors, and transport each chosen representation/inversion/clearing denominator through the token bijection and reflection.
2. Reconstruct every indexed central-sector matrix and provide its checked lower-triangular Gram witness for each exchange sign, reusing witnesses for irrelevant signs.

Lean details and boundary cases:

- ExchangeSigns assigns a Boolean to every group, including singles and U-pairs. Unused signs repeat sectors. The explicit index bijection must transport the archive's ring order to CentralBasis.
- ClearsDenominator includes 0 < D₀. Its integrality condition justifies replacing the floors in integerSectorMatrix by exact entries. No zero denominator is allowed. If D₀ is multiplied by k > 0, the matrix scales by k; multiplying g by k preserves the residual inequalities.
- The symmetric middle vector is ud+du and the exterior vector is ud−du. Normalizing these vectors would change the archived integer matrices. The rational-complex product fold is harmless: it multiplies the same commuting Pauli entries regardless of the Finset.toList order.
- Zero active tokens give one function to Fin 2, hence a one-dimensional tensor and scalar central sector. Seven archive records have this case, with matrices [195] for turns or [585] for straight patterns, equal to 15(q−p). Their row conditions pass. See [empty tensor cases](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/empty-tensors.json).
- Fin t ≃ CentralBasis prevents choosing t = 0 for a nonempty sector. An empty archived L triangle denotes a zero factor of the actual block size. Positive g, d and S are still required. No zero-scale or empty-sector loophole is used.
- groupSecond's min-based totalization causes no collision on actual pairs: corners have token pairs (0,1), (2,3), (4,5), (6,7); the tip leaders are 8, 11, 14, 17. The threshold functions correctly distinguish north (961/1000) from east/west (187/200).

The manuscript marks the finite checks pending in [sec8-inputs.tex](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:25). These are proof implementation obligations, not contradictory hypotheses or missing mathematical premises. In particular p:certificate alone does not supply witnesses. The complete bundle and the checks above support the truth verdict; they are computational verification plus definition inspection, not newly written kernel proofs.

**Common Lean audit.** A single scratch module imported the existing compiled statements and printed their elaborated types. All five are closed Prop declarations with no dropped mathematical instance assumptions. It confirms the rational divisions in interpolation and the finite-data quantifiers. See [inspection source](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/lean/Inspect.lean) and [elaborated output](/home/ubuntu/aklt/reports/TS2_H1M_02/evidence/lean-inspection.log). Finsets supply actual subtype indices and finite sums. Classical decidability/Fintype choices in the noncomputable definitions add no mathematical hypotheses. No vacuous, false or under-premised leaf was found.
