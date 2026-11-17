STATUS: COMPLETE

All eight leaves are **TRUE as written and self-sufficient**. No missing premise, counterexample, or unintended vacuity was found. No statement correction is required. Difficulties estimate Lean formalization work, including finite reindexing and subtype bookkeeping.

| Leaf | Verdict | Difficulty | Main finding |
| --- | --- | --- | --- |
| `AKLT.Blueprint.H1.PeripheralGeometryStatement` | TRUE | medium | Deleted sites are nonadjacent peripheral leaves; every unique bonded neighbour is retained. |
| `AKLT.Blueprint.H1.PeripheralFubiniStatement` | TRUE | hard | The finite assignment split accounts for every bond, slot, and status change. |
| `AKLT.Blueprint.H1.PeripheralAssignmentStatement` | TRUE | hard | Its premises supply one common positive factor and one common ball assignment for both values of `next`. |
| `AKLT.Blueprint.H1.BallChordStatement` | TRUE | medium | Normalize nonzero vectors using the explicit Euclidean squared norm; handle zero separately. |
| `AKLT.Blueprint.H1.AffineEvaluationStatement` | TRUE | medium | The exponent bound allows at most one coordinate from each entire vector. |
| `AKLT.Blueprint.H1.ProductBallNonnegativeStatement` | TRUE | medium | Twenty successive convex chords transfer nonnegativity from unit assignments. |
| `AKLT.Blueprint.H1.DifferenceStructureStatement` | TRUE | easy | Support inclusion and evaluation preserve all three predicates for any rational scalar. |
| `AKLT.Blueprint.H1.SectorSpinStableStatement` | TRUE | hard | Disjoint token blocks and the local spin-action tables suffice without coveredness. |

**Sources and scope.** Inspected repository revision `7a3393531c12080d76aefbdab300ac0c2df834b7`. The exact leaves are in [NodesReduction.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesReduction.lean:27) and [NodesSector.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesSector.lean:12). The paper comparison uses [Appendix D, leaf reductions and `c:reduce`](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:93), [the exchange-sector action tables and `l:sector`](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:417), and [the concrete finite moment laws](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8). The sector leaf's own docstring points to `d:exchange`; its supplied label `l:sector` is the subsequent application of this stability fact.

The definition trace covered `templateSites` through `square`, `latticeDist`, and `Plane`; tips, corners, slots, compass steps, neighbours and oriented `internalBonds`; all relevant `PatternData` fields, `statusAt`, `keptAt`, `Covered`, `bonds`, `active`, `spins`, and pattern functionals. It also covered `patternDegree`, `SingleReplacement`, retained/deleted sites, all group/token functions, radii, `leafNeighbour`, `formalDot`, and `reducedIntegrand`; the local/raw/separated evaluations, `LeafRule`, `PeripheralGeometry`, `UnitChord`, and `SeparatelyAffine`; polynomial evaluation and structural predicates; and the exchange basis, its integer coordinate formula, ambient span, Pauli matrices, token lifts, and three total-spin maps. The spin-law trace includes `SpinLetter`, `spinVector`, `spinWeight`, `siteFunctional`, the explicit icosahedron coordinates, golden ratio, and radius. These definitions are in [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8), [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8), [Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:9), [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:10), [OperatorContracts.lean](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:9), [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:59), [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:53), and [H1/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:14).

**PeripheralGeometryStatement — TRUE.** The retained-site filter removes only active tips and selected corners. A tip has only one possible template neighbour. A corner has at most two; in the unreduced representation a deleted corner has degree zero, and in the reduced representation it has degree zero or one. Every peripheral neighbour lies in the inner cross, where active sites are retained. All eight peripheral sites have even coordinate-sum parity, so none are nearest neighbours of another.

Route, line 1: Enumerate the thirteen template sites and peripheral bond endpoints, then specialize the retained-site filter to each representation.  
Route, line 2: Identify the unique incident bond when the degree is one; use the inner-cross retention and peripheral parity conclusions.

Lean traps: `patternDegree` counts present internal bonds, not kept directions or slot factors. Bonds have one positive orientation and no loops, so an incident bond contributes exactly once. `leafNeighbour` uses `toList.filterMap.headD`; degree one must establish that the filtered list has exactly one entry before its default `(0,0)` can be discarded. The covering-tip exception in `PatternData.bonds` must be preserved.

**PeripheralFubiniStatement — TRUE.** The active sites split into retained sites and deleted leaves. Peripheral geometry prevents any bond between deleted sites and leaves at most one bond from each deleted site to a retained spin. The original slots at a deleted site give exactly `coveredSiteField`; the remaining slots give `retainedOriginalFactors`. The passage site is retained. The potentially omitted outgoing bond also has retained endpoints, so its change is fully represented in the retained factors. Deleted-site laws are identical for current and next.

Route, line 1: Reindex assignments on the disjoint retained/deleted union and classify every original bond and external slot.  
Route, line 2: Exchange and factor the finite sums over deleted coordinates to obtain the product of `integratedLeafFactor` terms.

Lean traps: A `Finset` such as `V` is coerced to its finite subtype in `V → SpinLetter` and `∏ x : V`; reindex both the functions and the products. Track equality between `PatternData.spins` and `supportSpins` after reindexing. The dot product is written in both orders and needs symmetry. Retained slots need no extra status check because retained sites belong to `active`. No moment or probability-normalization premise is needed for this finite algebraic split.

**PeripheralAssignmentStatement — TRUE.** For each deleted isolated site, `LeafRule` supplies a positive slot normalizer; for each deleted degree-one site, it supplies a positive normalizer and one replacement vector. These choices depend on the leaf and original pins, and can be made before quantifying `next`. Their product is `K`. Retained corner slots are copied to their original token indices; each single replacement occupies its leader token; unused coordinates are zero. The explicit icosahedron unit-norm premise ensures that every possible retained neighbour spin is in the ball required by `LeafRule`, including `SpinLetter.none`, whose spin is zero.

Route, line 1: Choose all local normalizers and replacements and assemble the global assignment using the disjoint group-token blocks.  
Route, line 2: Apply the leaf identities at retained neighbour spins, identify evaluation of `reducedIntegrand`, and extract the same positive product `K` for both values of `next`.

Lean traps: Preserve the order `∃ K, ∃ u, ∀ next`; two independent current/next choices do not suffice. Match the two retained corner indices against `externalSlot`, and use the fact that groups have positive degree. `replacementRadius` lies in `ℚ`, so its cast in real evaluation must match the radius in `LeafRule`. All twenty norm bounds are required, including unused indices. Empty products are one; positivity of `K` follows from the local positivity hypotheses. The supplied `LeafRule` and unit-norm premise are sufficient; this leaf does not need an additional moment-evaluation theorem.

**BallChordStatement — TRUE.** For nonzero `v`, let `r = sqrt (normSq v)`, choose the unit endpoints `v/r` and `-v/r`, and use weight `(1+r)/2`. Nonnegativity of the sum of squares and its zero characterization give `0 < r ≤ 1`. At zero, opposite coordinate unit vectors and weight `1/2` give the required chord. Thus division by zero is avoidable within the stated hypotheses.

Route, line 1: Establish the sum-of-squares properties of `normSq` and construct the zero-vector chord separately.  
Route, line 2: Normalize the nonzero vector by its positive square root and check the unit, weight-bound, and pointwise combination identities.

Lean traps: `Vec3` is `Fin 3 → ℝ`; its usual Pi norm is the maximum coordinate norm. It is not the square root of this `normSq`. Use the explicit sum of squares, or transport through `EuclideanSpace ℝ (Fin 3)`. Scalar multiplication and equality of vectors are pointwise. The zero branch must precede normalization.

**AffineEvaluationStatement — TRUE.** At a fixed token, the sum of its three natural exponents is at most one. Each supported monomial therefore uses no coordinate of that token, or exactly one coordinate to the first power. Its evaluation has the affine update identity, and the finite linear combination of monomials has the same identity for every real weight.

Route, line 1: Expand evaluation over polynomial support and classify each token's exponent triple using the bound on its sum.  
Route, line 2: Verify the affine update identity for these constant or linear terms and sum with the real-cast rational coefficients.

Lean traps: Bounding each scalar-coordinate exponent by one would be insufficient; `VectorAffine` correctly bounds their sum. `SeparatelyAffine` quantifies over every `t : ℝ`, not only convex weights. The coefficient map is `Rat.castHom ℝ`, and `Function.update` replaces an entire vector at one token.

**ProductBallNonnegativeStatement — TRUE.** Choose a chord for one ball coordinate and apply separate affineness. The resulting value is a convex combination of two values whose selected coordinate is unit. Iterating through the finite twenty-coordinate domain reaches only unit assignments. Nonnegative coefficients preserve nonnegativity, even when a coefficient is zero. There is no need for continuity, minima, or compactness.

Route, line 1: Induct over the coordinates still to be replaced and select a chord for the next ball vector.  
Route, line 2: Apply the affine identity and the two inductive nonnegativity conclusions with `t ≥ 0` and `1-t ≥ 0`.

Lean traps: The induction is on `Fin 20` or its finite universal set, not only `reductionVectors`. The unit-assignment hypothesis also quantifies all twenty entries. Retain the norm bounds for untouched entries when applying the induction hypothesis. Do not divide by either convex weight or assume the two chord endpoints are distinct.

**DifferenceStructureStatement — TRUE.** Multiplication by a constant adds no variable exponent, and subtraction has support contained in the union of the two input supports. Hence vector affineness and support outside `J` are preserved. Evaluation respects subtraction and multiplication by the real cast of the rational scalar, so the two invariance hypotheses yield invariance of the difference. No sign condition on `c` is needed.

Route, line 1: Use support inclusion for subtraction and constant multiplication to transfer the degree and outside-`J` exponent conditions.  
Route, line 2: Expand evaluation of the difference and apply the two orthogonal-invariance identities with the same cast scalar.

Lean traps: Support inclusion is sufficient; support equality fails under cancellation and at `c=0`. The rings are rational polynomials and real evaluations, linked by the rational cast. `J=∅`, zero polynomials, and arbitrary negative or zero `c` all satisfy the same argument.

**SectorSpinStableStatement — TRUE.** Each group is one of the eight listed peripheral sites. The possible corner token blocks are `{0,1}`, `{2,3}`, `{4,5}`, and `{6,7}`, with singles using only the first entry; tip blocks are `{8}`, `{11}`, `{14}`, and `{17}`. They are disjoint for every `PatternData`. The integer-coordinate product vectors are exactly the local single, symmetric-pair, or exterior-pair vectors. The Pauli convention in `Frame.lean` gives the paper's action tables; the sum of these local actions preserves their product span. No geometric coveredness condition is needed.

Route, line 1: Check the group-token allocation and the explicit local `Z`, raising, and lowering action tables for all three group types.  
Route, line 2: Express each total-spin image of a generating `sectorVector` as a finite combination of generators, then extend preservation to `exchangeSpace` by span induction.

Lean traps: The symmetric vector `e₀⊗e₁ + e₁⊗e₀` is unnormalized, so the nonzero pair ladder coefficients are `1` and `2`. Both ladders kill the exterior vector, selected exactly for a D pair with sign `false`. `ExchangeSigns` is defined on all groups; unused signs have no effect. Cast integer coordinates into `ℂ` and account for `WithLp.toLp 2` and `Matrix.toEuclideanLin`. Dependent `GroupBasis` indices have sizes one, two, or three, never zero. With no groups, the configuration type `(∅ → Fin 2)` is a singleton: the tensor space is `ℂ`, its generating empty product is one, and all three spin maps are zero. This is the intended empty-tensor case.

**Finiteness, decidability, and nonvacuity.** Lean inspection confirmed all eight declarations are closed propositions, with no silently dropped section variable or instance premise. Finset-subtype and dependent-function `Fintype` instances supply the finite sums in these definitions. A writer can use `classical` for the noncomputable filters and finite choice; no new mathematical premise follows from doing so. None of these leaves contains problematic natural-number subtraction. Real division occurs only in the proposed chord construction and can be guarded by the nonzero branch.

Covered patterns exist: take outgoing east, passage U with kept directions east/north/west, remove the south neighbour, and assign U with all four kept directions to every other non-tip site; tips are U with arbitrary kept sets. The explicit unit-vector premise is true by the paper's icosahedron calculation, and `LeafRule` is the paper's leaf identity. Thus the conditional leaves are not true only through impossible premises. Empty support or empty groups are valid special cases rather than a source of unintended vacuity.

**Validation.** [inspect_statements.lean](/home/ubuntu/aklt/reports/TS_H1M_04/inspect_statements.lean) imported only the two target modules against the existing read-only compiled dependencies. It printed all eight elaborated declarations, the relevant predicates and types, and `Pi.norm_def`; the run exited successfully. Its [log](/home/ubuntu/aklt/reports/TS_H1M_04/inspect_statements.log) confirms the quantifier order and norm distinction. One Lean process was used; no leaf proofs were written.

The dependency-free [audit_checks.py](/home/ubuntu/aklt/reports/TS_H1M_04/audit_checks.py) independently checked:

- 131,072 combinations of all subsets of the sixteen template bonds and both representations, with all sites active. This tests a larger graph family than covered patterns; deleting additional isolated inactive vertices cannot affect the geometry conclusion.
- All 1,296 absent/single/pair token allocations for the four corners and four tips, verifying disjointness.
- The single-spin and symmetric/exterior pair action tables using exact rational arithmetic.
- 96 covered fixture/representation/pin/current-next cases, retaining all thirteen spin letters. The fixtures include U and D corners, retained D pairs, replaced D leaves, isolated U tips and D corners, removed sites, all three allowed outgoing directions, and U/D retained neighbours. Pins include equal, alternating antipodal, and deterministic varied unit vectors. The original, separated, and reconstructed finite sums agree, using one `K` and one `u` for both current and next; the largest relative discrepancy is `1.56e-15`.

The [check log](/home/ubuntu/aklt/reports/TS_H1M_04/audit_checks.log) records the results. The floating-point functional comparisons are diagnostic evidence; the verdicts rely on the definition analysis and paper routes above. The repository was not modified. All deliverables and scratch files are under this working directory; package and toolchain links point to the read-only repository.
