STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty | Assessment |
| --- | --- | --- | --- | --- |
| [PartLawBridgeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:16) | `l:finitefacts` | **TRUE** | medium | The stated positive normalizer suffices. |
| [EnumerationStepsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:26) | `l:removal` | **TRUE** | easy | Injective prefixes give valid removal steps. |
| [SurvivorGeometryStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:36) | `l:removal` | **TRUE** | medium | Four compass neighbours have the claimed geometry. |
| [RemovalIntegralStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:45) | `e:removalpolynomial` | **TRUE** | hard | The supplied tensors integrate the removed site. |
| [NeighbourFibresStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:53) | `l:removal` | **TRUE** | hard | Positive fibres are products of three-factor laws. |
| [PairMeanAveragingStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:60) | `l:removal` | **TRUE** | medium | Conditional pair bounds average over finite fibres. |
| [QuarticMeanBoundStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:67) | `l:removal` | **TRUE** | easy | Unit or zero support bounds each quartic product. |
| [PolynomialLowerStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:73) | `l:removal` | **TRUE** | easy | Both constants follow from the supplied expectations. |

All eight names have namespace `AKLT.Blueprint.Win` and module `AKLT.Blueprint.Win.NodesRemoval`. All eight statements are true and self-sufficient as written. No corrected statements or additional premises are needed. No leaf was classified as under-premised, false, vacuous, or unsure.

Reviewed the exact source on branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, against the paper’s [removal argument](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:233), [finite-facts lemma](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126), [moment lemma](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35), and [three-factor lemma](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197). The repository was read only. No proofs or sub-agents were created.

**Definition trace.** The following concrete definitions were read, including the definitions inside the two assumed Top statements. Standard Lean/Mathlib operations are used with their usual meanings.

- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): `Plane = ℤ × ℤ`; `latticeDist`, `Adjacent`; `Compass` and its finite instance, `Compass.step`, `neighbours`; `positiveNeighbours`, `internalBonds`, `originalLegs`; `setDistance`, `boundaryDepth`, `protectedSites`. Thus depth and protection always refer to the original finite volume, and bonds are indexed once.
- [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9): `Vec3`, `dot`, `normSq`, `UnitVector`; `goldenRatio`, `icoRadius`, `IcoLetter`, `signValue`, `icoVector`, `moment`; `Status`, `SpinLetter`, `spinVector`, `spinWeight`, `siteFunctional`; `SeparateDegreeFour`, `productFunctional`. U has twelve labels of weight `1/12` and a zero atom of weight zero; D has twelve weights `1/20` and zero-atom weight `2/5`.
- [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:70): `rationalMoment`, `rationalStatusMoment`. The degree-at-most-four cases agree with the second/fourth tensors, and the positive-degree D moments have the stipulated factor `3/5`.
- [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9): `Weight`, `normalize`, `Probability`, `expectation`. These are explicit finite real sums. `Probability` includes nonnegative atoms and mass one; it does not require every atom to be positive.
- [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9): `PinAssignment`, `extendIcoSpins`, `pinnedSum`, `freeSum`. Each original leg has its own unit pin. Removed sites get no new pins. Extension off the current configuration volume is exactly zero.
- [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:19): `PlaneConfiguration W` is the finite function type `↥W → IcoLetter`; the use of this abbreviation here introduces no rotated frame vectors.
- [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:47): `eventMass`, `localProduct`, `localMean`. The last two give the one-site product law used by the three-factor premise.
- [Top/Common.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Common.lean:13): every conjunct of `MomentsStatement` and [ThreeFactorMeanStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Common.lean:52), including the rational monomial and degree-limited product covariance clauses of the former and the range equality of the latter. These agree with the cited paper statements; there is no contradictory premise identified here.
- [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:72): `pairSum`, `quartic`, `removalPolynomial`, `partSum`, `partMean`; [RemovalEnumeration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:146), `removedPrefix`, `RemovalStep`, `survivors`; `partWeight`, `partLaw`, `restEvent`, `fibreMean`, `fibreSpinMean`, `NeighbourControl`. All hypotheses in these data definitions were included in the assessments.

**Shared Lean traps.** The declaration inspection confirms that all eight declarations have type exactly `Prop`, with no extra instance binders silently generalizing or weakening them. The finite sums are over the `Fintype` of configurations on the subtype of a `Finset`, never over the infinite plane. The relevant finite instances are supplied by the finite site subtype and the twelve-letter alphabet. The definitions using arbitrary event predicates and protected-depth filters employ classical decidability internally; writers may need `classical` when unfolding them. There is no missing decidability hypothesis.

`Vec3` is a function type: its inherited norm is a supremum norm, whereas the intended Euclidean quantity is `normSq = dot a a`. Use the explicit coordinate sum or `EuclideanSpace` when applying Cauchy–Schwarz. `boundaryDepth` takes values in `ℕ∞`; the comparisons with 2 and 3 occur there. None of these eight leaves uses the potentially delicate `depthShift` natural subtraction or an `ENat.toNat` conversion. The fractions in the eight conclusions and their expectations are real fractions; the only rational-to-real conversion relevant to the assumed moment statement is the explicit cast of `rationalStatusMoment`.

There are valid removal steps, for example the origin in `[-3,3]²` with no prior removals, and valid singleton enumerations. `RemovalEnumeration ∅` has no inhabitant because its domain is `Fin (last + 1)` and its image must be the enumerated set. This is the paper’s intended nonempty enumeration convention, not an accidental vacuity of the leaf. Empty configuration volumes still have their one empty configuration.

**PartLawBridgeStatement: TRUE; medium.** MomentsStatement supplies unit icoVector atoms and PinAssignment supplies unit pins, so every factor in partWeight is nonnegative. Its finite sum equals partSum applied to 1 in either Bool branch. The explicit positive-normalizer premise makes normalize a probability, and pulling the common denominator through the finite sum gives the claimed equality for arbitrary f. Arbitrary Y and an empty surviving volume cause no problem.

Lean traps: split pinned explicitly; its occurrence in partWeight is coerced to a proposition inside a conjunction. PlaneConfiguration (G \ Y) is definitionally the function type summed by pinnedSum/freeSum. All scalar divisions here are in R, and zero atoms are allowed by Probability.

Proof route (two lines):  
Identify partSum f with the sum of partWeight times f after commuting scalar factors; use the unit-support bounds to show partWeight is nonnegative.  
Use the supplied positive total mass to normalize, then distribute division over the finite sum to identify expectation with partMean.

**EnumerationStepsStatement: TRUE; easy.** The prefix is the image of indices whose values are less than j. At j+1 precisely index j is added, and injectivity prevents its site from already being in the prefix. image_eq and X subset G give membership; depth at least 3 excludes every enumerated site from the original protected layer, defined by depth at most 2. The previous field supplies the predecessor neighbour. RemovalEnumeration intentionally enumerates a nonempty set, matching p >= 1 in the paper.

Lean traps: last is the final index, so the domain has last+1 elements; distinguish j.val from a Fin index. The empty-X case has no RemovalEnumeration and is intentionally excluded by this data type. Depth comparisons take place in ENat, not Nat.

Proof route (two lines):  
Unfold removedPrefix and use image membership plus injectivity to compute the empty/full prefixes and insertion update.  
Use image_eq, X subset G, the depth assumption, and e.previous to establish RemovalStep and predecessor adjacency at every index.

**SurvivorGeometryStatement: TRUE; medium.** Depth at least 3 forces all four original compass neighbours of x into G and gives each neighbour original depth at least 2. survivors is a subset of these four distinct sites. It is all four when Y is empty, and a neighbouring site in Y excludes at least one. Any two distinct compass neighbours have ambient latticeDist 2. No convexity or connectedness of G is needed.

Lean traps: boundaryDepth is an ENat infimum over the original exterior; reason with exterior witnesses or the triangle inequality before converting any values to Nat. The definition of survivors excludes x and Y, and compass-image injectivity must be justified to count four neighbours. The comment mentions the surviving-degree bound, but that bound is not an extra conjunct of this leaf and follows directly from the same geometry.

Proof route (two lines):  
Use distance-to-exterior inequalities to put every compass neighbour in G with depth at least 2; enumerate the four offsets for cardinality and pairwise distance.  
Intersect with G \ insert x Y; an empty Y keeps all four, and a neighbour in Y removes one of the four.

**RemovalIntegralStatement: TRUE; hard.** RemovalStep puts x in the current volume at original depth at least 3, so x has no original leg and at most four surviving bond factors. Reindexing configurations separates the x letter from the after-removal configuration. The supplied first/third tensors vanish; the second tensor gives the unordered pair sum divided by 3; the fourth tensor gives the three compass-neighbour pairings divided by 15. If there are four survivors, they are exactly all four compass neighbours. Every other bond and original-leg factor is unchanged.

Lean traps: internalBonds indexes each undirected bond once using only east/north orientations, so use symmetry of dot for incoming factors. pairSum is half of an ordered off-diagonal sum. Reindex the dependent configuration function types and account for the single factor 1/12. Keep the original G in originalLegs; the quartic branch is used only when survivors has cardinality four. No partition-sum positivity or ExactStatement is required.

Proof route (two lines):  
Split the configuration sum into the x letter and all remaining letters, factor off all interactions not incident to x, and match the after-removal site prefactor and original legs.  
Expand the at-most-four incident factors and apply the supplied moment tensors, identifying pairSum and, only for four survivors, quartic.

**NeighbourFibresStatement: TRUE; hard.** Each survivor z lies in the after-removal volume, has original depth at least 2 and hence no original leg, and has at most three present bonds because x has been removed. Distinct survivors are not adjacent. On a fixed restEvent fibre, all outside factors are constant and the remaining weight is a product of one-site U weights with at most three unit fields each. MomentsStatement supplies unit support; ThreeFactorMeanStatement supplies positive local normalizers and the squared mean bound. Positive fibre mass permits cancellation of its constant and the global normalizer, giving the required dot-product factorization. No unsupplied FiniteFactsStatement or global-positivity leaf is needed.

Lean traps: NeighbourControl does not itself assert Probability, and quantifies only over positive-mass fibres. If the global normalizer were zero, normalize would be identically zero and no such fibre could exist; on a positive fibre the cancellation is justified. Establish the surviving-degree bound directly from the compass geometry, since it is mentioned only in SurvivorGeometryStatement's comment. Convert siteFunctional .U from SpinLetter to its twelve IcoLetter atoms; the none atom has zero weight.

Proof route (two lines):  
On each positive restEvent fibre, reindex the independent survivor letters and factor the conditional weight into its constant outside factor and at-most-three-factor U laws.  
Cancel their positive normalizers, apply ThreeFactorMeanStatement to each site, and factor the two-site dot expectation coordinatewise.

**PairMeanAveragingStatement: TRUE; medium.** NeighbourControl supplies normSq(m_z) <= 9/25 and factorizes every distinct pair's conditional dot mean on each positive restEvent fibre. The Gram-sum identity makes conditional pairSum at least minus one half of the sum of squared means, hence at least -(9/50)*card V, with no upper bound on card V needed. Rest-event fibres partition the finite configuration space; nonnegativity of p makes every zero-mass fibre contribute zero. The finite conditional-expectation averaging identity gives the conclusion, including V empty.

Lean traps: average over the partition into restEvent equivalence classes, or prove the weighted finite tower identity; summing fibre means unweighted over all configurations would repeat fibres and use the wrong weights. Only cancel strictly positive eventMass. Vec3 is a Pi type whose ordinary norm is a supremum norm, so use the explicit Euclidean normSq/dot sums. The pairSum factor 1/2 removes double counting; do not include diagonal terms.

Proof route (two lines):  
For each positive fibre, use the supplied pair factorization and 2*pairSum(m) = normSq(sum m) - sum normSq(m) to obtain the cardinality bound.  
Apply finite averaging over the rest-event partition, using Probability to discard zero-mass fibres and to normalize the constant lower bound.

**QuarticMeanBoundStatement: TRUE; easy.** MomentsStatement makes each icoVector unit; extendIcoSpins is zero off D, so every vector used in quartic has normSq at most 1 even when some of the four neighbour sites are absent. Each dot product has absolute value at most 1 and each of the three products has absolute value at most 1. A nonnegative probability average therefore has absolute value at most 3. No membership condition on x or its neighbours is missing, and the empty-volume value is zero.

Lean traps: use Cauchy-Schwarz for the explicit dot sum, or pass through EuclideanSpace; the inherited Pi norm on Vec3 is not the Euclidean norm. Split the membership test in extendIcoSpins. No independence or degree-four quadrature is needed; an absent neighbour makes every quartic summand zero.

Proof route (two lines):  
Obtain normSq <= 1 for each extended spin and use finite-dimensional Cauchy-Schwarz to bound the three quartic products pointwise.  
Bound absolute expectation by expectation of the absolute value and use Probability's nonnegativity and total mass one.

**PolynomialLowerStatement: TRUE; easy.** Expectation of the constant 1 is 1 by Probability, and linearity expands removalPolynomial. If card V is 4, the two supplied moment bounds give 1 - (9/50)*4/3 - 3/15 = 14/25. Otherwise card V <= 4 implies card V <= 3, the quartic term is absent, and the lower bound is 1 - (9/50)*3/3 = 41/50. The pair and quartic bounds are explicit hypotheses, so no relation between V, x and D is required.

Lean traps: split the Nat equality V.card = 4 before simplifying the conditional; the other branch needs the Nat bound V.card <= 3 and its cast to R. All divisions and constants in this statement are real, not Nat divisions. No subset or geometric premise needs to be added.

Proof route (two lines):  
Expand the expectation by finite-sum linearity and Probability, then split on V.card = 4.  
In the four-site branch substitute the pair bound and quartic lower bound -3; in the other branch use card V <= 3 and simplify the rational constants.

**Validation.** [StatementInspection.lean](/home/ubuntu/aklt/reports/TS_WIN_07/StatementInspection.lean) imported only the single requested leaf module and printed the declarations and their elaborated types, with `pp.explicit` inspection of the polynomial, normalized law, and prefix. It contains no proofs or new axioms. Lean `4.35.0-rc2` completed successfully using the repository’s existing compiled imports and a local symlink to its packages. Only one Lean process was used. The [inspection log](/home/ubuntu/aklt/reports/TS_WIN_07/statement-inspection.log) records the result.

The standard-library-only [check_sweep.py](/home/ubuntu/aklt/reports/TS_WIN_07/check_sweep.py) passed all supplementary checks; [check-sweep-results.json](/home/ubuntu/aklt/reports/TS_WIN_07/check-sweep-results.json) records the results:

- Exact arithmetic in `ℚ(√5)` checked twelve distinct antipodal unit atoms and all 35 monomials of total degree at most four.
- Exact removed-site averages agreed with the pair/quartic polynomial for all sixteen subsets of four specified rational fields, covering survivor counts zero through four. This checks the local integration identity; configuration reindexing and preservation of the original-leg factors were checked from the source definitions.
- All 256 allowed prior-removal subsets away from the origin among the depth-at-least-three sites of `[-3,3]²` satisfied the survivor claims, absence of original legs, and the bound of three remaining incident bonds.
- All `12^4 = 20,736` assignments of support letters to the four quartic sites satisfied the absolute bound; the maximum observed value was 3. This check used floating-point arithmetic. Absent-neighbour and empty-volume cases were checked from the zero-extension definition.
- Product-fibre models for zero through four sites, two positive outer masses and one zero outer mass verified conditional pair factorization, squared means at most `9/25`, and the pair-average lower bound to floating-point tolerance. The two-site and four-site models attain the lower bound within that tolerance.
- Exact rational arithmetic checked all five cardinalities in `PolynomialLowerStatement`: the derived bounds are `1`, `47/50`, `22/25`, `41/50`, and `14/25`. The last two are exactly the two advertised worst-case constants.

These are declaration and small-case checks, not formal proofs of the leaves. The verdicts rest on the source-level mathematical review and the proof routes above. The two hard leaves owe their difficulty to reindexing finite configuration sums and factorizing conditional weights; no unresolved mathematical assumption remains.

The machine-readable deliverable is [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_WIN_07/verdicts.jsonl), with exactly one object per requested leaf and a two-line route in every record.
