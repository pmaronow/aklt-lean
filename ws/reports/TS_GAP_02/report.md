STATUS: COMPLETE

| Leaf (`AKLT.Blueprint.Gap.` prefix) | Paper label | Verdict | Difficulty | Assessment |
| --- | --- | --- | --- | --- |
| `SurgeryPreservationStatement` | `l:surgery` | TRUE | medium | Conditional resampling preserves both marginals, even for pair-dependent rows. |
| `ConditionalPatchCouplingStatement` | `l:stopped` | TRUE | hard | The assignment hypotheses give the stated conditional success probability. |
| `FrameProductReferenceStatement` | `l:density` | TRUE | medium | All boundary factors can be absorbed into positive one-site weights. |
| `FrameInteractionBoundsStatement` | `l:density` | TRUE | easy | Multiply the bounds over precisely the internal bonds. |
| `NormalizedInteractionStatement` | `l:density` | TRUE | easy | The supplied positive partition sum normalizes the weight and preserves its bounds. |
| `SignedFrameBlockStatement` | `l:density` | TRUE | hard | Variational comparison loses one density ratio, giving `frameRatio^E.card`. |
| `VariationalCenteringStatement` | `l:density` | TRUE | medium | Constant and conditional complex means minimize their squared errors. |
| `ProductTensorizationStatement` | `l:density` | TRUE | hard | Commuting coordinate averages give the product Poincare bound with constant one. |

All eight statements are self-sufficient as mathematical obligations. No missing premise, counterexample, or unintended vacuity was found; no correction is needed. Empty products and singleton configuration spaces are explicitly intended by the paper. Difficulty estimates concern formalization from the closed statement, including the finite probability facts a writer may need to establish.

Audited on 2026-11-16 against repository `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The exact statements are in [NodesFinite.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:81). The repository remained clean and was not modified. The machine-readable records are in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_GAP_02/verdicts.jsonl).

The definition trace covered the following project vocabulary, through its concrete finite sums and products:

- [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:14): `Config`, `restrict`, `AgreeOn`, `fibre`, `disagreement`, and `AssignmentBound`; `planeInteraction` is defined in `NodesFinite.lean` itself.
- [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:8): `Weight`, `normalize`, `PositiveProbability`, `Probability`, `expectation`, `totalVariation`, `complexMean`, `variance`, `AgreeOutside`, `conditionalExpectation`, `blockDirichlet`, `dirichlet`, `PoincareLower`, and all fields of `Coupling`. [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:35) supplies `conditionalProbability` and `conditionOn`.
- [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:9): `ProperPlaneColouring`, `PlaneConfiguration`, `exteriorSites`, `FrameBoundary`, both extension functions, `planeWeight`, `planeLaw`, and `marginal`.
- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): `Plane`, `latticeDist`, `Adjacent`, `Compass` and its steps, `neighbours`, `positiveNeighbours`, `internalBonds`, and `originalLegs`.
- [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8) and [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:32): `Vec3`, `dot`, `IcoLetter`, `signValue`, `goldenRatio`, `icoRadius`, `icoVector`, `frameRotation`, `frameVector`, `frameBound`, and `frameRatio`.

**SurgeryPreservationStatement — TRUE.** The full-state conditional law is supported on the input's exterior-agreement class. Every class denominator is positive because it contains the input configuration, which has positive mass. Each row's first marginal depends only on the first input, and its second marginal only on the second input; unrestricted dependence of the joint row on both inputs therefore causes no problem. Empty and full resampling sets are valid. This is exactly the operation in [the surgery lemma](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:132).

Route: Define the output mass by the displayed mixture; its entries are nonnegative.  
Reorder finite sums, apply the two row and input marginals, and use stationarity of exterior-fibre conditioning.

**ConditionalPatchCouplingStatement — TRUE.** In `AssignmentBound`, take `U=A` and `J=Finset.univ \\ A`. This supplies the lower bound for a fixed assignment on `A` given its entire complement. A fixed full configuration exists by the nonempty alphabet hypotheses. Completing a maximal coupling on `B` and then independently resampling `A` in both components preserves both full laws. Disjointness keeps the agreeing `B` coordinates fixed; hitting the chosen assignment twice has conditional probability at least `α^(2*A.card)`. No range, consistency, or plane geometry premise is required for this isolated quantitative step. The paper uses exactly this construction in [the stopped-coupling argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:125).

Route: Maximally couple the `B` marginals, complete to a full-law coupling, and independently resample the two `A` fibres.  
Apply the assignment bounds conditional on both inputs and sum over agreeing `B` inputs to obtain success at least `t*α^(2*A.card)`.

**FrameProductReferenceStatement — TRUE.** For each site, its weight is `1/12` times all crossing-bond factors incident to that site. Membership in `originalLegs W` guarantees an interior endpoint and an exterior nearest neighbour. Proper colouring thus makes the explicit unequal-frame positivity premise apply to every boundary factor; it applies to internal factors too. Normalize each site weight separately and cancel their positive normalizers from `planeLaw`. Shared exterior neighbours introduce no extra interaction: their letters are fixed. For empty `W`, the product configuration is unique and `Z=1`. See [the paper's reference construction](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:224).

Route: Group crossing-bond factors by their interior endpoint and normalize the resulting positive one-site weights.  
Cancel the product of site normalizers in the finite partition quotient and choose `Z` to be the product expectation of `planeInteraction`.

**FrameInteractionBoundsStatement — TRUE.** Every member of `internalBonds W` has both endpoints in `W` and is adjacent; proper colouring supplies unequal colours. The supplied bounds therefore apply factor by factor. Their endpoints are positive, so multiplying inequalities is valid. The exponent is exactly the number of factors. `internalBonds` uses east/north orientations, counting each unoriented lattice bond once. An empty bond set gives one on both sides. See [the internal interaction estimate](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:234).

Route: Extract adjacency from bond membership and apply the per-frame bounds to each factor.  
Multiply the nonnegative bounds and identify the constant products with the stated cardinality powers.

**NormalizedInteractionStatement — TRUE.** The product reference and `ψ` are strictly positive. The supplied equation for `Z` identifies the exact finite sum of the numerator, and `Z>0` justifies its division. The remaining assertions are pointwise multiplication and division of ordered real quantities. No extra normalization premise is needed. With zero sites, the reference weight is one on the unique configuration. See [the normalized density bounds](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:242).

Route: Establish strict positivity and sum the quotient; the supplied equality for `Z` gives total mass one.  
Multiply `lo ≤ ψ ≤ hi` by the product weight, divide by positive `Z`, and rearrange the products.

**SignedFrameBlockStatement — TRUE.** The finite alphabet has twelve elements, so strictly positive site weights have positive site sums. Their normalized product absorbs all arbitrary magnitudes of `h`. Either Boolean branch gives an interaction in `[b,2-b]`. The paper's conditional and constant variational comparisons, together with product tensorization, give the ratio `(b^e/Z)/((2-b)^e/Z) = frameRatio^e`. No degree bound, bipartiteness, or normalization of `h` is necessary. `E` may contain both orientations: both then appear as actual factors and both are counted. Its unequal-colour premise excludes loops. Empty `E` gives a product law with Poincare constant one. See [the signed frame application](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:220).

Route: Normalize the site weights and bound the interaction density between `b^E.card/Z` and `(2-b)^E.card/Z`.  
Apply variational comparison and product tensorization, then simplify the single density ratio to `frameRatio^E.card`.

**VariationalCenteringStatement — TRUE.** The hypothesis on `h` says precisely that it is constant on each exterior fibre. The constant mean and the conditional fibre means minimize the corresponding complex squared errors. Normalization of `p` and positivity of all fibre denominators are available. For empty `U`, the block form is zero; for full `U`, the conditional assertion becomes constant centering. See [the variational formulas](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:178).

Route: Expand the squared distance from `z` around `complexMean p f`; the weighted cross term cancels.  
Repeat on each positive exterior fibre, where `h` is constant, and sum the nonnegative residual errors.

**ProductTensorizationStatement — TRUE.** The site normalization hypotheses imply that their product is a positive probability. Its coordinate conditional expectations are commuting orthogonal averages. The paper's finite telescoping argument applies equally to dependent alphabets and complex functions. `dirichlet` sums one update per physical site, so constant one has the correct normalization. Singleton coordinates contribute zero; with no sites both variance and Dirichlet form vanish. See [the product argument](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:200).

Route: Establish product normalization and identify the commuting coordinate averaging projections.  
Enumerate sites and telescope to the constant mean; orthogonality and contraction bound variance by the sum of one-site residual norms.

The Lean traps checked were:

- Explicit `#print` inspection retained all advertised type, `Fintype`, `DecidableEq`, and `Nonempty` quantifiers. The leaves use `Type` at universe zero; this narrows their scope but does not invalidate them. Classical equality on alphabets and classical predicate decisions require no extra mathematical premise.
- A `Finset` volume is used through its finite subtype, such as `x : W`; the plane itself is infinite. `restrict B` has dependent-function codomain. Equality of restrictions is equivalent to `AgreeOn B`, using function extensionality.
- `Coupling` requires nonnegative entries and the two marginals. It does not independently assert probability normalization. Full-state `fibre` laws normally have zero entries outside their support and must not be treated as strictly positive everywhere.
- `conditionalProbability p E A` means probability of **A given E**. The definition normalizes by the first event. In this audit every conditioning event used in a route has positive mass; Lean's total division at zero supplies no shortcut.
- `conditionalExpectation` divides in `ℂ`, while fibre weights divide in `ℝ`. Identifying them requires the real-to-complex casts; the real fibre mass is positive. Squared-error expansions use complex conjugates or real parts, since `Complex.normSq` is real.
- `2-frameBound`, the density quotients, and the final bounds are real expressions. The exponents `2*A.card` and `E.card` are natural numbers. There is no truncated natural subtraction or natural division hiding in these statements. `positiveSign e` tests the Boolean value `true`.
- `FrameBoundary` assigns admissible frame letters at actual exterior neighbour sites. The extension defaults are never used on the relevant bonds. Positivity for arbitrary unit-vector pins is neither asserted nor needed.

Validation used one Lean process at a time and no Lean proof scripts. [Inspect.lean](/home/ubuntu/aklt/reports/TS_GAP_02/scratch/Inspect.lean) imported the single target module under Lean `v4.35.0-rc2` and printed all eight elaborated statements plus key definitions successfully; [Inspect.out](/home/ubuntu/aklt/reports/TS_GAP_02/scratch/Inspect.out) retains the output. Package artifacts were accessed through a workspace symlink to the repository's `.lake/packages`; no dependency or repository builds were run.

[diagnostics.py](/home/ubuntu/aklt/reports/TS_GAP_02/scratch/diagnostics.py) also passed. Exact arithmetic in `ℚ(√5)` checked all 1,728 signed factors between distinct frames against the actual `frameBound`, including attainment of both endpoints. Exact rational checks used alphabet-size tuples `()`, `(1)`, `(2)`, `(2,3)`, `(2,1,2)`, and `(2,3,2)`: 588 assignment inequalities, 70 patch constructions, 25 surgeries with pair-dependent rows, 25 conditional centering identities, six product tensorization cases, and six normalized interactions. These finite diagnostics support the definition audit; the general verdicts rest on the arguments above and the cited manuscript passages. Results are retained in [diagnostics.json](/home/ubuntu/aklt/reports/TS_GAP_02/scratch/diagnostics.json).
