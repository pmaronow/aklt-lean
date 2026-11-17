STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty | Finding |
| --- | --- | --- | --- | --- |
| `AKLT.Blueprint.Q.BoundaryAbsorptionStatement` | `l:planeenergy` | TRUE | medium | Crossing factors partition by their interior endpoint; all local normalizers are positive and cancel. |
| `AKLT.Blueprint.Q.PlaneDensityBoundsStatement` | `l:planeenergy` | TRUE | medium | Internal factors have the stated bounds; the shared positive interaction mean cancels in the ratio. |
| `AKLT.Blueprint.Q.DensityVarianceStatement` | `l:density` | TRUE | medium | The minimum over complex centres gives the upper density comparison. |
| `AKLT.Blueprint.Q.DensityDirichletStatement` | `l:density` | TRUE | hard | Compare unnormalized fibre energies before minimizing; independence is unnecessary. |
| `AKLT.Blueprint.Q.ProductPoincareStatement` | `l:density` | TRUE | hard | Finite product tensorization gives the rate-one inequality, including empty and singleton products. |

All five leaves are self-sufficient as written. No corrected statement or additional premise is needed. The verdicts concern their mathematical content; no Lean proofs were written.

The exact leaf declarations were read in [NodesEnergy.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:95), alongside their elaborated forms in [inspect.out](/home/ubuntu/aklt/reports/TS_Q_08/inspect.out). The paper arguments are [sec3-quantum-frames.tex](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:747) and [app-finite.tex](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:163). The latter's conditional-expectation argument at line 22 was also checked.

**Definitions followed.** For the plane leaves, the dependency chain includes `planeSiteWeight`, `planeProductReference`, `planeInteraction`, `planeInteractionMean`, `planeDensityLower`, and `planeDensityUpper` in [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:172); `interactionBounds` in that same file at line 44; and `planeWeight`, `planeLaw`, `ProperPlaneColouring`, `PlaneConfiguration`, `FrameBoundary`, `exteriorSites`, `extendLetters`, and `extendBoundary` in [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:9). Geometry was followed through `Plane`, `Adjacent`, `latticeDist`, `Compass.step`, `neighbours`, `positiveNeighbours`, `internalBonds`, and `originalLegs` in [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8). Frame values were followed through `frameBound`, `frameRatio`, `frameVector`, and `frameRotation` in [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:32), then `Vec3`, `dot`, `IcoLetter`, `icoVector`, `signValue`, `icoRadius`, and `goldenRatio` in [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9).

For the probability leaves, the definitions read were `Weight`, `normalize`, `PositiveProbability`, `complexMean`, `variance`, `AgreeOutside`, `conditionalExpectation`, `blockDirichlet`, `dirichlet`, and `PoincareLower` in [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:8). `conditionalVariance` was also checked against the paper's integrated-variance convention: `blockDirichlet` directly uses the squared conditional-expectation residual. No geometric moment identity, torus statement, or quantum statement is needed for these five leaves.

**BoundaryAbsorptionStatement — TRUE; medium.** [Exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:95).

Every leg has its first endpoint in `W` and its second endpoint in `exteriorSites W`. Grouping these factors by their first endpoint gives exactly the site weights in the product reference, including one real factor `1/12` per site. A shared exterior site can occur in several distinct legs, with its one boundary letter used consistently in each factor. Proper colouring and `interactionBounds` give positive boundary factors. The scalar positivity needed here follows from the explicit definition `frameBound = (5 - sqrt 5) / 505`; it does not require an extra three-frame premise. Thus all local normalizers are nonzero. Their product is a configuration-independent positive scaling factor, which cancels under the global `normalize`.

Route 1: Reindex the boundary product by the subtype `W`, identifying `planeWeight` with the internal interaction times the product of unnormalized site weights.  
Route 2: Establish positivity of the local normalizers and cancel their common product when normalizing.

Lean traps: `∏ x : W` is a product over the finite subtype, whereas `originalLegs W` is a `Finset` of ordered pairs. Reindexing must preserve every leg and the site count. Endpoint membership justifies reducing `extendLetters` and `extendBoundary`; their default letters never enter these factors. Subtype membership proof terms do not change the letters. For `W = ∅`, the configuration space is a singleton and both displayed normalized weights equal one.

**PlaneDensityBoundsStatement — TRUE; medium.** [Exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:104).

Write `e = (internalBonds W).card`. Each internal bond joins adjacent sites with different colours, so its interaction factor lies between `frameBound` and `2 - frameBound`. Both endpoints belong to `W`. The explicit scalar definition gives `0 < frameBound < 1`, so both product bounds are positive. The supplied `PositiveProbability` premise and the nonempty configuration space give a positive `planeInteractionMean`. The supplied absorption equality identifies this same mean with the normalizer in the plane law. Therefore the two density bounds and their ratio have the intended meaning. Finiteness requires no additional hypothesis because all sums are finite real sums.

Route 1: Bound the internal product, establish positivity of its reference mean, and apply the supplied normalization equality to obtain both density bounds.  
Route 2: Unfold the density constants, cancel their common nonzero mean, and identify the quotient of powers using `frameRatio`.

Lean traps: establish positivity/nonzeroness before cancelling real denominators. The exponent is the cardinal of the internal-bond `Finset`; it is neither a site count nor a natural-number subtraction. The scalar quotients are real division. No separate `FrameScalarsStatement` premise is missing: the needed radical inequalities follow from the constants' definitions. If there are no internal bonds, the interaction, mean, both density constants, and ratio equal one. This includes the empty volume.

**DensityVarianceStatement — TRUE; medium.** [Exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:118).

Both laws have total mass one and positive weights. Their defined complex means minimize their respective weighted squared deviations over complex constants. Evaluate the squared-deviation functional for `q` at the mean for `p`, and apply the upper density bound. This argument works for arbitrary finite laws; no product premise is needed. `M = 0` cannot satisfy the domination premise for positive normalized laws, but the statement has many admissible instances with positive `M`.

Route 1: Use the weighted complex variance decomposition to compare `variance q f` to the `q`-weighted squared deviation from `complexMean p f`.  
Route 2: Apply `q σ ≤ M * p σ` termwise using nonnegativity of `Complex.normSq` and identify the resulting sum.

Lean traps: `f` is complex-valued, `variance` is real-valued, and the weights and comparison constant are real. The variance decomposition uses normalization and complex conjugation; a real-only variance lemma needs adaptation. The declared `Fintype Ω` is retained in all sums. An empty `Ω` cannot satisfy `PositiveProbability` because its mass sum is zero; singleton laws have zero variance. Neither observation makes the whole leaf vacuous.

**DensityDirichletStatement — TRUE; hard.** [Exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:126).

On each fixed complement fibre, the conditional expectation is the constant minimizing the unnormalized weighted squared deviation. The density lower bound compares those unnormalized objectives for every admissible centre. Minimization and summation therefore give exactly one factor `m`. Neither law needs to be a product law. The permitted value `m = 0` follows from nonnegative energies without dividing by `m`.

Route 1: Establish that each site's conditional expectation is constant on complement fibres and minimizes the weighted error among complement-dependent complex functions.  
Route 2: Compare at `q`'s minimizer using `q ≥ m*p`, use `p`'s minimizing property and `m ≥ 0`, then sum over sites.

Lean traps: the denominator in `conditionalExpectation` is complex division, but it is the complex cast of a positive real fibre mass. The fibre contains the conditioning configuration itself, so full support ensures a nonzero denominator. `AgreeOutside` uses classical proposition decidability; an alphabet `DecidableEq` premise is unnecessary. The explicit anonymous family of `Fintype (S x)` arguments is preserved: inspection shows it passed to `Pi.instFintype`, both `PositiveProbability` premises, and both `dirichlet` terms. Comparing normalized conditional probabilities pointwise would lose this argument; use the unnormalized energies. Missing alphabet `Nonempty` instances can be derived from an inhabited configuration space, which follows from normalization. An empty global configuration space contradicts the probability premises; an empty index type has one configuration and zero energy.

**ProductPoincareStatement — TRUE; hard.** [Exact declaration](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesEnergy.lean:135).

The site hypotheses make the displayed product weight a positive probability. Its single-site conditional expectations are commuting orthogonal projections in the weighted complex inner product. Finite tensorization gives the stated constant one with one update per site. Each alphabet is nonempty as a consequence of its normalized site law; a separate `Nonempty` premise is unnecessary.

Route 1: Derive from finite product sums that the single-site conditional expectations commute, are orthogonal projections, and have full product equal to the constant mean.  
Route 2: Telescope these projections into orthogonal increments and bound each squared increment by its single-site residual, then sum.

Lean traps: the alphabet family is dependent, so reindexing may require dependent-function equivalences. Inspection confirms that its explicit `Fintype` argument is used in the site probability premises and `PoincareLower`. Complex functions are included. `PoincareLower` is an inequality for every function, so it needs no assumption that the product has at least two points. There is no division by the number of sites. With an empty index type the product law has mass one on its unique empty configuration and both forms vanish. One-letter sites also contribute zero. An empty alphabet at an actual site contradicts its site probability premise.

**Validation.** The scratch [inspect.lean](/home/ubuntu/aklt/reports/TS_Q_08/inspect.lean) ran successfully against the existing Lean 4.35.0-rc2 artifacts. It contains only declaration inspection commands and checks all five elaborated statements, including the explicit instance arguments. A local `.lake/packages` symlink points to the repository's existing packages. Only one Lean process was used; the repository was not built or modified.

The independent finite checks in [check_small_cases.py](/home/ubuntu/aklt/reports/TS_Q_08/check_small_cases.py) passed; [checks.json](/home/ubuntu/aklt/reports/TS_Q_08/checks.json) records their scope. They use exact rational arithmetic and exact arithmetic in `Q(sqrt(5))`, without floating-point tolerances:

- All 1,728 signed interaction factors for distinct frame colours satisfy the specified bounds; the lower bound is attained. This also checks the consistency of the `interactionBounds` antecedent against the concrete frames.
- Absorption, positivity, normalization, both density bounds, and the density ratio passed for all 4,058 configurations across ten volume/boundary cases. The cases cover empty, singleton, adjacent-pair, separated-pair, and three-site corner volumes with two- and three-colour proper colourings; the latter geometries include shared exterior neighbours.
- The variance and Dirichlet density comparisons passed for 240 positive-law cases with complex-valued functions, including the sharp pointwise lower/upper ratios and `m = 0`.
- Product Poincare passed for 240 cases across alphabet-size lists `[]`, `[1]`, `[2]`, `[2,1]`, `[2,3]`, and `[2,2,2]`. Another 240 constant-function checks gave zero on both sides, and 240 additive-function checks attained equality.

These finite checks supplement the definition and paper audit; they are not formal proofs of the leaves. Machine-readable verdicts, reasons, fixes, two-line routes, and difficulties are in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_Q_08/verdicts.jsonl).
