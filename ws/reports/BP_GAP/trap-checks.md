# Per-leaf trap review

All names have namespace `AKLT.Blueprint.Gap`. The exact quantified statements and full eight-category checks are in `leaves.json`. The common checks retain nonempty alphabets, zero or empty products, finite sum indices, explicit cardinal casts, controlled natural subtraction and nonzero conditioning denominators. The following notes record the leaf-specific checks.

| Open leaf | Specific check |
|---|---|
| `FibreNormalizationStatement` | The full-state fibre law has zero atoms outside its fibre and is only Probability; the restricted block law is PositiveProbability. Its denominator contains the given input configuration with positive mass. |
| `ConditionalProjectionStatement` | Use complex conjugation in self-adjointness. Constants, means, and the two endpoint blocks are included; no real-only scalar-product convention is substituted. |
| `ConditionalVarianceStatement` | conditionalVariance is pointwise E_U\|f-E_Uf\|², whereas blockDirichlet is its integrated form. The equality of these finite sums is part of this leaf. |
| `MaximalCouplingStatement` | Probability forces a nonempty state space even without a separate Nonempty instance. Overlap 0 and 1 are included; branch at overlap=1 before residual division. |
| `CouplingMarginalTVStatement` | The disagreement lower bound holds for every coupling, and marginalization is by an arbitrary deterministic map. Neither statement asserts Hamming contraction from TV. |
| `MarginalCompletionStatement` | Zero marginal fibres are never sampled. Choose arbitrary residual laws only on zero fibres, after deriving that the full state space is nonempty from normalization. |
| `HammingLocalizationStatement` | The same full-law coupling is used on both sides. Empty Q and Q=univ, and a zero-site product, satisfy the pointwise inequality. |
| `CommonMinorizationStatement` | The common law is an actual probability, and 0≤t≤1 is explicit. The endpoints t=0 and t=1 require no normalized residual law. |
| `SurgeryPreservationStatement` | The selected coupling may depend on both input configurations. Its first row marginal depends only on the first configuration, and its second only on the second. |
| `ConditionalPatchCouplingStatement` | A and B are disjoint. Resample A after completing B and the remaining coordinates, conditioning separately on each full complement; then use the common prescribed A assignment. Empty A/B and t=0/1 are valid. |
| `FrameProductReferenceStatement` | Only admissible frame letters are used. Every fixed boundary factor is absorbed into its incident site weight. The empty volume has Z=1 and the empty product reference. |
| `FrameInteractionBoundsStatement` | Proper colouring supplies distinct frames on every internal edge; positive lower bounds justify multiplying inequalities. The edge set is counted once by internalBonds. |
| `NormalizedInteractionStatement` | Z is explicitly positive and equal to the product-law expectation. lo and hi are positive. No division is performed at a zero site normalizer or zero Z. |
| `SignedFrameBlockStatement` | The per-edge bounds cover both signs, h_x is strictly positive, and properness is required on each counted edge. Boundary factors do not enter the exponent. This covers arbitrary finite blocks and the empty product. |
| `VariationalCenteringStatement` | An admissible h must be constant on each complement fibre. The constant centering bound and the conditional centering bound are separate quantified conclusions. |
| `ProductTensorizationStatement` | Every site law is a positive normalized probability, and each alphabet is nonempty. Empty site sets give a one-point law, not an empty configuration type. |
| `DensityComparisonStatement` | Both density constants are positive. The conclusion loses one ratio m/M; a second ratio is not introduced. The displayed reference is a normalized product law. |
| `ConditionalBlockComparisonStatement` | Nested one-site conditioning inside a block must fix exactly the original complement of that site. Repeated labels contribute separately, including identical or empty blocks. |
| `MultiplicityEstimateStatement` | t may be zero, as no division is used. Nonnegative one-site Dirichlet forms justify the multiplicity estimate; sums are over labels. |
| `HammingPathStatement` | Insert zero into the finite edge-value set. This defines lipschitz=0 on singleton products, even if no Hamming-one pairs exist. Nonempty alphabets give a nonempty product. |
| `LipschitzCouplingStatement` | Each kernel row is a probability; r≥0 is explicit. The singleton case has no neighbour pairs and zero Lipschitz seminorm. |
| `LipschitzEigenvalueStatement` | A nonzero mean-zero real function is nonconstant because p sums to one. The eigenvalue bound uses the positive edge seminorm; constant eigenvectors are excluded by local premises. |
| `ReversibleEigenvalueGapStatement` | Positive p makes diag(sqrt p) invertible. Restrict to mean-zero real functions before diagonalization, then split complex functions into real and imaginary parts. The zero-dimensional restriction is allowed. |
| `BlockAverageFormStatement` | The label type is nonempty, so its cardinal denominator is positive. All sums count labels with multiplicity and preserve the rate-one convention. |
| `ProductPoincareTransportStatement` | The same site and configuration equivalences transport the variance and every singleton conditional form. Site and alphabet instances are explicit, so the finite-product enumerations agree. |
| `ProductCouplingTransportStatement` | Use the inverse of the same configuration bijection in both components. coordinate_eq proves exact equality of Hamming counts, not merely a bound. |
| `ThresholdSpacingStatement` | geometryThreshold is at least 16^4 for every l, including l=0. Monotonicity of nonnegative square roots gives s≥16 and excludes u=0. |
| `ContainingBlockCountStatement` | M≥1 and L,N≥2M+3 imply injectivity of the inner offset square. Count centre labels, not distinct sets or measure symmetries. |
| `ExteriorBlockCountStatement` | The halo includes corner offsets. At equality L=2M+3 its width is one full period and coordinate differences are still strictly smaller than that period. |
| `BlockVolumeBoundStatement` | The target is the cardinality of Site L N (A=LN), not a normalized update rate. Its upper bound is obtained from an actual injection. |
| `PeriodicNeighbourCouplingStatement` | The original one-site disagreement survives for non-containing blocks. Adjacent labels cost 1+K, far labels cost 1, and containing labels cost 0. Counts and K≥0 are explicit. |
| `TorusColourStatement` | Size supplies periods at least three. The odd last-site branch is checked at both incident edges, including wrap edges of period three. |
| `PullbackColourStatement` | Plane adjacency is unoriented; identify a positive torus bond or its reverse. Size excludes a plane unit edge reducing to a loop. |
| `HaloInjectionStatement` | The expanded coordinate interval has width 2M+3; any two elements differ by at most 2M+2, strictly below each period. Equality in the period bound is allowed. |
| `LiftBondStatement` | Separate internal bonds from crossing bonds. The halo injection rules out an exterior point reducing to an internal one. Unordered endpoint sets prevent orientation sign mistakes. |
| `BoxCoordinatesStatement` | The parity sign is a function on the lifted integers only. Sitewise antipodal permutations preserve the actual finite alphabets. The same change works for both exterior fibres, with at most one changed lifted site. |
| `BoxGaugeLawStatement` | The coordinate data, exact lifted bond data, proper colouring, and positive signed interactions are explicit. Exterior-only factors are nonzero before cancellation. No global odd-torus bipartition is assumed. |
| `TorusRangeTransferStatement` | The input uses the original four torus neighbours, while the conclusion allows the larger physical sup-distance halo. Extra corner sites cause no interaction and do not invalidate the implication. |
| `SquareInternalEdgesStatement` | internalBonds is an oriented-once Finset of pairs. The formula also holds at M=0; no unsigned subtraction is used in the edge count. |
| `FrameSpecRegularityStatement` | Positivity and conditioning consistency for the actual finite boundary law are explicit local inputs. Range one is proved from the four-neighbour product, without adding a missing Top hypothesis. |
| `FrameSpecEnergyStatement` | conditionalProbability takes the conditioning event first. J is fixed in that argument and U is the prescribed event; the exponent is U.card. Map subtype sites injectively into W before changing cardinalities. |
| `FrameWindowTransferStatement` | Allowed i satisfy i≥2 and i≤s, so the actual window is contained in the far volume even before using the large-threshold shell export. Total-boundary extensions therefore do not affect its marginal. |
| `ShellNestingStatement` | The floor error is at most one and s≥16 is explicit. Negative integer indices yield either the same inequality or an empty shell; no implicit Nat subtraction is used. |
| `FiniteEnergyChainStatement` | Full support and nonempty alphabets make every prescribed partial conditioning event attainable. The exponent counts prescribed sites, not conditioning sites. |
| `ShellRowStatement` | h≥4 and h≤s, geometric threshold, local separator facts, full support, consistency, energy, and all-boundary W are explicit. Skipped rows are identity; index h+1 receives no W success bound. Empty A/B/F and delta=1 are included. |
| `TraceMarginalsStatement` | The initial pair law is the product of two normalized positive laws. A skipped row is a point mass; every other row has the two full conditional marginals. Pair dependence is unrestricted. |
| `TrialCountStatement` | Fin h times correspond to shell indices 2 through h+1. Trials stop at h, and exclude both i and i+1 if exceptional. h≥4 controls h-3. |
| `ShellAbsorptionStatement` | Only positive-mass traces are used. A trial includes an unskipped successor. Later supports preserve agreement on the whole earlier far set, not only on the current shell. |
| `FiniteTrialFailureStatement` | No independence is assumed. Order the finite trial set and condition on the complete past. Empty trials give exponent zero; delta=0 or 1 is included without reciprocal 1-delta. |
| `TraceDisagreementStatement` | The endpoint coupling is required to be precisely the pushforward of the trace law. The success implication is required on positive-mass paths; zero paths contribute nothing. |
| `TerminalRadiusStatement` | This leaf takes the local stopped estimate, an assembled result, not another closed leaf as an assumption. s≥16 follows from the geometry threshold, so floor(s)≥4 and s-4>0. The zero-base real-power branch is explicit in the proof route. |
| `ScaleExistenceStatement` | d>0 is explicit. The integer is chosen before colouring, translate, boundary, and torus periods. No finite-dimensional compactness or effective numerical cutoff is asserted. |
| `BinomialTailStatement` | 0<d≤1/2 makes d^20*n^20 positive and 1-d positive. n≥44 makes all twenty falling factors positive, with n-3 and n-22 interpreted correctly. |
| `ScaleGeometryStatement` | All powers n^8 and n^2 in size conditions are natural powers. The spacing equalities are real equalities, using nonnegative square roots. n≥44 prevents a zero-scale corner case. |
| `HammingCardinalityStatement` | The near region is counted inside the full square subtype; it is bounded by the entire integer sup-ball, regardless of placement or exterior seed. n≥1 controls both polynomial bounds. |
| `HammingBudgetStatement` | The tail inequality is an explicit numerical input for this one n,d. Positive d and n≥44 justify all denominators. Each budget term is at most n^8/2000. |
| `FarBoundaryEqualityStatement` | y is explicitly outside the nonempty square. Distance zero is impossible there, so distance≠1 really means beyond range one. The full laws, not just marginals, are equal. |
| `StoppedHammingConversionStatement` | 0≤d≤delta≤1 and n≥4 control both bases and natural exponents. The local stopped estimate supplies a full-law coupling and localization is applied to that same coupling. |

The nine proved leaf statements are listed in report.md; their proofs and closedness checks settle the corresponding edge cases. No open statement was accepted as a proof.
