STATUS: COMPLETE

| Leaf | Verdict | Difficulty |
|---|---|---|
| `AKLT.Blueprint.Gap.PullbackColourStatement` | TRUE | easy |
| `AKLT.Blueprint.Gap.HaloInjectionStatement` | TRUE | medium |
| `AKLT.Blueprint.Gap.LiftBondStatement` | TRUE | medium |
| `AKLT.Blueprint.Gap.BoxCoordinatesStatement` | TRUE | medium |
| `AKLT.Blueprint.Gap.BoxGaugeLawStatement` | TRUE | hard |
| `AKLT.Blueprint.Gap.TorusRangeTransferStatement` | TRUE | easy |
| `AKLT.Blueprint.Gap.SquareInternalEdgesStatement` | TRUE | medium |
| `AKLT.Blueprint.Gap.FrameSpecRegularityStatement` | TRUE | medium |

All eight leaves are true and self-sufficient as written. No statement changes or additional premises are required. The verdicts include the explicit definitions of the fixed frames and lattice, rather than treating their intended mathematical meanings as assumptions.

Audited repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The paper references below use `/home/ubuntu/aklt/manuscript-v2/`. The repository was read only; all generated files are in this report directory.

**Definitions traced**

| Source | Relevant definition closure |
|---|---|
| [NodesPeriodic.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:55) | All eight exact statements; `LiftBonds`, `BoxCoordinates`, `paritySign`. |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:15) | `Config`, `restrict`, `AgreeOn`, `fibre`, `blockLaw`, `ProductChange`, `Carries`, `PlaneSpec`, `fill`, `RegularSpec`, `frameSpec`, `reduction`, `torusSquare`, `torusHalo`, `internalCount`, `TorusRangeOne`. |
| [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:16) | `Size`, its `NeZero` instance, `Site`, `Direction`, `Bond`, `nextSite`, `bondSites`. |
| [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:7) | `Plane`, `latticeDist`, `supDist`, `Adjacent`, `Compass` and its steps, `neighbours`, `positiveNeighbours`, `internalBonds`, `originalLegs`, `setDistance`, `square`. |
| [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8) and [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:32) | `Vec3`, `dot`, `goldenRatio`, `icoRadius`, `IcoLetter`, `signValue`, `icoVector`, `frameRotation`, `frameVector`. |
| [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:9) | Both proper-colouring predicates; plane/torus configurations and boundaries; `exteriorSites`, `extendLetters`, `extendBoundary`, both weights and laws, `marginal`. |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:8) and [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:41) | `Weight`, `normalize`, `PositiveProbability`, `AgreeOutside`, `conditionOn`. |
| [Specification.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Specification.lean:9) and [Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:9) | `inducedBoundary`, `conditionalPlaneLaw`, `conditionalTorusLaw`, `torusNeighbours`. |

**Findings and proof routes**

**[PullbackColourStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:57) — TRUE; easy.**

Adjacent is integer L1 distance one, hence one of the four unit displacements. Reduction sends it to a frozen positive-direction Bond, possibly with endpoints reversed. Size has both periods at least 3, so no edge becomes a loop. ProperTorusColouring therefore gives the required unequal colours. Lean traps: Bond indexes only positive directions; reverse the inequality for west/south. The casts in reduction are integer-to-ZMod casts, not chosen representatives.

Paper: [t:mainW](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:438).

Proof route: Classify latticeDist x y = 1 into the four unit displacements and reduce each displacement.  
Apply the proper-colouring hypothesis to the corresponding frozen bond and reverse its inequality when necessary.

**[HaloInjectionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:63) — TRUE; medium.**

For two points of square a (M+1), each integer coordinate difference has absolute value at most 2*M+2, strictly below both periods by 2*M+3 <= L.val,N.val. Equal ZMod reductions make each difference divisible by its period, forcing zero. The equality threshold is valid, and arbitrary negative centres cause no problem. Lean traps: square endpoints and differences are integers while M and the periods are naturals; use Int casts and natAbs. InjOn is on the coerced Finset, not on all Plane.

Paper: [l:boxlift](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:801).

Proof route: Extract coordinate interval bounds from square membership and divisibility from equality of the two ZMod casts.  
A period multiple with absolute value strictly smaller than that positive period is zero; conclude equality of both coordinates.

**[LiftBondStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:80) — TRUE; medium.**

All three conjuncts of LiftBonds hold. Internal coordinate differences are in [-2*M,2*M], so a torus unit edge has its actual unit displacement without wrapping. A torus crossing bond lifts its unique internal endpoint and its four-neighbour displacement into the halo; its other lift is exterior. Halo injectivity gives the final membership equivalence. Size prevents loops and duplicate unordered bonds. Lean traps: bondSites is an unordered Finset while Bond is a positive orientation index; the crossing condition is card(intersection)=1, not an oriented endpoint condition.

Paper: [l:boxlift](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:832).

Proof route: Classify torus bonds by positive direction and recover their unit displacements using the interval bounds; lift a crossing bond from its internal endpoint.  
Use square inclusion in the halo and the supplied InjOn hypothesis to show that a halo point has internal image exactly when it is internal.

**[BoxCoordinatesStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:108) — TRUE; medium.**

The hypothesis supplies an injective antipodal frameVector for each colour, so choosing the unique antipodal letter gives an involution and hence a site-alphabet permutation. Lift the centre using integer representatives and invert reduction on the inner square using the supplied halo injectivity. Define the transformed boundary only on the finite lifted halo (or exteriorSites), with a common fixed letter elsewhere. Then a changed torus halo site has exactly one exterior lift; all other plane boundary values agree. No proper-colouring premise is needed. Lean traps: boundary is a total Plane assignment, so a global periodic pullback would repeat the changed site infinitely often and would fail boundary_change; use the cutoff extension. setDistance has type ENat, and the required exterior distance is exactly one.

Paper: [l:boxlift](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:854), [t:mainW boundary extension](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:475).

Proof route: Choose an integer centre lift; combine the inverse reduction on the square with the colour-dependent antipodal involutions to build ProductChange.  
Extend the sign-changed boundary on the finite halo by a fixed letter outside it, and use halo injectivity and coordinate clamping to verify boundary_change and distance one.

**[BoxGaugeLawStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:118) — TRUE; hard.**

BoxCoordinates already supplies a configuration equivalence, site correspondence, internal parity-vector identity, and the parity-vector identity at every exterior nearest-neighbour site. centre_reduces identifies the image of its square with the labelled torusSquare. Along each plane nearest-neighbour bond the integer parity signs multiply to -1, so every affected antiferromagnetic factor becomes the corresponding ferromagnetic factor. LiftBonds and the loop/duplicate exclusions in Size give the exact bond reindexing. The supplied cross-colour positivity and proper torus colouring make all fixed exterior factors and normalizers strictly positive, allowing cancellation. No separate antipodality or frame-injectivity premise is missing: C already contains the required equivalence. Lean traps: Carries compares normalized masses, not raw weights; torus and plane site factors differ by a positive constant, and exterior-only factors must also be cancelled. Boundary values away from exteriorSites are irrelevant, including corner halo sites.

Paper: [l:boxlift](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:854).

Proof route: Reindex the internal and crossing torus bond factors using LiftBonds; apply C.vector_change and C.boundary_vector with opposite adjacent parity signs.  
Express the torus fibre weight as a positive constant times the transformed planeWeight, then reindex the finite normalizing sum by C.change.configurations and cancel the constant.

**[TorusRangeTransferStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:131) — TRUE; easy.**

conditionalTorusLaw unfolds to blockLaw for this law and alphabet. Every four-neighbour of a point represented by an offset in [-M,M]^2 is represented by an offset in [-M-1,M+1]^2. Consequently (U.biUnion torusNeighbours) \ U is contained in torusHalo \ torusSquare for U=torusSquare, and agreement on the latter implies the hypothesized Markov agreement. This uses no injectivity and remains valid when the square wraps or fills the torus. Lean traps: prove the subset in this direction; the halo includes corners absent from the interaction boundary. M>=1 is redundant, not contradictory.

Paper: [l:planeenergy](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:708), [t:mainW](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:434).

Proof route: Show the exterior four-neighbour set of torusSquare is contained in torusHalo minus torusSquare by adding a unit offset.  
Restrict AgreeOn to that subset, apply the supplied conditional-law equality, and unfold blockLaw and conditionalTorusLaw.

**[SquareInternalEdgesStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:139) — TRUE; medium.**

square a M is an inclusive integer box of side 2*M+1. internalBonds uses exactly the east and north neighbours and indexes each bond once. Each of the 2*M+1 rows has 2*M horizontal bonds, with the same vertical count, giving internalCount M=2*(2*M+1)*(2*M). M=0 has one site and no bonds, so both sides are zero. Negative and translated centres do not affect the count. Lean traps: internalBonds is a Finset of positively oriented ordered pairs despite its unoriented mathematical meaning; separate the disjoint horizontal/vertical families and justify integer interval cardinalities before converting to Nat.

Paper: [t:mainW](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:468).

Proof route: Split internalBonds into the disjoint horizontal and vertical bond families and reindex each by its permitted initial coordinates.  
Compute their integer-interval product cardinalities as (2*M)*(2*M+1) and add; the same computation covers M=0.

**[FrameSpecRegularityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:145) — TRUE; medium.**

The two law hypotheses supply finite-boundary positivity and full conditioning consistency. Restrict a total exterior assignment to exteriorSites W to obtain the first RegularSpec conjunct. For V subset W, the conditioning predicates agree after subtype reindexing; on exteriorSites V, fill uses sigma on W and the exterior assignment outside W, exactly inducedBoundary. A neighbour of V outside W is necessarily an exterior neighbour of W, so extendBoundary defaults never enter. The last RegularSpec conjunct follows directly because planeWeight uses the total boundary only at originalLegs W endpoints, all outside W and at sup-distance at most one from W. Empty W or V is valid: the configuration type on an empty volume has one element, its planeWeight is 1, and no exterior factor occurs. Lean traps: finite FrameBoundary W and total Plane assignments are different function types; reindex membership proofs explicitly. setDistance takes values in ENat and equals top on the empty set, whose boundary is empty.

Paper: [l:planeenergy](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:691).

Proof route: Restrict total boundaries to exteriorSites, use the given positivity and consistency, and identify the induced finite boundary with the restriction of fill.  
For range one, each exterior leg endpoint has an adjacent witness in W and hence sup-distance at most one; agreement there makes every planeWeight factor and its normalization equal.

**Lean and boundary checks**

A scratch Lean module imported `AKLT.Blueprint.Gap.NodesPeriodic` and printed all eight declarations plus `BoxCoordinates`. It exited successfully with Lean `v4.35.0-rc2`; [the output](scratch/inspect-output.txt) confirms the inferred quantifier types. No additional typeclass parameter or intended hypothesis was silently dropped. The model uses the fixed finite twelve-letter type, while the infinite plane is only indexed through finite-volume subtypes. Classical decidability is needed for the finite restrictions, conditions and marginals; it adds no mathematical premise.

The cast checks distinguish natural radii and cardinalities, integer coordinates and parity, real interaction factors, and extended-natural set distances. In particular, the divisions in the fixed rotation and weights are real divisions. For the gauge law, the positivity premise prevents zero normalization and zero exterior constants. For regularity, an empty finite volume has one configuration and weight one, while distance to the empty set is infinity; these conventions agree with the statements.

**Diagnostics**

The reproducible [finite diagnostic script](scratch/check_cases.py) passed; [results](scratch/finite-checks.json) record:

- 135 lifted geometries with radii 1–5, translated and negative centres, and periods at and just above `2*M+3`. These check halo injection, internal/crossing bond sets, halo membership, unique exterior lifts and reduction of plane edges.
- 33 internal-edge counts with radii 0–10 and three centres; 1,078 halo inclusions with periods 3–9 and radii 0–10, including squares that wrap or cover the torus.
- All 19,683 pairs `V ⊆ W ⊆ {-1,0,1}²`, including empty sets, checking that an exterior neighbour of `V` outside `W` belongs to `exteriorSites W` and that each exterior leg lies within sup-distance one.
- Exact arithmetic in `Q(sqrt(5))` for injectivity and antipodality of all three fixed frames and positivity of all 1,728 cross-colour factors `1 ± dot`. Their attained minimum is exactly `(5 - sqrt(5))/505`, so the frame hypotheses are not vacuous.
- Three gauge placements, including odd periods and the smallest admitted periods: exact equality of the torus/plane raw-weight ratio across four sampled interior configurations per placement, followed by exhaustive twelve-letter normalization of one specified site fibre in each placement.

The diagnostics supplement the definition audit; the gauge checks do not enumerate all block configurations or constitute Lean proofs. Only one Lean process was used, for declaration inspection. No leaf proofs were written.
