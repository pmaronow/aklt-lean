STATUS: COMPLETE

All eight leaves are **TRUE as written and self-sufficient**. No correction or extra hypothesis is needed. Names in the table have prefix `AKLT.Blueprint.Rec` and belong to module `AKLT.Blueprint.Rec.NodesResponse`.

| Leaf | Paper label | Verdict | Difficulty | Main check |
| --- | --- | --- | --- | --- |
| `NetworkPositiveStatement` | d:domain | TRUE | medium | Auxiliary rules supply the finite-network positivity hypotheses. |
| `ThreeFactorizationStatement` | d:ratios | TRUE | medium | Unpinned U integration gives I; post-step D integration gives J. |
| `TwoFactorizationStatement` | d:ratios | TRUE | medium | Two U factors integrate to I₂; one D factor integrates to 1. |
| `RemovedMeanIntervalsStatement` | l:response | TRUE | hard | Three conditional means have Euclidean norm at most 3/5; free positivity supplies the extra inequalities. |
| `TwoMeanIntervalsStatement` | l:response | TRUE | hard | The conditional pair product lies between −9/25 and 9/25. |
| `FreeRemovedPairStatement` | l:response | TRUE | medium | Removal makes the pair insertion admissible at separate degree four. |
| `LogMeanBasicStatement` | l:response | TRUE | medium | Positive integral representation and explicit diagonal branch. |
| `LogMeanMonotoneStatement` | l:response | TRUE | medium | Coordinatewise monotonicity of the same integral, including diagonals. |

Difficulty estimates concern Lean implementation with the paper's supporting results available. The conditional estimates require the most finite-sum and conditioning bookkeeping. These classifications do not assume other unproved blueprint leaves as hypotheses: the site laws, moments, geometry and pins are concrete definitions, and the supporting paper lemmas are provable facts about them.

**Sources and definition trace.** The audit used repository `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`; its working tree was clean when checked. The repository was only read. The exact leaves are at [NodesResponse.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:11). Relevant definitions were followed through:

- [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:26): all fields of `Departure` and `responseI₂`.
- [Defs/Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:9): `logarithmicMean`, `removeSite`, `removedPairMean`, `responseI`, `responseJ`.
- [Defs/Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10): `Network`, `active`, `Present`, `bonds`, `presentNeighbours`, `LocalRules`, `Auxiliary`, `spins`, `partition`, `expectation`, `AdmissibleStart`, `traceStep`.
- [Defs/PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:10) and [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9): `PinAssignment`, `Vec3`, `dot`, `normSq`, `UnitVector`, `Status`, `SpinLetter`, `spinVector`, `spinWeight`, `IcoLetter`, `icoVector`, `signValue`, `goldenRatio`, `icoRadius`.
- [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): `Plane`, `latticeDist`, `Adjacent`, `Compass`, its finite enumeration and `step`, `neighbours`, `positiveNeighbours`, `internalBonds`, `originalLegs`, `protectedSites`, `boundaryDepth`, `setDistance`.

The finite-network adapter and supporting contracts were checked in [Defs/FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:10) and [Top/Common.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Common.lean:32), including the finite probability definitions they use. Paper passages are [d:domain and d:trace](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:8), [d:ratios](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:240), [l:response](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:286), and [l:finitefacts](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126) and [l:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197).

**NetworkPositiveStatement — TRUE.** `Auxiliary` includes the bound of four present bonds plus original legs at every active site. Active statuses are U or D. All interaction factors and site masses are nonnegative; each active law gives positive mass to twelve distinct unit atoms. At most four antipodes are excluded at each step of the paper's greedy assignment, so a positive summand exists for either pin choice, with all independent original pins retained.

Route, line 1: Reindex the finite active subtype and its pin fibres as a valid `FiniteSpinNetwork`, preserving each once-counted bond and original leg.  
Route, line 2: Use the finite-network positive-summand argument; when there are no active sites the single empty configuration contributes 1.

**ThreeFactorizationStatement — TRUE.** `Departure.start` makes y active and outside the protected layer, hence unpinned. Exactly three distinct neighbours contribute its only factors. The U law has second moment 1/3 and zero odd moments, giving `1 + (P_fg + P_fo + P_go)/3`. The post-step D law has total mass 1 and second moment 1/5, giving `1 + P_fg/5`. All factors off y agree with the removed network, whose normalizer is positive.

Route, line 1: Split the active-site configuration sum at y and evaluate its U integral before the step and its D integral after the step.  
Route, line 2: Identify the remaining sums with `removeSite`; express the pair terms as its positive partition times its normalized means.

**TwoFactorizationStatement — TRUE.** The same hypotheses make y unpinned. Two U factors integrate to `1 + P_fo/3`. After the outgoing bond is erased, the single remaining D factor integrates to 1. Deleting the outgoing kept flags does not alter any factor wholly off y.

Route, line 1: Separate the y coordinate and apply the U second moment and the zero first moment of D.  
Route, line 2: Identify the off-site partition with the removed network and cancel its positive normalizer in `responseI₂`.

**RemovedMeanIntervalsStatement — TRUE.** Since y is active and outside `protectedSites G`, every site at distance at most two from y belongs to G. Its neighbours therefore have no original legs. Distinct neighbours of a square-lattice vertex are nonadjacent, and each loses one actual bond when y is removed. On each positive fibre their conditional laws form a product, with mean norms at most 3/5 under either Bool choice. The three-pair mean sum lies in `[−27/50, 27/25]`, and each pair mean lies in `[−9/25, 9/25]`, giving the stated I and J intervals. Free pair positivity gives `J⁰ ≥ 1` and `I⁰ − J⁰ = (2/15) E⁰ P_fg + (1/3)(E⁰ P_fo + E⁰ P_go) ≥ 0`.

Route, line 1: Condition on the complement of the three neighbours, use their product conditional law and the U/D three-factor mean bound, and average the pair inequalities.  
Route, line 2: Use degree-four free scalar-product positivity for each pair and the displayed expansion of `I⁰ − J⁰`.

**TwoMeanIntervalsStatement — TRUE.** The two neighbours likewise have no original legs, are nonadjacent, and retain at most three bonds after removal. Their conditional means have norms at most 3/5, so their pair expectation has absolute value at most 9/25. Dividing by 3 and adding 1 gives `[22/25, 28/25]`. Free positivity gives the additional lower bound 1.

Route, line 1: Factor each positive two-site conditional fibre, apply the three-factor mean bound, and average its pair-product estimate.  
Route, line 2: Apply free degree-four positivity to the pair insertion for the final inequality.

**FreeRemovedPairStatement — TRUE.** The memberships are in the actual present-neighbour finset, so each endpoint has lost a bond to y. The insertion contributes one coordinate degree at each distinct endpoint; the complete free integrand has separate degree at most four everywhere. Nonnegative coefficients and the U/D moments through degree four give a nonnegative numerator. The removed partition is positive. No U premise is missing: a D admissible start has at most one present neighbour and cannot satisfy the two distinct memberships.

Route, line 1: Reindex the removed network and verify the complete inserted polynomial's degree bound using the lost bonds.  
Route, line 2: Apply free tensor-expansion positivity and divide by the positive normalizer; discard the impossible D-start branch if necessary.

**LogMeanBasicStatement — TRUE.** The definition explicitly sets `L(x,x) = x`. For positive unequal inputs, strict monotonicity of log makes its denominator nonzero. The paper's representation `L(x,y) = ∫₀¹ exp(t log x + (1−t) log y) dt` agrees with both branches and gives positivity and the min/max bounds. The divided-difference identity holds off the diagonal by cancellation and on the diagonal as `0 = 0`.

Route, line 1: Split the diagonal and establish the exponential-integral representation by integrating an affine exponential off the diagonal.  
Route, line 2: Bound the integrand between the positive minimum and maximum; cancel only nonzero denominators in the identity.

**LogMeanMonotoneStatement — TRUE.** The premises already imply `x' > 0` and `y' > 0`. On `[0,1]`, the coefficients t and `1−t` are nonnegative, so the exponential integrand increases when either endpoint increases. The same integral representation includes either diagonal and permits any ordering between x and y.

Route, line 1: Obtain positivity of the primed inputs and represent both means by their exponential integrals, including diagonal branches.  
Route, line 2: Apply monotonicity of log and exp with nonnegative coefficients, followed by monotonicity of the integral.

**Lean traps checked.** No defect was found, but these details matter to the writers:

- Lean inspection confirmed that all eight leaves are closed definitions of `Prop`, and `Departure` has all three proof fields (`auxiliary`, `start`, `present`). No needed typeclass argument was silently dropped.
- Configurations are functions on the finite subtype `↥D.active`, with values in `SpinLetter`; there is no `Fintype Plane` requirement. An empty active set has exactly one function. The subtype changes after removal, so splitting configurations requires an equivalence.
- `Vec3` is `Fin 3 → ℝ`. Its default function-space norm is not the Euclidean norm intended by the paper. Use `normSq`, coordinate sums and Cauchy–Schwarz, or explicitly transport to Euclidean space.
- `SpinLetter` includes `none`. Its U weight is zero, its D weight is 2/5, and the twelve other D weights are 1/20 each. The D law has total mass 1, not 3/5. There is no extra scalar trace mass.
- Degree bounds count **present** bonds, not `kept` flags. `removeSite` changes only status, leaving stale flags harmless. `internalBonds` counts each unoriented bond once; the finite-network adapter must preserve that count.
- Original legs and pins are indexed by the original G. Removal creates no new pins, and trace deletion at a protected arrival keeps every original pin. Neighbours of y can belong to `protectedSites`; the needed fact is that they have **no original legs**.
- All displayed response constants and divisions elaborate in ℝ. Pins are indexed by original-leg subtype and have squared-Euclidean norm one. No rational-cast or natural-subtraction problem occurs. Lattice differences are in ℤ before `natAbs`.
- `protectedSites` uses a classical/noncomputable finite filter and extended-natural boundary depth. Use classical decidability for arbitrary filters and reindexings. Radius-two containment follows directly from the infimum definition, without truncating infinite depth.
- `expectation` is a total real quotient. Establish positivity of the removed normalizer before cancellation. Conditional arguments apply only to positive-mass fibres; zero-mass fibres contribute nothing.
- The mean estimates use independence after fixing the complement. Unconditional independence and arbitrary-function rotational invariance of the discrete alphabet are unavailable. The needed moment computations have degree at most four.
- Split the logarithmic mean's diagonal before cancelling `log x − log y`; positive off-diagonal inputs make that difference nonzero. Primed positivity in the monotonicity leaf follows from its supplied inequalities.

**Nonvacuity and checks.** Nonempty departure examples exist: take `G = square (0,0) 2`, U status on G, X outside, and all internal kept flags except one bond incident to the centre, erased at both ends. The centre has depth three and three present neighbours; erase a second centre bond for the two-neighbour premises. Any fixed unit pin assignment works. These examples also satisfy the free-pair premises. Positive real inputs, including `(1,1)`, witness the logarithmic-mean domains. The empty-network positivity case is an intended boundary case.

[Inspect.lean](/home/ubuntu/aklt/reports/TS_REC_01/scratch/Inspect.lean) ran successfully with Lean `v4.35.0-rc2`, importing the existing repository module and printing the eight elaborated statements and key definitions; [inspection log](/home/ubuntu/aklt/reports/TS_REC_01/scratch/lean-inspection.log). Only one Lean process was used, no theorem or proof was written, and no repository build was launched. Mathlib packages are linked into scratch by a symlink to the repository's packages directory.

[check_values.py](/home/ubuntu/aklt/reports/TS_REC_01/scratch/check_values.py) checked the twelve distinct antipodal unit atoms and all 70 U/D coordinate monomials through degree four using exact arithmetic in ℚ(√5), and seven rational endpoint identities. It also checked 121 positive-input logarithmic-mean pairs and 4,356 monotonicity comparisons at 90-digit decimal precision, including exact and near diagonals; [results](/home/ubuntu/aklt/reports/TS_REC_01/scratch/value-checks.json). These are supplementary checks, not machine-checked proofs of the universal leaves.
