STATUS: COMPLETE

| Leaf (namespace `AKLT.Blueprint.Rec`) | Paper label | Verdict | Difficulty | Finding |
|---|---|---|---|---|
| [`UDepartureInjectiveStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:98) | `l:terminalcover` | TRUE | easy | A departure changes U to D; no operation restores U. |
| [`DiamondTwelveStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:108) | `l:terminalcover` | TRUE | easy | The punctured Manhattan diamond contains 4 + 8 sites. |
| [`TerminalExceptionCountStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:113) | `l:terminalcover` | TRUE | hard | Existing pair hypotheses suffice to localize and inject all exceptional U departures. |
| [`KernelOrderingStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:11) | `d:kernel-order` | TRUE | easy | Sorting and complementary filtering preserve the first-visit indices. |
| [`KernelPositivityStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:17) | `d:kernel` | TRUE | easy | Cardinality follows from `powersetCard 2`; all coefficient-table entries are positive. |
| [`ShiftGeometryStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:24) | `l:Mtheta` | TRUE | medium | Each response site is one step from the departure vertex. |
| [`KernelSupportStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:30) | `d:kernel` | TRUE | medium | Empty exposure at length zero; no pair has shift greater than n + 1. |
| [`KernelRegroupStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:36) | `d:kernel` | TRUE | medium | Nonnegative `ENNReal` sums commute, including when infinite. |

All eight statements are true as written and self-sufficient. No corrected statement or additional premise is required. The `fix` fields in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_REC_08/verdicts.jsonl) are empty. These are mathematical truth assessments and proof routes; no proofs were written.

Reviewed repository `main` at commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository was not modified. Paper references below point to the supplied local manuscript.

**1. UDepartureInjectiveStatement — TRUE, easy.**

[`prefixNetwork`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:81) takes the first `j + 1` vertices, so its status is measured before departure j. [`traceStep`](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:88) updates only the departure site's status, sending U to D and either other status to X. Later steps cannot restore U. Consequently equal vertices at distinct indices cannot both have U status at departure. In fact, the auxiliary, admissible-start, and stopped-trail premises are unnecessary for this status-only conclusion. This agrees with the [paper's status argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:232).

Proof route, line 1: Establish that tracing preserves the property that a given site's status is not U.  
Proof route, line 2: Order two distinct indices, factor the later prefix through the earlier departure, and contradict its U status.

Lean cautions: distinguish departure indices `Fin n` from the `n + 1` vertices; the singleton prefix performs no step. Use `Fin.ext` when passing back from equal natural indices. At n = 0 the index conclusion is empty, as intended.

**2. DiamondTwelveStatement — TRUE, easy.**

[`Plane`, `latticeDist`, and `square`](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) mean the ambient integer lattice, Manhattan distance using integer `natAbs`, and a translated inclusive 5 by 5 square. The admissible offsets are `(±1,0),(0,±1),(±2,0),(0,±2),(±1,±1)`: twelve distinct points. The [paper](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:232) counts exactly these sites.

Proof route, line 1: Translate by minus e, preserving the square, Manhattan distance, and cardinality.  
Proof route, line 2: Enumerate the 25 offsets in `[-2,2]²`, retaining the twelve with distance one or two.

Lean cautions: this is a `Finset` cardinality, with no `Fintype Plane` instance needed. Coordinate subtraction takes place in ℤ, so there is no truncated natural subtraction.

**3. TerminalExceptionCountStatement — TRUE, hard.**

[`PairSetup`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:110) includes `PairData.pair : D.ResponsePair X u v c`, hence the complete ordinary consistent-domain hypotheses, active endpoints, a removed centre, distance-two endpoint geometry, and the D-endpoint degree restrictions. It also includes `u ∉ protectedSites G`; the leaf explicitly supplies the corresponding condition for v. Thus these requirements are already hypotheses, rather than missing premises.

The first stopping set is `insert v S`. Its endpoint e belongs to S and v does not, so the entire first trail avoids v. Tracing leaves v's status and kept set unchanged. At e, only the arrival flag is lost; every other nonlive site retains the full-U/two-kept-D rules. Normalizing the second start erases the flag to removed c. During the second trace the same induction preserves these rules away from e and the current endpoint. A departure site lies outside S, so its radius-two diamond lies in G. If its distance from e exceeds two, its non-tip data admit a covered pattern. No second departure can equal e, since e is in the stopping set.

Crucially, the predicate is [`CoveredDepartureV2`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:15): matching intersects translated template kept sets with the original G. This permits the full template U kept sets at boundary corners, with external slots representing original legs. The tips have covering U status and are excluded from global matching. The uncorrected `Defs.CoveredDeparture` would present the boundary obstruction documented in [`Counterexample.lean`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Counterexample.lean:36); that obstruction does not apply here.

Every exceptional U departure therefore lies in the punctured radius-two diamond about e. Status monotonicity makes the vertex map injective on those indices. This is the [paper's full second-trace argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:183), including exceptions at arbitrary positions.

Proof route, line 1: Derive the first- and second-trace kept-set invariants and construct V2 pattern witnesses when the departure is farther than two from e.  
Proof route, line 2: Inject the filtered exceptional indices into the twelve-site diamond, using U-departure injectivity and its cardinality.

Lean cautions: `uncoveredCount` filters all of `Fin m`, not a prefix. Prove the derived second start is auxiliary and admissible before applying lemmas requiring those facts. Keep original G fixed throughout normalization and tracing. Membership in the square follows from the Manhattan bound by bounding each coordinate. Classical decidability is needed for the filter involving an existential covered-pattern predicate. H1, H2, H3, pins, partition positivity, and ordinary-domain membership of the terminal auxiliary network are unnecessary.

**4. KernelOrderingStatement — TRUE, easy.**

[`firstVisitList`](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:73) filters the duplicate-free `List.finRange n` by absence of an earlier departure. For n ≤ 12, `mergeSort` preserves the list up to permutation for any Boolean comparator. For n > 12, straight and nonstraight filters partition the original list. Nodup follows from permutation. The [paper's cutoff and θ independence](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:572) agree with the definitions.

Proof route, line 1: Obtain Nodup of `firstVisitList` from `finRange` and filtering.  
Proof route, line 2: Apply `List.mergeSort_perm` or `List.filter_append_perm`, then transport Nodup across the permutation.

Lean cautions: the conclusion is permutation plus Nodup, not sortedness or optimality. Transitivity of `shortOrderLE` and `ClosedTrail` are unnecessary here. Its rational score divisions occur only after the zero-reward checks; in any event comparator properties are not required for permutation. The branch at n = 12 is the short branch.

**5. KernelPositivityStatement — TRUE, easy.**

The [exact coefficient definitions](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:10) have strictly positive rational entries for both Boolean cases: α = 145217/10⁶ or 150000/10⁶; β = 352782/10⁶ or 357549/10⁶; β′ = 340008/10⁶ or 344661/10⁶. The passage factors are 1000/961 and 200/187, and base factors are 1/3 and 1/5. [`responsePairs`](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:36) uses `powersetCard 2`, guaranteeing two distinct elements. Conditionals, finite sums, and the recursive exposure sum preserve nonnegativity, including the zero closed-trail branch.

Proof route, line 1: Split the finite coefficient-table cases and use `mem_powersetCard` for pair cardinality.  
Proof route, line 2: Induct through `exposureSum` after establishing nonnegative rewards, then sum nonnegative word contributions.

Lean cautions: these coefficients live in ℚ, so the divisions are rational. Direction words have a finite function-type instance inherited from `Fin n` and `Compass`; Plane itself remains infinite. The comment says “live neighbours,” but the displayed conclusion asserts cardinality and positivity only. For arbitrary invalid words the inserted outgoing site need not be live. Proving that extra semantic claim would require a valid closed-trail hypothesis; it is not part of this leaf.

**6. ShiftGeometryStatement — TRUE, medium.**

Every response-pair member is a neighbour of departure vertex y: either it belongs to `liveOtherNeighbours`, or it is the inserted outgoing vertex, which is a unit step away by the `wordVertex` recurrence. The endpoint equality in [`ClosedTrail`](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:15) gives `d(y,u) ≤ i` and `d(y,v) ≤ n-i`. Thus each response site z satisfies

`min(d(z,u), d(z,v)) ≤ min(i+1, n-i+1) ≤ n/2+1`.

Taking the finite supremum gives `pairShift`. This is exactly the [paper's geometry](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:633), and also holds at revisit departures.

Proof route, line 1: Derive prefix/suffix distance bounds and response-member adjacency from the unit-step recurrence.  
Proof route, line 2: Use triangle inequalities, bound the minimum by the mean, and apply `Finset.sup_le`.

Lean cautions: the displayed division by two is in ℝ, not ℕ. The suffix bound uses natural `n-i` only with `i < n`, so no truncation error occurs. `Finset.sup` defaults to zero on an empty set; membership in `powersetCard 2` ensures the actual pairs are nonempty. No positivity, H2, or H3 premise is needed.

**7. KernelSupportStatement — TRUE, medium.**

At n = 0, the first-visit list and ordering are empty and `exposureSum` is zero; also `kernelStart` differs from both targets. At any length, the preceding geometric bound implies `pairShift ≤ n+1`. When `n+1 < s`, every conditional in `responseKappa X Y s` is zero, hence so are its exposure sum and the length coefficient.

Proof route, line 1: Simplify the empty ordering and exposure at length zero.  
Proof route, line 2: Exclude shift s for every closed-trail response pair, then propagate zero through rewards, exposure recursion, and the finite word sum.

Lean cautions: `Finset.range (n+2)` includes precisely shifts 0 through n+1; the strict support inequality matches this endpoint. The word sum ranges over every direction word, so split the `ClosedTrail` conditional before using geometry. A definition named `ShiftGeometryStatement` is a proposition, not an available proof; establish its content or use a subsequently proved theorem.

**8. KernelRegroupStatement — TRUE, medium.**

[`shiftKernel` and `shiftedKernel`](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:110) take values in `ℝ≥0∞`. Distribute the fixed shift factor over the length tsum, then exchange the two tsums. The support property makes the fixed-length shift sum equal to the finite range used in `shiftedLength`. These operations permit infinite values and require no real summability, matching the [paper's nonnegative-series convention](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:550).

Proof route, line 1: Unfold the kernel series and apply `ENNReal.tsum_mul_right` followed by `ENNReal.tsum_comm`.  
Proof route, line 2: Use support to discard shifts outside `range (n+2)` and identify each inner sum with `shiftedLength`.

Lean cautions: retain `ENNReal` throughout; there is no need for `toReal`, subtraction, or a finiteness premise. The shift factor is `ENNReal.ofReal` of a real integer power, and θ > 0 makes it the intended positive inverse power. The existing Mathlib ENNReal tsum lemmas have no extra summability hypotheses. No division by zero or coercion discrepancy occurs.

**Verification and limits.**

[scratch/inspect.lean](/home/ubuntu/aklt/reports/TS_REC_08/scratch/inspect.lean) imports the existing compiled module, prints all eight elaborated statements, and evaluates the diamond cardinality at `(0,0)` and `(-11,7)`. Lean 4.35.0-rc2 exited successfully, printing 12 twice; [inspect.log](/home/ubuntu/aklt/reports/TS_REC_08/scratch/inspect.log) confirms that no unexpected instance arguments appeared. One Lean process was used, with packages symlinked from the repository. No repository modules were rebuilt and no theorem declarations were added.

[scratch/checks.py](/home/ubuntu/aklt/reports/TS_REC_08/scratch/checks.py) records reproducible finite checks in [checks.json](/home/ubuntu/aklt/reports/TS_REC_08/scratch/checks.json): all 1,365 words through length five plus 300 sampled words at lengths 12–14; 36,037 arbitrary-word response pairs; all 154 closed first-hit trails through length eight and their 3,324 response pairs; 16 exact-rational finite regrouping checks; and 538 sampled two-trail instances. Domain preparation produced 58 consistent examples containing D sites; the accepted second trails include 602 D departures. All 61 observed exceptional U departures lay within the asserted diamond; the largest observed exception count was two. Network sampling used square volumes, so it supplements the invariant analysis rather than settling general G by enumeration.

The statements are not globally vacuous. For example, in `G = [-5,5]²`, put c at `(0,0)` with status X and give every other site status U with full kept sets. Take `u=(-1,0)`, `v=(1,0)`, and arbitrary unit pins. The first trail goes west to `e=(-4,0) ∈ S`, and the second goes east from v to `(4,0) ∈ S`; all the terminal-count hypotheses hold. Kernel closed trails exist for C at length two (`north,east`) and B at length four (`north,east,east,south`), with positive response contributions. Empty length-zero cases are the intended boundary cases.
