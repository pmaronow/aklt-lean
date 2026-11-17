STATUS: COMPLETE

| Leaf (`AKLT.Blueprint.Rec.` prefix) | Verdict | Difficulty | Fix |
| --- | --- | --- | --- |
| PairClosureStatementV2 | TRUE | medium | None |
| TerminalExceptionLocationStatementV2 | TRUE | hard | None |
| TerminalExceptionCountStatementV2 | TRUE | hard | None |
| ShortKernelOrderingStatementV2 | TRUE | easy | None |
| LongKernelOrderingStatementV2 | TRUE | easy | None |
| StoppedQuotientSumStatementV2 | TRUE | medium | None |

All six statements are true and self-sufficient as written. The routes below derive the required trace and raw-window invariants from the concrete definitions; they do not assume other open blueprint leaves. Difficulty includes those derivations when a writer starts from only the leaf's hypotheses. Full names, reasons, fixes, and two-line routes are also recorded in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS2_REC_02/verdicts.jsonl).

**Definitions and paper checked.** The exact statements are in [NodesV2Closure.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Closure.lean:28), [NodesV2Ordering.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Ordering.lean:14), and [NodesV2Handoff.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Handoff.lean:41). Their relevant definition chains were read through:

- `PairSetup`, `PairData`, `normalized`, `normalizeStart`, `prefixNetwork`; `Network.ResponsePair`, `Consistent`, `Ordinary`, `Auxiliary`, `LocalRules`, `active`, `Present`, `presentNeighbours`, `HasPairType`, and `removeSite`.
- `Plane`, `Compass`, compass steps/reversal, `latticeDist`, neighbours, squares, original legs, `setDistance`, `boundaryDepth`, and `protectedSites`; `DirectionWord`, word vertices/bonds/incoming directions, `StoppedNetworkTrail`, `traceNetwork`, and `traceStep`.
- `uncoveredCountV2` and the explicitly qualified `AKLT.Defs.CoveredDepartureV2`, including `normalizeRotation`, the template sites/tips/corners, `PatternData` status/kept accessors, `Covered`, `bonds`, and `InternalPresent`. The distinct `AKLT.Blueprint.Rec.CoveredDepartureV2` was also compared.
- `ClosedTrail` and its fixed geometry, `IsTrail`, departure counts/revisits, first-visit lists, straightness, response neighbours/dead sites/live pairs, `pairCoefficient`, `responsePairType`, rational coefficient tables, `kernelWitness`, `witnessKappa`, `passageFactor`, `shortOrderLE`, `kernelOrdering`, and `longOrdering`.
- `MemoryQuotient`, `Correct`, `RawWindow`, `windowArrival`, `windowSuccessor`, `WindowAdmissible`, `windowKind`, `StepKind`, both stopped operators, and `finiteOperatorSum`. The finite pin-assignment and status definitions were checked as well.

The paper comparisons use [l:closure](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:61), [l:terminalcover](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:172), [d:kernel-order](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:575), [d:pattern](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:488), and [l:automaton-quotient](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:320).

**PairClosureStatementV2 — TRUE, medium.** `PairSetup.pair` includes `Network.Consistent`, so full kept sets at U sites, two-element kept sets at D sites, and mutual kept flags between active sites are hypotheses through the structure. Normalization erases only the U start's flag toward the removed centre. Before each departure the live site is interior, since `StoppedNetworkTrail` forbids every protected departure, independently of the chosen `T`.

The definition tests all trail bonds in the initial network. To apply the paper's evolving-network induction, derive that each unused selected bond remains present. A non-start D site has at most two initial incident present bonds: arrival uses one and departure uses the other. An initial D start has at most one. A non-start U site can depart twice, using all four incident bonds through its two arrivals and departures; a U start has at most three, because its centre is removed. Distinct bonds therefore prevent a later step through a site already removed by a D departure.

The prefix induction leaves only the live kept-set defect. At a live U site, every active non-arrival neighbour has its bond to the live site present, by the live site's three kept flags and mutual consistency. Removing the live interior site restores `Consistent`. Each neighbouring D endpoint loses a present bond and has at most one remaining. Two distinct lattice neighbours of the centre are at distance two, and `responsePairType {a,b}` classifies their collinear or diagonal geometry correctly.

Route, line 1: Derive evolving presence and the kept-set/live-site invariant by prefix induction, including the initial D case.  
Route, line 2: Delete the live U site, establish the D endpoint degree bounds, and classify the two distinct neighbours.

**TerminalExceptionLocationStatementV2 — TRUE, hard.** The first stopping set contains both `p.v` and the original protected set. Since its endpoint is protected and `p.v` is not, the first trail never visits `p.v`. Its status and kept set remain unchanged. The first terminal network has one fixed U kept-set defect at the protected endpoint `e`; all original legs remain. Normalizing the interior second start supplies its absent incoming bond, with the incoming direction fixed by the displayed equation.

Repeat the prefix induction during the second trace, retaining `e` as the fixed defect. If `latticeDist y e > 2`, the entire radius-two template avoids `e`. Its non-tip data obey the ordinary kept-set rules except at the live centre, whose three non-arrival flags are exactly the required centre data. A covering witness uses the actual non-tip statuses and D flags, completes external directions of U corners, and uses covering U tips. This satisfies the shared matcher's exact internal-presence comparisons and one-sided condition at tips. The actual external directions need no exact matching. Thus every uncovered U departure is at distance at most two. It is distinct from `e`, because second departures avoid the original protected set.

Route, line 1: Derive the first terminal single-defect invariant, untouched second start, and second prefix invariant with `e` fixed.  
Route, line 2: Construct the shared covering pattern outside distance two; use its contrapositive and protected-site avoidance.

**TerminalExceptionCountStatementV2 — TRUE, hard.** Derive the same localization argument from the hypotheses. A U departure changes that site's status to D; a later departure changes it to X. No trace operation creates a U status. Consequently exceptional U departure indices map injectively to their vertices, even when the trail revisits sites. The punctured radius-two diamond contains four sites at distance one and eight at distance two. This bounds the exact `Finset.univ.filter` used by `uncoveredCountV2`, including exceptions at any trail position.

Route, line 1: Establish the single-defect location bound for every uncovered U index using the trace invariants and pattern construction.  
Route, line 2: Inject these indices into the twelve-site punctured diamond using status evolution, then bound the filter's cardinality.

**ShortKernelOrderingStatementV2 — TRUE, easy.** The ordering equality follows by selecting the `n ≤ 12` branch of `kernelOrdering`. For sortedness, interpret `shortOrderLE` as lexicographic comparison of the extended rational score and path index: a zero reward has infinite score, finite scores compare in ℚ, and equal scores compare indices with `≤`. The Boolean relation is total and transitive, including comparisons of two zero rewards. `List.pairwise_mergeSort` gives the stated `Pairwise`. The coefficient tables and witness are positive, so the finite scores also have the intended positive denominators. This truth does not require the `ClosedTrail` hypothesis.

Route, line 1: Unfold `kernelOrdering` and select its short branch.  
Route, line 2: Establish totality/transitivity of the extended-score/index comparator and apply `List.pairwise_mergeSort`.

**LongKernelOrderingStatementV2 — TRUE, easy.** The `12 < n` hypothesis selects precisely the concatenation defined as `longOrdering`. Both displayed lists filter `firstVisitList`, itself a filter of `List.finRange n`. Filtering preserves strict increasing order of path indices, giving both `Pairwise (fun i j => i.val < j.val)` assertions. This conclusion also holds without `ClosedTrail`. These are intended ordering checks, not vacuity.

Route, line 1: Unfold the two ordering definitions and discharge `¬ n ≤ 12`.  
Route, line 2: Preserve strict index order from `List.finRange n` through the first-visit and straight/turn filters.

**StoppedQuotientSumStatementV2 — TRUE, medium.** `Q.Correct` identifies admissible directions, kinds, projected successors, and arrivals on non-revisit edges. Its allowed-edge condition is sufficient for a termwise comparison of the direction/phase sums. On revisit edges, the explicit arrival-independence hypothesis on `weight` supplies the remaining coefficient equality. Both the raw stopping indicator and reward are explicitly pullbacks on raw windows.

Iterating needs raw-successor closure, which is derivable here. With `m ≥ 1`, the first `m-1` bonds of `windowSuccessor w d` are the translated suffix bonds of `w`; its final bond is the translated appended bond. Old injectivity and `WindowAdmissible` distinguish all of them. The argument includes `m = 1`. Thus every admitted successor satisfies `RawWindow`, and the hypotheses limited to raw states remain applicable throughout induction. Equality of all iterates implies equality of the sum for `j ∈ Finset.range (R+1)`. In particular, `R = 0` uses reward pullback. Reward support on the stopping set, positivity, and convergence assumptions are unnecessary for this finite rational identity.

Route, line 1: Derive raw-successor closure and the one-step pullback identity, using the stopping and weight hypotheses.  
Route, line 2: Induct on iterate exponent on raw states from reward pullback, then sum through `R`.

**Lean traps and edge cases.** The two predicates named `CoveredDepartureV2` differ: these V2 terminal leaves and `uncoveredCountV2` explicitly use `AKLT.Defs.CoveredDepartureV2`. Exact global kept-set matching at tips or external slots would change the obligation. `nonarrivalNeighboursV2` filters active neighbours, so presence must be derived. `removeSite` updates status only. Prefix length `j` takes `j+1` vertices; `i : Fin n` ensures every inspected site is a departure. The subtraction in `wordIncoming` is in its positive-index branch, and the memory subtraction is protected by `1 ≤ m`.

Sorting compares Booleans with `= true`; its tie relation is non-strict, whereas the long lists assert strict index order. The coefficient and ordering arithmetic is exact ℚ, including `5404319552844595 / 4503599627370496`; replacing it by `6/5` changes the data. `Finset` operations count departure indices, not a putative finite ambient plane. Finite direction words have a `Fintype`, while the plane does not need one. Classical decidability is needed for the noncomputable protected-set and predicate filters. There are no silently lost instance hypotheses in the elaborated leaves, and no real/rational coercion affects these conclusions.

Zero-length departure assertions have empty `Fin 0`. The terminal first trace cannot have length zero under its interior-start and protected-endpoint hypotheses. `p = 0` supplies no phase state for the quotient conclusion, but positive-phase instances exist. Likewise, impossible `q = 0` quotient data do not make the universal statement vacuous.

**Nonvacuity.** For the closure and terminal leaves, take `G = [-5,5]²`, centre `c=(0,0)` removed, all other sites U with full kept sets, `u=(-1,0)`, and `v=(1,0)`. Both starts are interior. A first trail `N⁴` ends at `e=(-1,4)`; a second trail from `v`, `N³ W³ N`, ends at `(-2,4)` and has valid distinct initial present bonds. At its U departure `y=(0,3)`, `e` is a non-tip corner and `a=(-1,3)` is a non-tip D neighbour. The missing bond `{a,e}` cannot be reproduced by a covered pattern: its U corner keeps that bond and non-tip consistency forces the active other end to keep it too. The exact internal-presence matcher would then require a bond that the first trace erased. Thus the location leaf's uncovered-departure antecedent is realizable, at distance two.

Short closed trails exist, for example `N E` for type C. Long closed trails exist, for example `N⁶ E² S⁶` of length 14 for type B. For the quotient statement, `m=1`, four classes recording the single direction, and one phase give nonempty correct quotient data.

**Validation.** [audit_checks.py](/home/ubuntu/aklt/reports/TS2_REC_02/audit_checks.py) passed with seed `20261116`. It inspected 582 first and 1,027 second stopped trails across five consistent networks, including U/D starts and targets, a D passage, a diamond volume with boundary corners, and an explicit first trail that revisits its start. It checked 10,891 evolving trace steps, 9,249 response pairs, 6,003 constructed covering witnesses outside the defect diamond, and injectivity of U departures. Separately it exhaustively checked all 11,516 admissible successors of 4,020 raw windows at memories 1–7. These finite checks support the general definition-based arguments above; they do not enumerate all hypotheses of the leaves.

One Lean process checked [inspect_statements.lean](/home/ubuntu/aklt/reports/TS2_REC_02/scratch/inspect_statements.lean), importing the existing single-module dependency graph with Lean `v4.35.0-rc2`. It exited successfully and printed all six elaborated statements, structure/definition signatures, and the merge-sort theorem's exact assumptions; see [inspect_statements.log](/home/ubuntu/aklt/reports/TS2_REC_02/scratch/inspect_statements.log). Package access uses a scratch symlink to the repository's existing `.lake/packages`. No proofs were written and no repository files were modified.
