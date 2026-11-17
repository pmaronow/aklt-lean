STATUS: COMPLETE

| Leaf (`AKLT.Blueprint.H3.` prefix) | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| [SuffixWindowValidityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:11) | TRUE | medium | The ten remembered bonds are a translated restriction of the true trail; the next bond is unused. |
| [SuffixWindowLabelsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:18) | TRUE | medium | Slice shifting, incoming direction, and one-way revisit detection have the required bounds. |
| [IncidentBondBudgetStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:29) | TRUE | medium | Arrivals and departures together use distinct bonds among four physical incident bonds. |
| [DepartureBalanceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:36) | TRUE | easy | Every departure after time zero matches its preceding arrival. |
| [KnownSiteMemoryStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:44) | TRUE | medium | A remembered known-site revisit would force three departures, contrary to the explicit budget. |
| [TrueRewardIdentityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:58) | TRUE | medium | The finite live sets and pair coefficients agree exactly. |
| [RewardForgettingStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:67) | TRUE | medium | Enlarging the live set retains existing pairs with equal or larger coefficients. |
| [LocalCoefficientComparisonStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:94) | TRUE | medium | `TrueStepFacts` includes every local fact used by the phase-row comparison. |

All eight leaves are self-sufficient as written. No missing premise, counterexample, or unintended global vacuity was found. No statement correction is required. Individual empty suffix cases are discussed below. The full JSON records, including two-line proof routes and implementation cautions, are in [verdicts.jsonl](verdicts.jsonl).

The audit used repository revision `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository and manuscript were only read. No Lean proofs were written; the scratch Lean file contains imports and signature/definition inspection commands only.

**Sources and unfolding scope.** The exact eight statements and `TrueStepFacts` were read in [NodesDomination.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:11). Their relevant definition chains were traced through the following files, down to finite-set operations, integer-coordinate arithmetic, and rational arithmetic:

| Source | Definitions checked |
| --- | --- |
| [H3/Basic.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/Basic.lean:12) | `trueKind`, `arrivalCount`, `trueDeadSet`, `suffixWindow` |
| [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) | `Plane = ℤ × ℤ`, `Compass`, its `Fintype`, `step`, `reverse`, `neighbours` |
| [Defs/Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:110) | `PairType` and its finite instance |
| [Defs/Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9) | `localThreshold`, `passageFactor`, `alphaBound`, `betaBound`, `betaPrimeBound`, `DirectionWord`, `wordVertex`, `wordBond`, `IsTrail`, `wordIncoming`, `wordStraight`, `departureCount`, `wordRevisit` |
| [Defs/Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:9) | Fixed start/centre/targets/incoming direction, `ClosedTrail`, `deadAt`, `responseNeighbours`, `liveOtherNeighbours`, `responsePairs`, `pairCoefficient`, `responsePairType`, `kernelWitness`, `witnessKappa` |
| [Defs/Automaton.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Automaton.lean:9) | `RawWindow`, `windowArrival`, `windowSuccessor`, `WindowAdmissible`, `StepKind`, `windowKind`, `lastWindowWord`, `MemoryQuotient`, `MemoryQuotient.Correct` |
| [Defs/Stationary.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:10) | `Phase`, `phaseDiagonal`, `phaseTransition`, `relaxedReward`, `stationaryCoefficient`, `FirstDirection`, `SurvivingPrefix` |
| [Defs/Computational.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Computational.lean:50) | `takeWord`, `truePhaseCoefficient` |
| [Mathlib finite powersets](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Data/Finset/Powerset.lean:198) | `powersetCard`; membership means subset with exactly the specified cardinality |

The paper argument is [app-input-contracts.tex, stationary domination](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:555), especially its proof at lines 574–647. The local dead-site and response-pair rules are in [sec7-recursion.tex, definition of the kernel](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:517). The phase and stationary definitions immediately preceding the domination lemma were also compared with Lean. The existing [assembly](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/Assembly.lean:68) was checked to confirm that it obtains the per-word budget from the incident/balance facts and supplies the full `TrueStepFacts` conjunction; no unproved leaf was assumed to establish its own verdict.

**SuffixWindowValidityStatement — TRUE, medium.** For `10 ≤ j < n`, `suffixWindow w j` has letters `w[j-10], …, w[j-1]`. Every window vertex is the corresponding true vertex minus `wordVertex kernelStart w (j-10)`. Translation preserves equality of unoriented bond finsets. Restricting global bond injectivity gives rawness; injectivity against departure `j` excludes every remembered bond. Immediate reversal would duplicate bond `j-1`.

Route, line 1: Establish the slice and vertex-translation identities, then restrict global bond injectivity.<br>
Route, line 2: Compare the next bond with remembered bonds and the preceding bond to obtain both admissibility clauses.

**SuffixWindowLabelsStatement — TRUE, medium.** The successor word shifts the same slice and appends `w i`; this remains valid at `i.val = n-1`, where the new prefix length is exactly `n`. The remembered final direction is the true incoming direction. A positive remembered departure count identifies a true earlier departure with absolute index in `[i.val-10, i.val)`. Consequently a true first departure cannot be a remembered revisit, and its straight/turn test has the same incoming direction. The statement correctly permits forgotten true revisits.

Route, line 1: Compare letters of the shifted slices and identify their final incoming letter.<br>
Route, line 2: Translate remembered departure indices to true indices, then use the one-way implication for first-visit labels.

**IncidentBondBudgetStatement — TRUE, medium.** A departure at `z` and an arrival at `z` are incidences of used bonds. A Compass step is never zero, so a single step cannot contribute to both counts at the same `z`. Distinct departure indices give distinct unoriented bonds by `IsTrail`. The other endpoint of an incident bond lies among the four distinct neighbours of `z`. The virtual incoming bond is not included in either count and is not needed for this bound.

Route, line 1: Inject the disjoint union of counted arrivals and departures into used bonds incident at `z`.<br>
Route, line 2: Inject those bonds into their other endpoints in `neighbours z`, whose cardinality is four.

**DepartureBalanceStatement — TRUE, easy.** For any word, every departure at index `j>0` is preceded by the arrival at index `j-1`. This map is injective, and only the possible departure at index zero remains unmatched. The terminal arrival is included by `arrivalCount`. At `n=0` both counts are zero. No trail assumption is required, even for repeated bonds or immediate reversals.

Route, line 1: Remove the possible index-zero departure and send every remaining counted index `j` to `j-1`.<br>
Route, line 2: Preserve the site condition under that injection and add back at most one initial departure.

**KnownSiteMemoryStatement — TRUE, medium.** The surviving prefix, `L ≤ n`, and `L ≥ 12` give true departures at indices zero and one from `u` and `a=u+d₀`. Any suffix departure at either site is therefore a true revisit. At suffix index `i`, a memory-detected earlier departure has absolute index at least `i.val-10 ≥ 2`. Together with its initial departure and its current departure, this gives three distinct indices counted by `departureCount … n`, contradicting the explicit bound of two. Separately, reusing `{u,a}` would duplicate the time-zero bond.

Route, line 1: Recover the initial direction and initial departure indices zero/one to witness true revisits.<br>
Route, line 2: Exclude memory detection by the three-departure contradiction and exclude initial-bond reuse by bond injectivity.

The current departure is included because the budget is evaluated at `n` and `i.val<n`. A budget only for departures strictly before `i.val` would not directly give the required contradiction. If `L=n`, there is no suffix departure index, as intended. The known-site antecedents are achievable: the checked row-B trails `W³ N³ E³ S⁴ E² N` and `W⁴ N³ E³ S⁴ E³ N`, with `d₀=W` and `L=12`, depart from `u` at time 12 and `a` at time 13 respectively. Both avoid the centre, first hit the target at their endpoints, use distinct bonds, and have at most two departures at every site.

**TrueRewardIdentityStatement — TRUE, medium.** Nonreversal at index zero is explicit in `IsTrail`; at later indices it follows from the two consecutive bonds being distinct. For the reward equality, use the successor identity `wordVertex … (i.val+1) = x + (w i).step`. On any candidate neighbour `z`, membership in `trueDeadSet w i` is exactly `deadAt w i z`; inserting the centre adds no extra dead neighbour because `deadAt` already declares it dead. Both definitions then have identical live sets, two-element pairs, straightness tests, coefficients, and witness factors.

Route, line 1: Derive the successor identity and rule out reversals using the appropriate initial or consecutive-bond clause.<br>
Route, line 2: Identify the live sets extensionally and unfold the equal finite pair sums and coefficients.

The reward equality alone holds even without the trail hypothesis. Both sides insert the outgoing site after excluding dead non-outgoing neighbours. Thus no missing outgoing-liveness premise is concealed here; outgoing liveness for actual completed continuations is a separate geometric fact in the paper.

**RewardForgettingStatement — TRUE, medium.** Enlarging the dead set shrinks the live set. Nonreversal makes the arrival and outgoing neighbours distinct, leaving at most two other neighbours. With zero live neighbours there is no two-element pair. With one there is one outgoing pair with coefficient `β′`. With two the retained outgoing pair receives `β`, and the other outgoing pair and the non-outgoing pair contribute nonnegative terms. All required inequalities hold for the frozen rationals:

| Passage | `α` | `β′` | `β` | `β − β′` |
| --- | --- | --- | --- | --- |
| straight | `145217/10⁶` | `340008/10⁶` | `352782/10⁶` | `12774/10⁶` |
| turn | `150000/10⁶` | `344661/10⁶` | `357549/10⁶` | `12888/10⁶` |

Both witness entries are positive: `h_B=1` and `h_C=5404319552844595/4503599627370496`. Arbitrary remote dead sites and declaring the outgoing site dead do not affect the comparison, since only the other-neighbour live set is subtracted before the outgoing site is inserted.

Route, line 1: Compare the nested live sets by their possible cardinalities zero, one, and two.<br>
Route, line 2: Compare retained pairs using `β′≤β`, then add the remaining nonnegative pair contributions.

**LocalCoefficientComparisonStatement — TRUE, medium.** `TrueStepFacts` explicitly supplies rawness, admissibility, incoming and kind comparisons, the reward bound, current centre/target avoidance, next-centre avoidance, and the known-site conjunction. `Q.Correct` turns admissibility into `allowed=true` and identifies the quotient kind. On a non-revisit window edge it also identifies the quotient arrival, which combines with the supplied true incoming equality.

At a known site the safety conjunction prevents both stationary killing conditions and forces the true row to be the same `1/5` diagonal row. Elsewhere a remembered revisit is a true revisit, so the rows agree without using arrival or reward. For a forgotten true revisit, all relaxed first-visit diagonals are at least `1/3 ≥ 1/5`, and off-diagonal entries are nonnegative. At a true first visit the kinds match, and the reward bound gives the possible phase-change comparison because its multiplier is positive. These cases cover all sixteen phase pairs. A final step into the target is allowed: the stationary target rule tests the current position, not the next one.

Route, line 1: Extract allowed/kind and conditional arrival from `Q.Correct`, then split known-site and true/window revisit cases.<br>
Route, line 2: Use equal revisit rows, `1/5≤1/3` for forgotten revisits, and the reward inequality for first-visit phase changes.

No extra `IsTrail`, `10≤i.val`, `d₀≠east`, or closedness premise is needed here because the pointwise facts used by the comparison are already present. Positivity is a fact about the fixed definitions, not an additional blueprint hypothesis. The representative/successor portions of `Q.Correct` are stronger than this local comparison requires.

**Lean traps checked.**

- Natural subtraction is truncated. The memory identities use `10≤i.val`, while predecessor indices require positivity. `takeWord` pads with east beyond the original length, and `lastWindowWord` pads short words; all relevant slice uses have the needed length bounds. At the final departure the new prefix length is `n`, which is still safe.
- `departureCount` uses `Finset.range (min i n)` and counts departures strictly before `i`; `arrivalCount` uses arrivals at vertices `1,…,n`. In the budget leaf `min n n=n`. Initial and terminal vertices therefore need the stated treatment.
- `wordRevisit` and `wordStraight` are `Bool`; `windowKind` tests a proposition about a natural cardinality. `Q.allowed` is also `Bool`, and `Q.Correct` gives its equality to `true`, sufficient to dismiss the stationary guard `allowed=false`.
- `Plane` is infinite. The arguments count finite index sets and the finite set `neighbours z`; they do not need a `Fintype Plane`. Unoriented bonds and response pairs are finsets, so orientation swaps do not create multiplicity. `powersetCard 2` selects genuine two-element subsets, excluding empty/singleton pairs.
- `Classical` decidability occurs inside the noncomputable definitions, notably `trueDeadSet`, live-neighbour filtering, and `responsePairType`. It supplies no extra mathematical assumption. Lean inspection confirms all eight declarations are closed `Prop`s and retains the explicit `Q.Correct` and `TrueStepFacts` premises; no relevant instance argument was silently dropped.
- All local weights and comparisons here are in `ℚ`. `localThreshold` is positive in both cases, so its inverse has no zero-denominator issue. The witness for C is the exact dyadic rational above; replacing it by `6/5` would change the definitions. No real/rational coercion or infinite sum is used by these eight statements.
- `Q.Correct` preserves arrival only for an admissible non-revisit window edge. An unconditional arrival rewrite would be unjustified. Revisit phase rows ignore arrival and reward, which is precisely why that weaker correctness condition suffices.

**Validation performed.** [validate_sweep.py](validate_sweep.py) uses integer lattice coordinates and Python `Fraction`, with results in [validation.json](validation.json). Every check passed:

- Enumerated all raw trails through length 12: 736,896 extensions, including all 60,092 length-ten and 474,924 length-twelve words. This class also permits the initial direction excluded by the fixed virtual incoming bond, so it contains the relevant true-trail class. Checked the incident/balance invariants during extension.
- Checked 229,184 remembered raw windows and 644,016 eligible suffix steps, including cases where the tested step is the full word's last departure. Checked slice shifting, incoming directions, admissibility, and one-way revisit/first-visit labels.
- Checked all 2,916 comparable dead-set configurations across the twelve nonreversing direction pairs at three translated positions. The configurations include outgoing and remote dead sites. Checked 27,648 scalar phase entries with exact arithmetic, including reward monotonicity and forgotten-revisit comparisons.
- Checked 12,571 reward identities on 1,000 deterministic random words, including nontrails and dead outgoing neighbours, with seed `20261116`.
- Checked the two nontrivial known-site suffix examples above, including the complete closed-trail, surviving-prefix, and budget premises.
- Ran one Lean 4.35.0-rc2 inspection module, [Inspect.lean](Inspect.lean), successfully. It imports the leaf module, checks all eight closed signatures, and prints `TrueStepFacts`, `MemoryQuotient.Correct`, and the local comparison. Output is saved in [lean-inspection.txt](lean-inspection.txt). Packages are read through a workspace symlink to the repository's existing `.lake/packages`; no repository build was run.

The finite diagnostics support the audit and exercise boundary cases. The universal verdicts rest on the definition analysis and the proof routes given above; the diagnostics do not constitute Lean proofs or a new verification of the 3741-state certificate.
