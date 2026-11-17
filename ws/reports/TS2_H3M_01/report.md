STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty |
|---|---|---|---|
| `AKLT.Blueprint.H3.StationaryCoefficientOffCentreStatementV2` | `d:stationary-walk` | TRUE | easy |
| `AKLT.Blueprint.H3.StationaryCentreZeroOperatorStatementV2` | `l:stationary-local-global` | TRUE | easy |
| `AKLT.Blueprint.H3.StationaryContinuationBridgeStatementV2` | `l:stationary-domination` | TRUE | medium |
| `AKLT.Blueprint.H3.StationaryCertificateBridgeStatementV2` | `d:stationary-certificate` | TRUE | easy |
| `AKLT.Blueprint.H3.StoppedQuotientIntertwiningStatementV2` | `l:automaton-quotient` | TRUE | medium |

All five leaves are true and self-sufficient. No additional premises or statement corrections are needed. This audit used repository branch `main`, commit `c5280ad0093d975dad9fda355e71acd980b74c65`, and Lean `v4.35.0-rc2`. The paper references were read in [app-input-contracts.tex](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:315), including their proof text. The routes below can be carried out from the definitions within each leaf; none assumes another unproved blueprint leaf.

**StationaryCoefficientOffCentreStatementV2.** The [statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesV2Stationary.lean:16) compares definitions that differ only in where they test whether the destination is the centre. V2 puts that test before the known-site branch; the legacy definition puts it after that branch. Under the stated off-centre hypothesis, both destination tests are false and every remaining branch agrees. This matches the repaired operator in `d:stationary-walk`.

Proof route (easy):

1. Unfold both coefficients and split their current-terminal/admissibility and known-site guards.
2. Eliminate the destination-centre tests using the hypothesis; all remaining branches coincide.

Lean traps: The first guard uses `Q.allowed a d = false`; a Boolean condition `if Q.allowed a d` elsewhere means equality to `true`. Preserve the disjunctions' association when simplifying. The unordered bond is a `Finset Plane`. No positivity, quotient correctness, or restriction on the first direction is needed.

**StationaryCentreZeroOperatorStatementV2.** In the [statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesV2Stationary.lean:26), both operators sum over the same absolute directions and next phases. Away from the centre their coefficients agree. At a centre destination, the hypothesis sets `F ψ (Q.successor a d) kernelCentre` to zero. Both products therefore vanish, including a possible nonzero legacy coefficient.

Proof route (easy):

1. Compare each direction/phase summand, splitting on its destination being the centre.
2. Use coefficient equality away from the centre and the supplied zero continuation value at the centre.

Lean traps: The zero-value premise covers every phase and class, including the successor class. The sums use the actual four-element `Fintype` instances for `Compass` and `Phase`; directions are not deduplicated by their successor. When using this equality inside iteration, apply extensionality to all three function arguments.

The restriction on `F` has content. Take memory one with its correct identity quotient, the class with arrival east, `X = B`, `d₀ = north`, `x = kernelStart = (-1,0)`, and an east step in the same phase. The legacy coefficient into the centre is `1/5`, while V2 gives zero. For `F` equal to one at the centre and zero elsewhere, the operator values here are respectively `1/5` and zero. This is a sanity example outside the premise, not a counterexample to the leaf.

**StationaryContinuationBridgeStatementV2.** The [statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesV2Stationary.lean:35) fixes the initial function to `stationaryReward X`. Its targets are `(1,0)` for B and `(0,1)` for C, both distinct from the centre `(0,0)`. The initial reward is therefore zero at the centre. Both operators have zero rows when their current position is the centre, so every reward iterate preserves that property. Operator agreement on this invariant identifies every iterate and their finite sums.

Proof route (medium):

1. Check the two target coordinates and preserve the zero-centre invariant under each operator.
2. Induct on the iterate using agreement on functions zero at the centre, then sum over `Finset.range (R + 1)`.

Lean traps: The sum includes the zero-step reward; for `R = 0` both sides equal that reward. `T^[j]` iterates the function transformer. `Function.iterate_succ_apply'` exposes the outer operator application useful for this induction. The reward's class argument is ignored in its body but its `Fin 3741` type is retained. No `Q.Correct`, first-direction restriction, nonnegativity, or infinite-series premise is needed.

**StationaryCertificateBridgeStatementV2.** In the [statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesV2Stationary.lean:45), `PassesV2` and `Passes` have identical first five conjuncts. The final row differs only in the coefficient supplied to `coefficientCeiling`. Off-centre arguments agree before rounding. At a centre destination, the fifth conjunct sets the natural-number multiplier `C.extended ψ (Q.successor a d) kernelCentre` to zero. Thus the complete rounded row sums agree even when the centre-edge ceilings differ.

Proof route (easy):

1. Retain the first five passing conditions, including their zero extended values at the centre.
2. Compare final-row summands by destination and transfer the unchanged integer inequality.

Lean traps: `coefficientCeiling` returns `ℕ` using `Nat.ceil`, and the row arithmetic is in `ℕ`. The value scale is `2^16 = 65536`; the coefficient scale is `2^48 = 281474976710656`. No division by either is needed. The target equality coerces the stored value and value scale to `ℚ`. An inside site is a subtype of a finite square, while successors use `extended` and may be outside. The centre check is already an equality for `extended`, so no square-membership lemma is needed for the zero multiplier. Neither a ceiling bound nor a finite-data witness is required.

This implication is not globally vacuous. With `q = 1` and every direction disallowed, choose all caps equal to the value scale, stored target values equal to the prescribed scaled terminal rewards, and all other stored values zero. The free and stationary rows are zero and both terminals lie inside the radius-70 square, so the checks are consistent. Such a quotient need not be correct, and correctness is not a premise of this leaf.

**StoppedQuotientIntertwiningStatementV2.** The [statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesV2Quotient.lean:38) supplies all required information. `Q.Correct` matches admissibility, admitted-edge kind, projected successor, and nonrevisit arrival. The separate weight premise handles revisit arrival. Both terminal tests and the reward have explicit pullback hypotheses, including the zero-step term. The supplied successor closure keeps each induction step inside `RawWindow`, where these hypotheses apply. This is precisely the finite operator argument of `l:automaton-quotient` with displayed-state stopping.

Proof route (medium):

1. Establish one-step agreement by matching terminal tests and each direction/phase term, using arrival equality or revisit independence.
2. Induct with all raw starting windows generalized, use reward pullback at zero and closure at successors, and sum through `R`.

Lean traps: `Correct` does not promise arrival equality on revisit edges. Kind and successor guarantees are conditional on admissibility. Pullback hypotheses hold on raw windows, not all words, so the induction must use closure and generalize the starting window. The terminal functions are distinct Booleans depending on phase, memory state, and position; neither pullback may be dropped. All directions remain separate indices, including parallel quotient edges. The existing generic `stopped_pullback` theorem uses `ℝ≥0∞` and a different horizon convention; a direct rational finite-sum argument needs no nonnegativity premise.

The reward-support condition is stronger than the algebraic equality needs but matches stopped-reward semantics. Given explicit successor closure, the memory lower bound is also unnecessary to the algebraic induction. These redundant assumptions do not cause vacuity. For a nontrivial instance, use memory one, its four-class identity quotient, one phase, weight one, and stopping/reward one at `(1,0)`. Starting at `(0,0)` with east arrival, the horizon-one sum includes the allowed east step and is nonzero.

The definition trace covered the following dependencies:

| Group | Definitions inspected |
|---|---|
| Lattice and finite directions | `Plane = ℤ × ℤ`, `Compass`, its `Fintype`, `step`, `reverse`, `neighbours`, `square`: [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8). |
| Pair and fixed geometry | `PairType` and its `Fintype`: [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:110); `kernelStart`, `kernelCentre`, both `kernelTarget` branches: [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:9). |
| Memory and quotient | All six `MemoryQuotient` fields and `Correct`; `RawWindow`, `windowArrival`, `windowSuccessor`, `WindowAdmissible`, `StepKind`, `windowKind`: [Automaton.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Automaton.lean:9). |
| Words and numerical factors | `DirectionWord`, `wordVertex`, `wordBond`, `departureCount`; `localThreshold`, `passageFactor`, `alphaBound`, `betaBound`, `betaPrimeBound`: [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9). |
| Responses and phases | `responsePairType`, exact dyadic `kernelWitness`: [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:47); `Phase`, its `Fintype`, `phaseTerminal`, `phaseDiagonal`, `phaseTransition`, `relaxedReward`: [Stationary.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:9). |
| Stationary operators | `freeCoefficient`, both stationary coefficients, both stationary applications: [Stationary.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:46). |
| Certificates | `certificateRadius`, both scales, `coefficientCeiling`, `StationaryData`, `extended`, `potential`, `Passes`, `PassesV2`: [Stationary.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:76). |
| Rewards and iteration | `stationaryReward` and both continuation sums: [Computational.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Computational.lean:77); function iteration: [Mathlib Iterate.lean](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Logic/Function/Iterate.lean:55). |
| General stopping | `rawStoppedBackwardV2`, `quotientStoppedBackwardV2`: [NodesV2Quotient.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesV2Quotient.lean:12). The older rational pullback and generic nonnegative stopped model were also read for comparison. |

The common response expressions are identical in the compared branches, so their numerical bounds are not additional premises. The C witness remains the exact dyadic `5404319552844595 / 4503599627370496`. Coefficient and continuation equalities are over `ℚ`; certificate rows are over `ℕ`. No real-to-rational identification is involved.

Lean's elaborated declarations retain every explicit hypothesis and index; no required instance argument was silently dropped. Raw admissibility and some finite-set predicates use classical decidability. A writer can use `classical`, which adds no mathematical premise.

`DirectionWord m` is inhabited for every natural `m`, including the singleton empty-word type at zero. Thus `MemoryQuotient m 0` is uninhabited because its project field would map into `Fin 0`. These isolated empty cases do not make any leaf globally vacuous. The quotient leaf excludes memory zero, and `windowArrival` guards its subtraction `m - 1` by positivity. The other four leaves remain valid at memory zero. At `p = 0` the quotient leaf has no starting phase. No unguarded natural subtraction or division-by-zero issue enters the proof routes.

Verification used [scratch/Audit.lean](/home/ubuntu/aklt/reports/TS2_H3M_01/scratch/Audit.lean), which imports the two assigned modules and prints all five elaborated statements and their central definitions. One Lean invocation exited successfully. Its [output](/home/ubuntu/aklt/reports/TS2_H3M_01/scratch/elaborated.txt) also records reductions of both target coordinates, the centre, and the two scales. The scratch file contains declaration inspection and closed reductions, with no new proofs, axioms, or admitted goals. Package access uses a scratch symlink to the repository's existing `.lake/packages`.

The [finite enumeration script](/home/ubuntu/aklt/reports/TS2_H3M_01/scratch/check_small_windows.py) checks actual raw words of memories one through four: respectively 4, 12, 36, and 108 windows. It checks closure on all 472 admitted labelled edges. With two phases, three starting positions, and exact signed-rational weights, it compares iterates and stopped sums at horizons 0 through 3, totaling 3840 cases. At memory four it deliberately changes quotient arrival on all eight windows with only revisit edges. All checks passed; [results](/home/ubuntu/aklt/reports/TS2_H3M_01/scratch/small_windows_results.txt) record the counts. These finite checks support the structural verdicts and are not formal proofs.

[verdicts.jsonl](/home/ubuntu/aklt/reports/TS2_H3M_01/verdicts.jsonl) contains one object per assigned leaf, recorded as the sweep progressed, with two-line routes and empty `fix` fields. No proofs were written, no sub-agents were launched, and the repository was not modified.
