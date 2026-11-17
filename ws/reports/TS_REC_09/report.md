STATUS: COMPLETE

| Leaf in `AKLT.Blueprint.Rec` | Paper label | Verdict | Difficulty | Finding |
| --- | --- | --- | --- | --- |
| `KernelLengthMajorantStatement` | `l:Mtheta` | TRUE | hard | H2 bounds the exact exposed trail weights; the coefficient and shift bounds have the required constants. |
| `MajorantFiniteStatement` | `l:Mtheta` | TRUE | medium | The series is a constant multiple of `Σ n r^n`, with `r = q / sqrt θ < 1`. |
| `UnshiftedWitnessStatement` | `h:H3` | TRUE | hard | The same finite cutoff rows exhaust the full nonnegative weighted kernel row. |
| `ShiftPowerIncrementStatement` | `l:Mtheta` | TRUE | medium | The power bound holds, including `s = 0`, `n = 0`, and `θ = 1`. |
| `TransportChoiceStatement` | `l:Mtheta` | TRUE | easy | Both epsilon bounds are positive; they give the strict inequalities and the budget. |
| `WitnessPerturbationStatement` | `l:Mtheta` | TRUE | hard | The increment sums to at most `(1-θ) B h_X`; its unshifted premise is for the correct row. |
| `ShiftedRowsRealStatement` | `l:renewal` | TRUE | medium | The finite ENNReal row gives the explicit real `Summable` clause in `RenewalRows`. |
| `FiniteKernelTailDominationStatement` | `e:rec-T1` | TRUE | hard | H2 supplies summability; the finite sum is part of the full nonnegative renewal action. |

All eight leaves are true as written and self-sufficient. No missing premise, corrected statement, contradictory hypothesis, or unintended empty-domain argument was found. Difficulty describes the expected Lean work from the concrete definitions. The routes below use auxiliary facts derivable from those definitions; an unproved sibling `...Statement : Prop` is not assumed to be a theorem.

Audited repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. Exact statements: [NodesKernel.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:43). The paper comparison used the local [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:517), including `h:H3` at line 594, `l:Mtheta` at line 618, `e:rec-T1` at line 858, and `l:renewal` at line 928. No repository files were modified and no proofs were written.

The definition closure was read through the following concrete data:

| Source | Definitions inspected that affect these leaves |
| --- | --- |
| [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:169) | `realKernel`, `shiftedLength`, `kernelMajorant`, `witnessReal`, `witnessRatio`, all four transport constants, `RenewalRows`, `renewalOp` |
| [Defs/Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:9) | Canonical start/centre/targets/incoming direction; `ClosedTrail`; dead/live and response-neighbour sets; response pairs, coefficients, types and shifts; `responseKappa`; exact witness and ceiling; first-visit list, short comparator and ordering; `exposureSum`; contributions, length coefficients, both kernel series, cutoff rows and `PositiveVectorBound` |
| [Defs/Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9) | All rational thresholds/coefficient tables; `DirectionWord`, vertices and bonds; `IsTrail`; incoming/straight/revisit definitions and departure count; both trail weights; `OpenTrailBound` |
| [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8), [Defs/Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:110) | `Plane = ℤ × ℤ`, ambient taxicab distance, compass directions/steps/reversal, neighbours, `PairType` and the actual finite-type instances |
| [Top/Response.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Response.lean:21) | `H3Statement = PositiveVectorBound`, and both conjuncts of `ShiftedWitness` |

For the discussion, write `C = 18094/100000 + 2*(36751/100000) = 22899/25000`, `h_X = witnessReal X`, and `ρ₀ = 993015/10^6`. The vector is exactly `h_B = 1`, `h_C = 5404319552844595/4503599627370496`; hence `min h = 1`, `H = witnessRatio = h_C > 1`. The value `h_C` must not be replaced by the rational `6/5`.

**1. `AKLT.Blueprint.Rec.KernelLengthMajorantStatement` — TRUE, hard.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:43); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:632). `OpenTrailBound CV q` explicitly includes `1 ≤ CV`, `0 < q`, and `q < 1`, as well as its length bound. Thus `q² < θ ≤ 1` implies `0 < θ ≤ 1`.

The outgoing site belongs to the three nonarrival neighbours on a true trail: initial reversal is forbidden explicitly, and an immediate reversal later would repeat an unoriented bond. There are at most two other live sites. With zero, one, or two such sites, the total response coefficient is respectively zero, `β′`, or `α + 2β`, all at most `C`. The ordering contains every first departure once. Every exposure prefix product is at most the full first-visit product because the passage factors are `1000/961` or `200/187`, both greater than one. Multiplying that full product by `trailBaseWeight` gives exactly `trailWeight`, including the revisit factor `1/5`.

The response sites are neighbours of the departure site. The prefix and remaining suffix have lengths `i` and `n-i`, so the ambient shift is at most `n/2+1`. This gives the real-power factor in the majorant. Closed trails form a subset of the H2 class with the same start and incoming direction. At length zero there is no closed trail, and both sides are zero. H1 and H3 are unnecessary.

Proof route, line 1: Bound each trail's finite shifted exposure by `n*C*θ^(-n/2-1)` times the product over all its first visits.  
Proof route, line 2: Multiply by the base weight, identify the H2 trail weight, enlarge to all `IsTrail` words, and apply H2 and nonnegative finite-sum conversion to ENNReal.

Lean traps: use `Real.rpow` for the half-integer exponent and `zpow` for the actual integer shifts, with a positive base. The `n/2` in the majorant is real division. Positivity must be established before moving finite rational/real sums through `ENNReal.ofReal`. Treat response pairs as unordered two-element `Finset`s; counting ordered pairs would double the beta terms. A permutation result for `mergeSort` is enough for the majorant; its comparator's optimization property is irrelevant here.

**2. `AKLT.Blueprint.Rec.MajorantFiniteStatement` — TRUE, medium.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:50); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:656). The available hypotheses give `r = q / sqrt θ` strictly between zero and one. For every natural `n`, the majorant equals `(C*CV/θ) * n * r^n`. Its nonnegative series therefore has finite value `(C*CV/θ) * r/(1-r)^2`. The term at `n=0` is zero. This leaf uses no trail combinatorics beyond the scalar inequalities already included in H2.

Proof route, line 1: Use positive-base real-power identities to rewrite the majorant as a constant multiple of `n*r^n`, and derive `0 < r < 1` from `q² < θ`.  
Proof route, line 2: Apply weighted-geometric summability and `Summable.tsum_ofReal_ne_top` to get the required ENNReal finiteness.

Lean traps: prove `θ > 0` before using `sqrt θ`, inverse powers, or `rpow` identities. Finiteness is an ENNReal conclusion, so the real convention that a nonsummable `tsum` is zero cannot establish it. The local Mathlib has `hasSum_coe_mul_geometric_of_norm_lt_one` and `Summable.tsum_ofReal_ne_top`.

**3. `AKLT.Blueprint.Rec.UnshiftedWitnessStatement` — TRUE, hard.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:56); [paper equivalence](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:594). H3 is an inequality for **every** finite true-trail length cutoff, rather than a claim about a single numerical prefix. Its `closedContribution` uses the identical dyadic witness and cutoff-twelve ordering used by the kernel coefficients. Linearity of `exposureSum` in its reward identifies the weighted sum of the type/shift coefficients with the closed contribution at each length. Every response pair has exactly one type and one natural shift, so none is lost or duplicated.

The nonnegative full row is the supremum of these cutoff sums. The zero-length contribution is zero; the start differs from both targets. H3 therefore bounds that full row without H2 or any prior real summability assertion.

Proof route, line 1: Commute the nonnegative ENNReal length/type/shift sums and partition each finite response-pair sum to recover `closedContribution`.  
Proof route, line 2: Remove the zero-length term and take the supremum of the `Finset.Icc 1 R` cutoffs bounded by H3.

Lean traps: `Icc 1 R` includes its right endpoint, whereas `range R` does not. Account for this and the zero term when using `ENNReal.tsum_eq_iSup_nat` or `ENNReal.tsum_le_of_sum_range_le`. `∑ Y : PairType` is a finite sum over the concrete two-element `Fintype`. ENNReal regrouping does not require real `Summable`. Preserve the exact rational-to-real witness casts and the same ordering throughout.

**4. `AKLT.Blueprint.Rec.ShiftPowerIncrementStatement` — TRUE, medium.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:63); [paper estimate](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:678). The hypotheses imply `0 < b < θ ≤ 1` and `b < 1`. For positive integer `s`, the finite geometric identity expresses `θ^(-s)-1` as `(1-θ)` times the sum of `θ^(-k)` for `1 ≤ k ≤ s`. These terms are nonnegative and bounded by `b^(-s-1)`. The assumption `s ≤ n+1` then gives the displayed, slightly looser bound. When `s=0` or `θ=1`, the left side is zero; `n=0` allows exactly `s=0,1` and causes no failure.

Proof route, line 1: Obtain `0 ≤ θ^(-s)-1 ≤ (1-θ)*s*b^(-s-1)` from a finite geometric identity or the mean value theorem, treating `s=0` separately.  
Proof route, line 2: Use `0 < b < 1` and `s ≤ n+1` to bound the remaining factor by `(n+1)*b^(-n-2)`.

Lean traps: the exponents are in `ℤ`; `-(n : ℤ)-2` does not truncate at zero. `n+1` multiplying the bound is real. Monotonicity reverses when comparing exponents of a base strictly between zero and one. Neither `b=0` nor `θ=0` is admitted.

**5. `AKLT.Blueprint.Rec.TransportChoiceStatement` — TRUE, easy.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:70); [paper constants](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:662). H2 supplies all scalar premises needed: `CV ≥ 1` and `0 < q < 1`. For `b=(1+q)/2` and `r=q/b`, one has `0 < q < b < 1`, `0 < r < 1`. Consequently the exact `transportB` is positive. Both terms defining `transportEpsilon` are strictly positive. Its first upper bound gives `b < transportTheta < 1`, and `q² < q < b` supplies the required lower bound. Its second upper bound gives the budget with `transportRho=(1+ρ₀)/2`. The exact ceiling satisfies `0 < ρ₀ < 1`.

Proof route, line 1: Unfold the constants and establish `H > 0`, `CV > 0`, `0 < q < b < 1`, `0 < r < 1`, and `B > 0`.  
Proof route, line 2: Apply the positivity and two upper bounds of the minimum defining epsilon to obtain the strict inequalities and `ε*B ≤ (1-ρ₀)/2`.

Lean traps: justify the signs of `b`, `1-r`, `min h`, and `B` before clearing denominators. In particular `q=0`, which would make `B=0`, is excluded by H2. No stronger lower bound on `q` or `CV` is needed. All divisions in the choice are real; the data for `ρ₀` and `h` begin as rationals.

**6. `AKLT.Blueprint.Rec.WitnessPerturbationStatement` — TRUE, hard.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:80); [paper increment](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:686). With `b=(1+q)/2`, its hypotheses imply `q² < q < b < θ ≤ 1`. Thus the H2 finiteness estimate applies at both `θ` and one. For the fixed row `X`, the increment divided by `h_X` is bounded length by length by `(1-θ)*H*C*CV*n*(n+1)*b^(-n-2)*q^n`. The sum over both output types uses the **total** response coefficient bound `C`, so there is no extra factor for the two types. The weighted-geometric identity for `n(n+1)r^n`, with `r=q/b`, gives exactly `(1-θ)*transportB CV q`.

The explicit unshifted premise is for this same row `X` and is sufficient. Other rows' unshifted inequalities, H3, and a contraction premise `ρ<1` are unnecessary for this leaf. At `θ=1` the increment vanishes and the budget is just `ρ₀ ≤ ρ`.

Proof route, line 1: Form the nonnegative shifted-row increment and bound it using `s ≤ n+1`, the scalar power estimate, the H2 length argument, and `h_Y/h_X ≤ H`.  
Proof route, line 2: Sum the `n(n+1)(q/b)^n` majorant, add the supplied unshifted row bound, and apply `ρ₀+(1-θ)B ≤ ρ`.

Lean traps: splitting the real increment as a difference of two series needs their summability first. Alternatively, work throughout with the nonnegative increment series in ENNReal and use the pointwise identity `θ^(-s)=1+(θ^(-s)-1)`. A factor `1-θ=0` at `θ=1` must not conceal an infinite series; the geometric increment majorant is finite independently. Do not apply an individual-entry majorant to each output type and then accidentally double `C`.

**7. `AKLT.Blueprint.Rec.ShiftedRowsRealStatement` — TRUE, medium.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:92); [paper operator convention](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:947). `Top.ShiftedWitness` explicitly gives finite shifted entries and a finite upper bound for the weighted row. Each shift factor `ENNReal.ofReal (θ^(-s))` is finite and strictly positive. A term of a finite shifted entry cannot therefore hide an infinite `shiftKernel`. The witness is positive by its concrete definition.

Regroup the ENNReal row as a sum over `PairType × ℕ`. Its bound by `ENNReal.ofReal (ρ*h_X)` makes the entire sum finite. This establishes genuine summability of the real terms and permits transfer of the exact weighted row inequality. It supplies all four clauses of `RenewalRows`: nonnegative coefficients, positive witness, weighted `Summable`, and the bound. H2 and H3 are not missing hypotheses.

Proof route, line 1: Derive finiteness of each `shiftKernel` from the finite shifted entries, and regroup the bounded weighted ENNReal row over `PairType × ℕ`.  
Proof route, line 2: Apply `ENNReal.summable_toReal` and `ENNReal.tsum_toReal_eq`, identify the nonnegative real factors, and transfer the inequality and positivity clauses.

Lean traps: `ENNReal.toReal ⊤ = 0`; coefficient nonnegativity alone is therefore no convergence argument. Prove finiteness of the **whole** weighted sum for `ENNReal.summable_toReal`. In this Mathlib version `ENNReal.tsum_toReal_eq` takes pointwise finiteness, which by itself does not prove summability. Reindex the finite type sum and natural shift sum as the product index used in `RenewalRows`.

**8. `AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement` — TRUE, hard.**

[Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesKernel.lean:100); [paper finiteness assertion](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:858). H2 at `θ=1` gives finite total unshifted row mass. For example, applying the entry estimate to the two output types bounds it by `2*C*CV*q/(1-q)^2`. Nonnegativity and finite row mass justify identifying `realKernel X Y s` with the real sum of the rational length coefficients. The uniform bound `0 ≤ F ≤ 2` then makes the full real renewal action summable. Its regrouping by length, type, and shift dominates the displayed finite subcollection.

There is no condition on the sign of the depth `d`; both sides evaluate the same function on `ℤ`, including negative arguments. There is no need to assume `F` is constant below zero. `N=0` gives zero on the left and a nonnegative right side. The shift cutoff contains `0` through `n+1`; all nonzero length-`n` coefficients are supported there. H3 is unnecessary, and the statement intentionally isolates the summation step from the preceding domain-to-trail comparison in the paper.

Proof route, line 1: Derive finite unshifted row mass from the H2 length estimate, identify the real coefficient series, and establish summability of the action on bounded nonnegative `F`.  
Proof route, line 2: Regroup that nonnegative summable series and bound its finite `range N`, `range (n+2)` part by `renewalOp realKernel F X d`.

Lean traps: the printed term `F Y (d-s)` elaborates as `F Y (d-(s : ℤ))`, matching `renewalOp`; there is no natural subtraction. The finite left side uses rational coefficients cast to `ℝ`, while the right side uses `.toReal` of ENNReal series, so equality of the coefficient representations requires finiteness. Prove real summability before applying `sum_le_tsum` or commuting real series. `range (n+2)` includes `n+1`.

The common instance/decidability checks found no dropped premise. `PairType` and `Compass` have concrete global `Fintype` instances with two and four constructors. Consequently each `DirectionWord n = Fin n → Compass` is genuinely finite. `DirectionWord 0` has one element; its closed-trail predicate fails because the start is neither target. Classical decidability is used for the closed-trail condition, filters, and type predicates inside the supplied noncomputable definitions. A writer may use `classical` when unfolding them; no mathematical decidability hypothesis must be added. Rational-to-real casts preserve the exact finite data, and `ENNReal.ofReal` preserves these sums only after the relevant nonnegativity facts are supplied.

Validation artifacts are retained in [scratch/Inspect.lean](/home/ubuntu/aklt/reports/TS_REC_09/scratch/Inspect.lean), [scratch/lean_inspection.log](/home/ubuntu/aklt/reports/TS_REC_09/scratch/lean_inspection.log), [scratch/check_cases.py](/home/ubuntu/aklt/reports/TS_REC_09/scratch/check_cases.py), and [scratch/case_checks.json](/home/ubuntu/aklt/reports/TS_REC_09/scratch/case_checks.json). The Lean inspection imported the existing compiled module using Lean `v4.35.0-rc2`, printed all eight definitions and the main premise definitions, checked the relevant Mathlib interfaces, and evaluated the exact constants and finite-type cardinalities. It exited successfully. It contained no proofs and used one Lean process; the package link is under the scratch directory.

The Python checks used `Fraction` arithmetic throughout: all open trails from the canonical start/incoming direction through length 10 (including 45,069 at length 10); all 452 B and 450 C closed trails through length 10; and one explicit length-14 trail for each type to exercise the longer-trail ordering. They checked the response coefficient bound, both shift bounds, exposure and weighted type/shift regrouping identities, finite length majorants, finite row increments, and finite renewal-action regrouping with negative depths and empty cutoffs. The finite H2 sums at `CV=10, q=certifiedRate` and the H3 cutoff-ten rows also passed. The latter rows were approximately `0.3372431381` for B and `0.5963808776` for C; these finite checks are not assertions about the untested infinite tails. A further 21 exact scalar transport choices and 5,292 shift-power cases passed, including `θ=1`, `s=0`, and `n=0`. The parameter samples test the scalar consequences of H2; they do not assert H2 for arbitrary sampled `CV,q`.
