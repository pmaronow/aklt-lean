STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| `AKLT.Blueprint.Rec.TwoLogIdentityStatement` | TRUE | medium | The positive step quotient is `1/I₂`; the response sign agrees with pinned minus free. |
| `AKLT.Blueprint.Rec.AlphaPositiveStatement` | TRUE | hard | The conditional mean intervals give `alpha ≥ 175/5916 > 0`. |
| `AKLT.Blueprint.Rec.AlphaUniformStatement` | TRUE | hard | The crude enclosure gives `alpha ≤ 6061317/33500000 < 18094/100000`. |
| `AKLT.Blueprint.Rec.BetaPositiveStatement` | TRUE | medium | Both `I` arguments are positive, so their logarithmic mean and beta are positive. |
| `AKLT.Blueprint.Rec.BetaUniformStatement` | TRUE | hard | `beta ≤ 340634561/926892330 < 367502/10^6 < 36751/100000`. |
| `AKLT.Blueprint.Rec.ThreeLogIdentityStatement` | TRUE | medium | The positive step quotient is `J/I`; its log difference collects into the stated canonical coefficients. |
| `AKLT.Blueprint.Rec.ReciprocalIntegralStatement` | TRUE | medium | Reciprocal-affine integration agrees with the defined logarithmic mean, including its diagonal. |
| `AKLT.Blueprint.Rec.LogCoefficientMonoXStatement` | TRUE | medium | `3/5 ≤ c ≤ 1` makes the reciprocal-integral expression nonincreasing in positive `x`. |

All eight statements are self-sufficient as written. No missing premise or corrected statement is required. Difficulty estimates include obtaining the needed finite-sum facts from the definitions; the sharp conditional-mean estimates account for the three hard ratings. No proofs were written.

Audit target: repository `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, using Lean `v4.35.0-rc2`. The exact leaves are in [NodesResponse.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:124) and [NodesLogMean.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesLogMean.lean:11). Paper comparisons used [sec6-walks.tex](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:240), labels `d:ratios` and `l:response`; [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:260), labels `e:rec-log-integral` and `l:log-mean-bounds`; and [sec2-moments.tex](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex), labels `l:moments`, `l:finitefacts`, and `l:35`.

The definition trace covered the following in-scope dependencies, rather than relying on comments or on unproved blueprint statements:

| Source | Definitions read |
| --- | --- |
| [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:26) | `Departure`, `pairResponse`, `responseI₂`, `crudeLogUpper`. |
| [Defs/Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:9) | `logarithmicMean`, `reciprocalLogMean`, `removeSite`, `stepRatio`, `removedPairMean`, `responseI`, `responseJ`, `responseAlpha`, `responseBeta`, `responseBetaPrime`. |
| [Defs/Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10) | `Network`, `active`, `Present`, `bonds`, `presentNeighbours`, `LocalRules`, `Auxiliary`, `spins`, `partition`, `expectation`, `AdmissibleStart`, `traceStep`, `traceNetwork`, `traceRatio`. |
| [Defs/PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9) | `PinAssignment`, with one independent unit vector per original leg. |
| [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9) | `Vec3`, `dot`, `normSq`, `UnitVector`, `Status`, `SpinLetter`, `spinVector`, `spinWeight`, `IcoLetter`, `icoVector`, `signValue`, `icoRadius`, `goldenRatio`; also the finite site/product functionals used by the paper's estimates. |
| [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) | `Plane`, `latticeDist`, `Adjacent`, `Compass`, `Compass.step`, `neighbours`, `positiveNeighbours`, `internalBonds`, `originalLegs`, `setDistance`, `boundaryDepth`, `protectedSites`. |

The decisive checks for the six response leaves were these:

- `Departure.auxiliary`, `.start`, and `.present` are actual structure fields. They give a valid auxiliary network, `y` active and outside the original protected layer, and a mutually present outgoing bond. The U hypothesis and the displayed distinct neighbour sets supply the exact two- or three-bond cases. Ordinary consistency and H1 are unnecessary here.
- Being outside the width-two protected layer makes `y` and all its neighbours free of original leg factors. Removing `y` leaves its distinct neighbours nonadjacent, with at most three incident factors each. Thus the paper's conditional independence and mean bound apply to both pin choices, including D neighbours and zero-mass configurations after discarding zero marginal fibres.
- The resulting intervals are `41/50 ≤ I_b ≤ 34/25` and `116/125 ≤ J_b ≤ 134/125`. Each removed pair insertion has separate degree at most four; free positivity therefore supplies `I_false ≥ 1` and `J_false ≥ 1`. These facts are consequences of the encoded network data, not additional assumptions.
- The explicit post-step D law has twelve atoms of mass `1/20` and a zero atom of mass `2/5`, totaling one. Summing out `y` produces `1` in the two-neighbour case and `J` in the three-neighbour case. There is no missing scalar trace mass, and removal leaves every original pin unchanged.
- With `r_ab` defined as pinned minus free, `log(rho_false) - log(rho_true)` has the stated positive `I` difference and negative `J` difference. Equal logarithmic-mean arguments, vanishing pair responses, and either independent I/J diagonal cause no failure.

For the two analytic leaves, positivity of `x,y` keeps the affine denominator bounded away from zero on `[0,1]`. The equality case uses `logarithmicMean x x = x` directly. For monotonicity, the hypotheses also imply `c > 0` and `x' > 0`. At each integration parameter, `cA+B ≤ A+B` and `5c ≥ 3` give the required sign. This covers `c=3/5`, `c=1`, `x=x'`, and crossings of either logarithmic-mean diagonal. Comparing integrands avoids needing to differentiate the piecewise definition of the mean.

Two-line proof routes, using `L_I = L(I_true,I_false)` and `L_J = L(J_true,J_false)`:

| Leaf suffix | Route |
| --- | --- |
| `TwoLogIdentityStatement` | Sum out `y` in both partitions and obtain the positive quotient `rho_b = 1/I₂_b`.<br>Apply the positive divided-difference identity and unfold beta-prime and the pair response. |
| `AlphaPositiveStatement` | Obtain the conditional-mean intervals for I and J from the encoded geometry and U/D moment laws.<br>Bound `L_I ≤ 34/25`, `L_J ≥ 116/125`, giving `alpha ≥ 25/102 − 25/116 = 175/5916`. |
| `AlphaUniformStatement` | Obtain `I_true ≥ 41/50`, `I_false ≥ 1`, `J_b ≤ 134/125`, and apply logarithmic-mean monotonicity.<br>Use the crude enclosure at `41/50`, subtract `25/134`, and compare the exact rational fractions. |
| `BetaPositiveStatement` | Use positive normalizers and the pointwise three-spin estimate `I ≥ 1/2` to make both I arguments positive.<br>Use positivity of their logarithmic mean and take the reciprocal of its positive multiple by three. |
| `BetaUniformStatement` | Use conditioning for `I_true ≥ 41/50` and admissible free pair positivity for `I_false ≥ 1`.<br>Lower-bound `L_I` by `L(41/50,1)`, apply the crude logarithm enclosure, and compare rational bounds. |
| `ThreeLogIdentityStatement` | Sum out `y` under U and post-step D to obtain the positive quotient `rho_b = J_b/I_b`.<br>Expand the log quotient difference using divided differences and collect the three pair responses. |
| `ReciprocalIntegralStatement` | Split `x=y` and evaluate the constant integral there.<br>Off the diagonal, integrate the positive reciprocal affine function and simplify using injectivity of log on positive reals. |
| `LogCoefficientMonoXStatement` | Rewrite each reciprocal logarithmic mean as an integral over its positive affine denominator.<br>Compare integrands for `x≤x'` using `c≤1` and `5c≥3`, then integrate. |

Lean traps to carry into implementation:

- These are closed Props. Inspection of all eight elaborated definitions confirmed their quantifiers; no required typeclass premise was silently omitted. `Departure` retains all three proof fields. `G` is a `Finset Plane`; configuration sums use its active subtype and a finite function type, without a `Fintype Plane` assumption. Deleting `y` requires reindexing that dependent configuration type. Classical decidability is appropriate for protected-site predicates and these finite equivalences.
- `Vec3` is the ordinary function type `Fin 3 → ℝ`. Its default Pi norm is not the Euclidean norm used in the paper. Work with the explicit `dot` and `normSq`, or transport to Euclidean space when using norm lemmas. Arbitrary-function rotational covariance of the twelve-point law is not available or needed.
- `Real.log` and real division are total. Establish positive normalizers, positive I/J values, and nonzero logarithmic differences before cancellation. Split `x=y` in the logarithmic mean. For integrals, establish continuity/integrability on `[0,1]` before applying integral order or linearity lemmas.
- The statement bounds and `3/5` in the analytic leaf are real fractions; `crudeLogUpper` and its endpoint arithmetic are rational. Cast rational bounds to real explicitly. The subtractions here occur in ℝ or ℚ, and the lattice coordinate subtraction is in ℤ; no truncated ℕ subtraction affects these leaves.

Nonvacuity was checked with `G = {-2,…,2}²`, every site in G of status U, every site outside G of status X, and kept flags only on two or three selected centre bonds, at both ends. The centre has boundary depth three and is an admissible U start; all protected sites remain U. Constant unit pins may be assigned to every original leg. Both neighbour-count premises occur, and these examples give I=J=1, beta=1/3, and alpha=2/15. Empty G admits no Departure, but that does not make the universally quantified response claims vacuous. The analytic hypotheses likewise have examples, including `x=y=x'=1`.

Validation: [Inspect.lean](/home/ubuntu/aklt/reports/TS_REC_03/scratch/Inspect.lean) imports the cached target modules and only prints the eight statements, `Departure`, and `logarithmicMean`; Lean exited successfully. The [inspection log](/home/ubuntu/aklt/reports/TS_REC_03/scratch/Inspect.log) confirms the structure fields and statement shapes. [check_bounds.py](/home/ubuntu/aklt/reports/TS_REC_03/scratch/check_bounds.py) passed exact `Fraction` checks and finite checks of both nonvacuity geometries. In particular, the alpha upper-bound slack is exactly `173/33500000`. These checks supplement the mathematical audit; they are not formal proofs of the leaves. Only one Lean process ran at a time, no repository module was rebuilt, and repository status remained clean.

Per-leaf reasons, fixes, routes, and difficulty are recorded in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_REC_03/verdicts.jsonl).
