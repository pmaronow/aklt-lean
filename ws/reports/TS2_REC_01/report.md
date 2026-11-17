STATUS: COMPLETE

All eight leaves are **TRUE** as written and self-sufficient. No missing premise, counterexample, or unintended vacuity was found. No statement change is needed.

| Leaf | Paper label | Verdict | Difficulty | Assessment |
|---|---|---|---|---|
| [AKLT.Blueprint.Rec.LocalMixtureStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Local.lean:18) | `l:local` | TRUE | hard | Common nonnegative mixture; extra tip bonds use effective mean zero. |
| [AKLT.Blueprint.Rec.CoveredRatioStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Local.lean:32) | `l:local` | TRUE | hard | H1 transfers to the actual post/pre quotient; denominators are positive. |
| [AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Local.lean:41) | `l:response-typed` | TRUE | hard | Integrating the unpinned departure and cancelling its positive removed-site normalizer gives both lower bounds. |
| [AKLT.Blueprint.Rec.LegacyCoverComparisonStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Local.lean:55) | `d:pattern` | TRUE | medium | Reuse the frozen witness; actual nonremoved endpoints lie in G. |
| [AKLT.Blueprint.Rec.BoundaryExampleCoveredStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Local.lean:64) | `l:local` | TRUE | easy | The existing concrete pattern satisfies the shared matcher, including the boundary corners. |
| [AKLT.Blueprint.Rec.OnePointPointwiseStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Walk.lean:22) | `l:onepoint` | TRUE | hard | Admissible prefixes and at most twelve U exceptions yield the same product bound for both pin choices. |
| [AKLT.Blueprint.Rec.OnePointSumStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Walk.lean:34) | `l:onepoint` | TRUE | hard | Stopped words embed in H2; the protected distance is finite and the geometric tail has the stated constant. |
| [AKLT.Blueprint.Rec.CoveredClosureStatementV2](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Closure.lean:18) | `l:closure` | TRUE | hard | The normalized consistent-pair prefix invariant supplies a shared covered pattern at each U departure. |

The audit is against repository commit `c5280ad0093d975dad9fda355e71acd980b74c65`. Difficulty estimates include deriving the necessary moment, positivity and trace consequences from the stated data; an unproved sibling leaf is not being treated as an extra hypothesis.

The mathematical sources are the finite-moment and three-field arguments in [sec2-moments.tex](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126), the covering construction in [sec6-walks.tex](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:546), the one-point estimate in [sec6-walks.tex](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:695), and the closure and integrated-response arguments in [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:61) and [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:398).

The custom definitions were traced through the following files:

- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): integer plane, directions, rotations via `Response.lean`, distances, neighbours, internal bonds, original legs, original protected layer and square.
- [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8) and [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:8): unit vectors, the twelve icosahedral atoms, the zero atom, U/D weights, finite site functionals and independent original-leg pins.
- [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10): active sites, two-sided presence, local/auxiliary/ordinary/consistent rules, partitions and expectations, admissible starts, trace operations, coefficients and quotients, and response-pair geometry/data.
- [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:8): rational thresholds/inverses, finite direction words, prefix vertices, unoriented bond injectivity, incoming directions, departure-count revisits, rational trail weights, H2 and stopped-word enumeration.
- [Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:8) and [Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:24): all thirteen template sites, tips, corners and twenty slots; covered rules, template bonds and current/next functionals; H1, removal, integrated I/J and the shared matcher.
- [Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:12), [Counterexample.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Counterexample.lean:8), and [Top/Response.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Response.lean:9): the frozen matcher, `Departure`, normalization/prefixes, finite stopped sum and sum of maxima, distance/constants, `PairData`/`PairSetup`, the boundary example and exact semantic H1 premise. `uncoveredCountV2` was checked in [NodesV2Walk.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesV2Walk.lean:9).

**Cross-cutting Lean checks.** `AKLT.Blueprint.Rec.CoveredDepartureV2` and `AKLT.Defs.CoveredDepartureV2` are different predicates. Only the legacy-comparison premise uses the former. All eight targets elaborate as closed propositions. Lean inspection confirms the `Departure` auxiliary/start/present fields and the inherited `PairSetup.pair` and `interior` fields are retained; no required instance argument was silently dropped.

`InternalPresent` explicitly permits either bond orientation. The shared matcher equates presence only between non-tips, and requires only actual-present implies cover-present at tips. It does not match external kept directions or inactive flags. Those choices are sufficient because partition functions depend on present bonds and unchanged original legs. Every external slot at a nonremoved pattern site is included irrespective of the pattern kept flags; absent corner factors must therefore be filled by the zero-field splitting identity.

`Network.partition` and `patternFunctional` sum over finite dependent functions on the active-site subtypes, with `SpinLetter = Option IcoLetter`. X sites are omitted, the extra zero letter has zero U mass, and D has normalized mass `2/5` at zero plus `1/20` at each of twelve unit labels. No cardinality or normalization mismatch was found. Flattening such indices to `Fin k` and using classical finite enumeration are implementation work, not missing premises.

`localThreshold`, `passageFactor`, `traceCoefficient` and `trailWeight` use rational arithmetic; the asserted estimates use real casts. `exceptionFactor` and `onePointConstant` use real division. Positivity must be established before clearing partition denominators. For `protectedDistance`, finiteness must be derived before using `ENat.toNat`, since `toNat` alone does not preserve infinity. The `i.val - 1` in `wordIncoming` occurs only in the nonzero-index branch. Prefixes take `i.val + 1` vertices, so their live site is exactly departure i. No natural-subtraction or indexing defect was found.

`StoppedNetworkTrail` checks presence in the original network. Evolving presence is a consequence of the degree/start rules and distinct bonds: a D removal destroys no unused present bond. The filter defining `uncoveredCountV2` ranges over every `Fin n` departure, including late exceptions, with classical decidability. The maximum remains inside the stopped-word sum.

Empty-volume data cannot supply an admissible active start or a response pair. A zero-length one-point stopped trail would require its start both inside and outside the original protected layer, so that class is empty as intended. Closure at n = 0 has no departure indices. These local empty cases do not make the full leaves vacuous: the boundary example and sampled consistent domains have actual positive-length stopped trails.

**LocalMixtureStatementV2 — TRUE (hard).**

Departure supplies Auxiliary, an interior active start and a present outgoing bond. The radius-two template therefore lies in G and has no original legs at its centre or nearest neighbours. The shared matcher gives exactly the non-tip internal factors and retains every actual tip bond. On each finite outside-spin fibre, integrate actual tips, realize their means (or zero for an added cover bond) by three unit fields, and split all eight corner ball/zero fields into antipodal unit fields. This gives the same finite nonnegative weights for current and next. Lean traps: global weights need not sum to one; tips are not matched by status or kept set; finite dependent spin sums require reindexing; the straight/type equivalence follows from injectivity of the rotated chart.

Two-line proof route:

1. Freeze the finite outside spins and replace each tip by a covering U tip with its actual effective mean, or zero if only the cover bond exists, absorbing positive normalizer ratios into common weights.
2. Resolve all corner slots by two antipodal unit fields and flatten the finite fibre/slot index into Fin k; the same terms represent both partitions and preserve straight versus turn.

Fix: none.

**CoveredRatioStatementV2 — TRUE (hard).**

The common nonnegative covering mixture transfers H1 to Z_current >= c Z_next. Auxiliary gives positive finite-network normalizers and the interior-start hypothesis removes original legs at the departure site; 0 < c, so the actual step quotient is at most 1/c. No consistency or external-kept matching premise is missing. Lean traps: stepRatio is the post/pre quotient, and passageFactor is a rational inverse cast to the reals; positivity is required before clearing denominators.

Two-line proof route:

1. Carry out the common covering-mixture argument and apply H1 term by term, using north iff outgoing = incoming to choose c.
2. Use positive partition normalizers and positive localThreshold to divide Z_current >= c Z_next into stepRatio <= passageFactor.

Fix: none.

**CoveredIntegratedLowerStatementV2 — TRUE (hard).**

The covering argument yields Z_current >= c Z_next. With exactly two or three distinct present neighbours, integrating the unpinned U departure gives Z_current = Z_removed I2 and Z_next = Z_removed, or Z_current = Z_removed I and Z_next = Z_removed J. The removed-network normalizer is positive under the inherited degree bounds, so cancellation gives both conclusions. All needed interior and Auxiliary hypotheses are fields of Departure. Lean traps: the finite neighbour-set equalities alone allow duplicated entries, but the explicit inequalities exclude them; localThreshold is cast from Q to R; responseI2 is Rec-local while responseI/J are in Defs.

Two-line proof route:

1. Transfer H1 through the covering mixture to the unnormalized current/next partition inequality.
2. Integrate the departure spin in the two- and three-neighbour cases and cancel the positive departure-deleted partition function; this yields I2 >= c and I >= c J.

Fix: none.

**LegacyCoverComparisonStatementV2 — TRUE (medium).**

The same pattern witness works. Auxiliary.LocalRules forces every nonremoved matched site into G; inside G the frozen equality identifies each kept half-bond, giving the shared non-tip present-bond equivalence and its one-sided tip implication. No consistency assumption on D is needed. Lean trap: the premise is the Rec-local CoveredDepartureV2, while the conclusion is AKLT.Defs.CoveredDepartureV2; InternalPresent allows either orientation.

Two-line proof route:

1. Reuse the frozen pattern and its status/outgoing clauses; use LocalRules to put non-X matched endpoints in G.
2. Expand Present and InternalPresent and transport half-bond membership through the injective rotated chart, treating tips separately.

Fix: none.

**BoundaryExampleCoveredStatementV2 — TRUE (easy).**

boundaryExamplePattern is a witness after the east chart (x,y) -> (y,-x). The entire radius-two template lies in boundaryExampleG; only the canonical arrival (0,-1) is removed. Normalization deletes precisely the centre-arrival flag, and all remaining internal bonds agree. External corner legs impose no matching requirement. Lean trap: boundaryExample_v2_covered proves the Rec-local matcher, not this shared matcher directly.

Two-line proof route:

1. Choose boundaryExamplePattern and unfold the finite template, normalization and east rotation.
2. Check non-tip statuses and internal present bonds; all covering-tip obligations hold, including at the boundary corners.

Fix: none.

**OnePointPointwiseStatementV2 — TRUE (hard).**

Auxiliary, AdmissibleStart and the stopped initially-present distinct-bond trail imply admissible auxiliary prefixes: no unused present bond is destroyed, U has at most three present bonds at departure, and D at most one. U departures are first departures; revisits depart as D. H1 bounds each covered pinned U ratio by the proper passageFactor, while the free ratio is at most one; uncovered U ratios are at most 12/5 and D ratios equal one. At most twelve exception positions give a common product bound for both pin choices and hence their maximum. Lean traps: StoppedNetworkTrail tests presence in the original D, so evolving presence must be derived; uncoveredCountV2 filters all Fin n indices using classical decidability; rational trace/trail weights must be cast; n=0 contradicts the start/stopping hypotheses.

Two-line proof route:

1. Establish admissible auxiliary prefixes and apply the local H1 bound, the uniform 12/5 U bound and the trivial D ratio, matching first departures and revisits to trailWeight.
2. Multiply the common nonnegative majorants, telescope the positive partition quotients, use uncoveredCountV2 <= 12 and then take the maximum of the two ratios.

Fix: none.

**OnePointSumStatementV2 — TRUE (hard).**

The absent incoming bond makes every stopped network word an IsTrail with the designated incoming direction. Pointwise domination applies to every summand, and any such word has length at least the original protected distance. An admissible active start makes G nonempty; an extreme site of finite G belongs to protectedSites G, so that set is nonempty and the ENat distance is finite before toNat is used. OpenTrailBound includes 1 <= CV and 0 < q < 1, justifying the nonnegative geometric tail and 1/(1-q). Lean traps: onePointSum is finite and retains the maximum inside each word summand; its length range includes zero, whose stopped class is empty here; ENat.toNat alone would send infinity to zero, so finiteness must be established.

Two-line proof route:

1. Dominate each finite stopped summand pointwise; use the absent incoming bond to embed its word among the IsTrail words and show length >= protectedDistance G u.
2. Use OpenTrailBound and extend the nonnegative finite length sum to the geometric tail CV*q^d/(1-q), with finiteness of d supplied by a nonempty finite G.

Fix: none.

**CoveredClosureStatementV2 — TRUE (hard).**

PairSetup carries the full ordinary-consistent ResponsePair data, a removed adjacent centre and an interior first endpoint. Normalization removes only the U start flag to that removed centre. Prefix induction preserves mutual active kept flags and full-U/two-kept-D rules off the live endpoint; a live U has precisely its three nonarrival flags, and its arrival site is X or a departed D with two nonpassage flags. Rotation therefore supplies a covered pattern with the actual non-tip statuses and internal bonds; covering tips may add bonds but lose none. No assumption that v is interior or avoided is needed. Lean traps: PairSetup inherits Consistent through PairData.pair; i : Fin n excludes the terminal endpoint, and every departure avoids the original protectedSites even for arbitrary T; flags to X sites and external flags impose no shared matching obligations.

Two-line proof route:

1. Induct along the normalized trace, deriving evolving presence and the kept-set invariant: nonlive U sites are full, nonlive D sites keep two, active flags are mutual, and departed sites never return to U.
2. At each live U departure rotate and copy non-tip statuses and D flags, complete the U flags, and use covering U tips; check the non-tip equivalences and retain every actual tip bond.

Fix: none.

**Validation.** One Lean process imported the compiled target modules and printed the exact eight propositions plus their structure/matcher dependencies, with `autoImplicit=false` and `relaxedAutoImplicit=false`. It exited successfully. No target proof was written or attempted; the inspection source and output are [Inspect.lean](/home/ubuntu/aklt/reports/TS2_REC_01/scratch/Inspect.lean) and [inspect.log](/home/ubuntu/aklt/reports/TS2_REC_01/scratch/inspect.log). Package access uses a scratch symlink to the repository package store, and all generated files are in this report directory.

The deterministic integer/set check [check_geometry.py](/home/ubuntu/aklt/reports/TS2_REC_01/scratch/check_geometry.py) evaluated all 117 boundary-example non-tip/template pairs. It also checked 3,618 stopped trails, 13,145 U departures, 1,490 D departures and 839 D starts across the boundary example and 160 mixed-status consistent domains. At every sampled U departure both matchers accepted the constructed pattern; 5,984 absent actual tip bonds were added by a cover. The checks also verified admissible prefixes, preservation of every unused original present bond, and terminal auxiliary status. Results: [geometry-results.json](/home/ubuntu/aklt/reports/TS2_REC_01/scratch/geometry-results.json).

The single-site check [check_tip_means.py](/home/ubuntu/aklt/reports/TS2_REC_01/scratch/check_tip_means.py) evaluated 2,000 tip replacements under U/D laws with zero through three ball fields, including absent internal bonds. The maximum factor error was 6.66e-16; the maximal actual mean norm was 0.6, and all tested normalizers were positive. Results: [tip-results.json](/home/ubuntu/aklt/reports/TS2_REC_01/scratch/tip-results.json). These floating-point checks are sanity checks; the verdict uses the paper's exact moment and mean-realization argument.

The repository was read only. No sub-agents were launched, and no proofs were added.
