STATUS: COMPLETE

All eight leaves are TRUE as written. No statement correction or additional mathematical premise is needed. Difficulty rates a standalone Lean development from the concrete definitions; the coefficient leaf includes establishing its prefix-status invariant.

| Leaf | Verdict | Difficulty | Paper label |
|---|---|---|---|
| `AKLT.Blueprint.Rec.CoveredIntegratedLowerStatement` | TRUE | hard | `l:response-typed` |
| `AKLT.Blueprint.Rec.BetaPrimeAnalyticStatement` | TRUE | easy | `l:response-typed` |
| `AKLT.Blueprint.Rec.BetaAnalyticStatement` | TRUE | easy | `l:response-typed` |
| `AKLT.Blueprint.Rec.AlphaAnalyticStatement` | TRUE | medium | `l:response-typed` |
| `AKLT.Blueprint.Rec.UStepMomentStatement` | TRUE | medium | `l:stepid` |
| `AKLT.Blueprint.Rec.DStepMomentStatement` | TRUE | easy | `l:stepid` |
| `AKLT.Blueprint.Rec.TraceDynamicsStatement` | TRUE | hard | `d:trace` |
| `AKLT.Blueprint.Rec.TraceCoefficientStatement` | TRUE | hard | `d:trace` |

The audit followed the exact statements and their concrete dependency chains: [Rec definitions](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:15), [geometry](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:9), [site laws and vectors](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9), [original pins](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:10), [networks and tracing](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10), [direction words and stopped trails](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:24), [covered patterns](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:9), [H1](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Response.lean:10), and [logarithmic means and responses](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:9). Helper facts in the routes below are consequences of these definitions. H1 is an explicit premise of the covered leaf; that leaf is classified as the stated conditional, without independently certifying H1.

The conclusions have substantive admissible instances. The analytic hypotheses allow equality at their lower endpoints; the moment formulas allow arbitrary vectors and nonempty index types; and interior auxiliary networks admit positive-length stopped trails. For example, a U square with one adjacent interior site removed and the passage flag toward it erased admits a straight covered departure away from the removed site and a trail to its protected layer. Empty cases are compatible with the formulas rather than making the universal assertions trivial.

**`CoveredIntegratedLowerStatement` — TRUE, hard.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesLocal.lean:52); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:395). Departure already contains Auxiliary, AdmissibleStart, a present out-neighbour, and unit pins. Since y is outside the protected width-two layer, its radius-two template lies in G and neither y nor its immediate neighbours has original legs. CoveredDepartureV2 matches all non-tip statuses and kept directions inside G; directions leaving G are original leg factors in the external corner slots. The paper tip replacement and corner-slot convex expansion give Z_current >= c*Z_next under H1. Integrating y gives (I2,1) or (I,J), with the same strictly positive deleted-site normalizer, so the claimed integrated inequalities follow. No ordinary/consistent-domain premise is needed beyond the local matching and Auxiliary.

Proof route: Condition on outside spins, replace actual tips and fill corner slots with a common nonnegative mixture, then apply the given H1 termwise to get Z_current >= c*Z_next.  
Integrate the U departure spin in the two/three-neighbour cases and cancel the common positive removed-site partition, obtaining I2 >= c or I >= c*J.

Lean checks: Unpack all proof fields of `Departure`; they supply auxiliary validity, admissibility and the present outgoing bond. Use `CoveredDepartureV2`, including its intersection with `G`: outside directions are original legs, whose pins remain in `Network.partition`. The threshold is a rational cast to a real. Rotation sends canonical north to `incoming`, so pattern straightness equals `outgoing = incoming`. Cancellation uses the positive removed-site partition; positivity of `J` is also derivable (even the coarse bound `J ≥ 4/5` suffices). Classical finite choices in the mixture introduce no additional hypothesis.

**`BetaPrimeAnalyticStatement` — TRUE, easy.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesLocal.lean:65); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:497). The hypotheses imply It >= c > 0 and I0 >= 1 > 0. The logarithmic mean is positive and increasing on positive arguments, including its explicitly defined diagonal; hence its reciprocal decreases. No bound c <= 1 is needed.

Proof route: Compare logarithmicMean c 1 <= logarithmicMean It I0 using positive-argument monotonicity.  
Take reciprocals of positive quantities and divide by 3; unfold reciprocalLogMean.

Lean checks: `logarithmicMean` has an explicit diagonal branch. Handle equal arguments before clearing a logarithm difference; a denominator sign cannot be assumed for unequal arguments until their order is known. All divisions here are real, and `0 < c` also makes `It` strictly positive.

**`BetaAnalyticStatement` — TRUE, easy.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesLocal.lean:71); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:480). With a = 116/125, c >= 3/5 implies c > 0, Jt >= a > 0, It >= c*Jt >= c*a > 0, and I0 >= J0 >= 1. Monotonicity therefore gives the stated bound. The hypothesis c <= 1 is stronger than this leaf requires, but harmless.

Proof route: Derive It >= (116/125)*c > 0 and I0 >= 1 from the given inequalities.  
Compare logarithmic means with ((116/125)*c, 1), then invert and divide by 3.

Lean checks: Infer positivity before reversing inequalities under reciprocals. The fractions `3/5` and `116/125` are real in this statement. The two lower bounds on `Jt` and `J₀`, together with `c > 0`, supply every required positivity fact.

**`AlphaAnalyticStatement` — TRUE, medium.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesLocal.lean:78); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:480). All four logarithmic-mean arguments are positive from the stated lower bounds. Lowering It to c*Jt and I0 to J0 increases only the positive reciprocal-mean term, leaving the subtraction fixed. For 3/5 <= c <= 1, G_c(x,y) = 1/(3*L(c*x,y)) - 1/(5*L(x,y)) is nonincreasing in each positive variable, as proved by the paper integral argument.

Proof route: Use positive logarithmic-mean monotonicity to bound the left side by G_c(Jt,J0), keeping the entire subtraction term.  
Apply the two coordinate monotonicities of G_c down to (116/125,1) and unfold reciprocalLogMean.

Lean checks: Keep the same `Jt,J₀` subtraction while lowering `It,I₀`; then compare the entire function `G_c`. Independent bounds on the positive and subtracted terms do not give this sharper estimate. Both conditions `3/5 ≤ c` and `c ≤ 1` support the monotonicity argument, and diagonal values are included.

**`UStepMomentStatement` — TRUE, medium.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:11); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:100). siteFunctional U is exactly the uniform twelve-label icosahedral law, including a zero label of weight zero. For k <= 3 the inserted linear factor gives degree <= 4. The U second- and fourth-moment contractions are reproduced by the residual D products: D has constant moment 1 and second moment dot/5. The unrestricted vectors need no norm hypothesis, and k = 0 gives zero on both sides.

Proof route: Expand the product for k = 0,1,2,3; odd moments vanish and the U second/fourth moments give the linear and triple contractions.  
Expand each residual D product (at most two factors); its constant and second moments reproduce those contractions.

Lean checks: The residual product is a `Finset` product over `Finset.univ.erase i`, rather than a product over the full `Fintype`. At `k = 0`, the product on the left is one but its inserted linear factor has mean zero; the outer sum on the right is empty. `SpinLetter` includes a zero atom of weight zero for U and weight `2/5` for D; omitting that D atom would change its constant moment. The vectors are arbitrary real vectors, so positivity of the individual linear factors is unnecessary.

**`DStepMomentStatement` — TRUE, easy.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:19); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:143). The D law is (3/5) times the U law plus (2/5) at zero; its first moment is zero and its second moment is dot/5. The explicit k <= 1 restriction covers precisely the two cases needed and excludes the invalid higher-degree deletion formula. For k = 0 both sides are zero.

Proof route: Split k <= 1 into k = 0 and k = 1 and expand the one possible factor.  
Use the vanishing D first moment and D second moment dot/5; the zero atom contributes zero to the inserted linear factor.

Lean checks: Keep the explicit restriction `k ≤ 1`; this deletion formula does not extend to general larger `k`. The second moment is `1/5`, since each of the twelve nonzero D labels has weight `1/20`. `Fin 0` contributes an empty sum, and the zero atom contributes nothing to the inserted linear factor.

**`TraceDynamicsStatement` — TRUE, hard.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:27); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:50). The initial admissible degree bounds and the explicit prohibition of every nonterminal departure from protectedSites suffice. Arrival deletes a distinct bond, leaving at most three bonds at an unchanged U site, or at most one at an existing D site. A U departure leaves at most two bonds after becoming D; a D departure has no other present bond when it becomes X. Thus no unused original present bond is lost. Protected statuses remain U, kept subsets only shrink, and factor degrees do not increase, so every prefix is Auxiliary. Prefix j takes j+1 vertices and therefore performs exactly j steps, including j=0 and j=n.

Proof route: Induct on prefixes while maintaining Auxiliary, survival of every unused original present bond, and the degree bound at the live endpoint.  
Use bond injectivity and the deleted arrival bond to verify the next admissible departure; deletion at a D departure destroys no extra bond and protected sites are never departed from.

Lean checks: `StoppedNetworkTrail` tests presence in the initial network; presence in each prefix must be established using distinct unoriented `wordBond`s. Use the prohibition of departures from the original `protectedSites G`, which is present even for arbitrary `T`. `prefixNetwork ... j` takes `j+1` vertices and performs `j` trace steps. The terminal prefix is required to be auxiliary, while admissibility is required only at departures indexed by `Fin n`. The initial D bound is at most one, not the general auxiliary D bound of two.

**`TraceCoefficientStatement` — TRUE, hard.** [Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:38); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:90). Under the trail and admissibility hypotheses each evolving departure has status U or D, so the recursive coefficient never takes its zero X branch. Unfolding the vertex-list recursion gives exactly n positive rational factors, 1/3 for U and 1/5 for D. ND filters all of Fin n using the same evolving prefix status as that recursion; factoring 1/5 = (1/3)*(3/5) gives the stated formula without natural subtraction. For n=0 the list is [u], ND=0, and both sides are 1.

Proof route: Derive that each evolving departure is active U or D by the unused-bond/prefix induction, and express the recursive coefficient as the product over Fin n.  
Replace every D factor by (1/3)*(3/5), count exactly the ND filtered indices, and multiply positive rational factors; handle the empty product as 1.

Lean checks: `traceCoefficient` and its displayed factors are rational, and both exponents are natural. `ND` filters the full `Finset.univ : Finset (Fin n)` by evolving prefix status, not initial status or lattice revisit count. Its equality test has the ordinary `DecidableEq Status` instance. The proof must exclude the recursive X branch before asserting positivity. Factoring each D contribution directly avoids natural subtraction and its truncation behavior.

Across these leaves, all finite index types are concrete (`Fin k`, `SpinLetter`, active-site subtypes and compass directions). Lean printed all eight definitions with the intended quantifiers and hypotheses; there is no silently dropped instance parameter. Classical reasoning may be used for finite reindexing and choices without strengthening any proposition.

Validation completed with one Lean process and no proof declarations. [Inspect.lean](/home/ubuntu/aklt/reports/TS_REC_05/lean-scratch/Inspect.lean) imports the existing compiled module and prints the eight statements; [compiler output](/home/ubuntu/aklt/reports/TS_REC_05/lean-scratch/inspect-output.txt) contains the printed definitions, and Lean returned exit code zero. [checks.py](/home/ubuntu/aklt/reports/TS_REC_05/checks.py) passed 600 numerical moment cases, 1,648 numerical analytic inequalities and 45,272 exact-rational trace-prefix checks across 7,680 valid configurations of a lattice square with a tail. The trace cases include 32 prefixes with repeated departures and 24,072 zero-length prefixes. [Recorded results](/home/ubuntu/aklt/reports/TS_REC_05/checks-result.json) distinguish these supporting checks from the general mathematical audit. The repository and manuscript were read only; generated files and package symlinks are confined to this working directory.
