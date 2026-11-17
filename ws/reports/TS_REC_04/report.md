STATUS: COMPLETE

| Leaf | Verdict | Difficulty |
| --- | --- | --- |
| `AKLT.Blueprint.Rec.LogCoefficientMonoYStatement` | TRUE | medium |
| `AKLT.Blueprint.Rec.EightTermRemainderStatement` | TRUE | medium |
| `AKLT.Blueprint.Rec.LogEnclosureLowerStatement` | TRUE | easy |
| `AKLT.Blueprint.Rec.LogEnclosureUpperStatement` | TRUE | easy |
| `AKLT.Blueprint.Rec.TipReplacementStatement` | TRUE | hard |
| `AKLT.Blueprint.Rec.BallSlotConvexityStatement` | TRUE | easy |
| `AKLT.Blueprint.Rec.LocalMixtureStatement` | TRUE | hard |
| `AKLT.Blueprint.Rec.CoveredRatioStatement` | TRUE | medium |

All eight statements are true from their own hypotheses and concrete definitions by the paper's arguments. No premise repair or counterexample was found. The difficulties refer to the indicated routes, allowing reuse of proved supporting results. In particular, the easy enclosure leaves reuse the eight-term remainder result, and the ratio leaf reuses the common mixture. An imported definition named `...Statement : Prop` supplies a proposition, not its proof.

Audited repository revision: `7a3393531c12080d76aefbdab300ac0c2df834b7`. Source statements are in [NodesLogMean.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesLogMean.lean) and [NodesLocal.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesLocal.lean). Paper arguments are [§7, l:log-mean-bounds](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:260), [§6, l:local](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:555), and the supporting [§2, l:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197). No proofs were written and the repository was not modified.

**Definitions traced.** For the analytic leaves, I unfolded `logarithmicMean`, `reciprocalLogMean`, `logMeanLower` and `logMeanUpper` in [Defs/Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:9). For the tip/slot leaves, I traced `Vec3`, `dot`, `normSq`, `UnitVector`, `Status`, `siteFunctional`, `SpinLetter`, `spinWeight`, `spinVector`, `IcoLetter`, `icoVector`, `signValue`, `goldenRatio` and `icoRadius` in [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean). The auxiliary `localProduct` and `localMean` definitions agree with these actual finite functionals.

For the last two leaves, I also traced `Departure` and `CoveredDepartureV2` in [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:16); the network, active-site, present-bond, auxiliary, admissible-start, partition and trace definitions in [Defs/Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean); `PinAssignment` in [Defs/PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9); all template, slot, coveredness, bond, active-spin and partition definitions in [Defs/Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean); `normalizeRotation` and `stepRatio` in [Defs/Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean); `H1Statement` in [Top/Response.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Response.lean:10); `localThreshold` and `passageFactor` in [Defs/Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9); and their lattice dependencies in [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean), including boundary depth, protected sites, original legs and once-counted internal bonds.

**LogCoefficientMonoYStatement — TRUE.** Its hypotheses ensure both arguments of each logarithmic mean are strictly positive, including at `y'`. The reciprocal-mean integral represents the defined diagonal as well as unequal arguments. For an integration parameter `t` in `[0,1]`, put `A=(1-t)*x` and `B=t*y`. The derivative in `y` of the difference integrand has sign given by `t*(1/(5*(A+B)^2)-1/(3*(c*A+B)^2))`, which is nonpositive because `0<c<=1` and both denominators are positive. The stronger lower bound `c>=3/5` causes no problem; it is needed for the sibling x-monotonicity argument.

Route, line 1: Use the positive-variable reciprocal-logarithmic-mean integral, including its equal-argument case, and compare the difference integrand at `y` and `y'`.  
Route, line 2: Integrate the pointwise comparison; continuity on the compact parameter interval follows from strictly positive affine denominators.

Lean traps: a proof of the off-diagonal logarithm quotient alone is insufficient when `c*x=y` or `x=y`. The integration endpoints `t=0,1` also belong to the interval. The constants and divisions here are real.

**EightTermRemainderStatement — TRUE.** The exact residual after the eight odd powers is `2*integral_0^t z^16/(1-z^2) dz`. On `0<=z<=t<1`, it lies between zero and `2*integral_0^t z^16/(1-t^2) dz`, which gives the stated `2*t^17/(17*(1-t^2))`. Thus both the exponent and the factor 17 are correct, even near either endpoint of the permitted interval.

Route, line 1: Integrate the exact finite geometric identity for `1/(1-z^2)`, whose residual is `z^16/(1-z^2)`, from zero to `t`.  
Route, line 2: Evaluate the logarithmic antiderivative and bound the residual using `1-z^2>=1-t^2>0`.

Lean traps: `Finset.range 8` contains `0,...,7`; the last retained power is 15. Lean prints the denominator as `2*↑k+1`, agreeing with the natural odd exponent after casting. All exponents are natural, and `1-t^2` is real subtraction. There is no truncated natural subtraction or infinite-series summability obligation.

**LogEnclosureLowerStatement — TRUE.** For rational `0<s<1`, the substitution `t=(1-s)/(1+s)` gives `0<t<1` and `log((1+t)/(1-t))=-log s`. The defined reciprocal logarithmic mean is `(-log s)/(1-s)` on this domain. Division of the lower residual bound by positive `1-s` gives exactly the cast of `logMeanLower s`.

Route, line 1: Cast the rational hypotheses to the reals, make the substitution, and rewrite the logarithm and off-diagonal reciprocal logarithmic mean.  
Route, line 2: Divide the lower eight-term remainder inequality by `1-s>0` and identify the finite rational expression after casting.

Lean traps: cast the entire rational expression, including powers, finite sums and divisions. Prove the required nonzero denominators before field simplification; `s<1` excludes the diagonal and `s>0` makes its logarithm valid.

**LogEnclosureUpperStatement — TRUE.** The same substitution and positive division transform the upper residual into `2*t^17/(17*(1-t^2)*(1-s))`, precisely the correction term in `logMeanUpper`. The rational denominator grouping and its real cast agree.

Route, line 1: Substitute `t=(1-s)/(1+s)` in the upper eight-term residual and rewrite the logarithm as `-log s`.  
Route, line 2: Divide by `1-s>0`, cast the exact rational correction into the reals, and unfold the upper enclosure.

Lean traps: establish `1+s>0`, `1-s>0`, `0<t<1` and `1-t^2>0` before clearing denominators. Lean's totalized division at zero never enters this domain.

**TipReplacementStatement — TRUE.** Write the actual external product as `W`, its positive normalizer as `A`, and its normalized first moment as `mu`. The explicit second and fourth moments give `|mu|<=3/5` for at most three ball fields under either U or D. Every vector in this ball is realized by a triple of unit U fields. If that triple has normalizer `A'`, the required scale is `A'/A>0`. Equality of the masses and first moments yields the identity for every `v`; no bound on `v` is necessary. The direction of the scale in the statement is correct.

Route, line 1: Obtain positivity and the three-factor mean bound from the degree-four moments, sum-of-squares identity, ball-field mixtures and D contraction.  
Route, line 2: Realize the mean by the continuous aligned-to-120-degree triple path and moment covariance, then use scale `A'/A` in the affine functional.

Lean traps: the icosahedral support is not invariant under every orthogonal rotation. Only the relevant degree-three/four moment expressions are covariant. Include D's positive zero atom (`2/5`) and its `3/5` share of the U law. `k=0` has product one and mean zero, which is realized by a 120-degree unit triple. The witnesses are chosen before `forall v`, as required; they do not depend on the test vector.

**BallSlotConvexityStatement — TRUE.** If `b` is nonzero, let `r=sqrt(normSq b)`, `e=b/r`, and `t=(1+r)/2`. The hypotheses give `0<r<=1`, so `e` is a unit vector and both mixture weights are nonnegative. If `b=0`, any coordinate unit vector and `t=1/2` work. The identity is affine and holds for arbitrary `n`.

Route, line 1: Split the zero case, otherwise normalize by the positive Euclidean length and choose the displayed weight.  
Route, line 2: Check the subtype and interval conditions and expand both sides using bilinearity of `dot`.

Lean traps: `Vec3` abbreviates the plain function type `Fin 3 -> Real`; its usual function norm is the maximum-coordinate norm. Use `normSq` and coordinate sums, or explicitly transport to `EuclideanSpace`, for Euclidean calculations. Do not divide by the length before treating the zero vector. The negative vector need not be bundled again because the statement uses `-e.val`.

**LocalMixtureStatement — TRUE.** Its required geometric and validity facts are already hypotheses through `Departure`: `auxiliary` includes `LocalRules`, `start` places `y` outside the protected layer, and `present` records a genuine outgoing bond. Outside the width-two protected layer, the complete radius-two template is contained in `G`. Its centre and four neighbours have no original legs. The eight radius-two sites have exactly the external directions represented by the twenty slots.

V2 matching supplies the non-tip statuses and internal flags. Its intersection with `G` correctly permits boundary corners with original legs. It deliberately imposes no match on actual tip kept sets. An actual tip has at most three external factors. When the covering rule requires its internal bond but the actual bond is absent, replace it by a zero-mean U tip and retain the actual positive constant; a removed actual tip has constant one. When the covering rule does not require the bond, the actual bond is also absent. These cases make replacement valid without a global consistency assumption on the auxiliary network.

For each fixed outside configuration, the tip normalizers and the outside weight are the same before and after the step. Fill both slots of every corner, using zero fields for absent factors, then expand their antipodal decompositions. The current and next local sums consequently have identical coefficients and identical unit slot choices. Absorb the inverse of the common positive tip replacement scale into each coefficient. The statement asks only for nonnegative weights; their sum need not be one. A finite index exists: with `M` outside active sites, one may use `13^M * 2^8` indices, retaining zero coefficients and inactive-slot choices. The pattern itself can be the same for all indices.

Route, line 1: Split the finite outside-spin sum, integrate and replace all four tips, and expand the eight filled corner slots into antipodal unit choices.  
Route, line 2: Enumerate these finite pairs by `Fin k`, use outside weights times inverse tip scales times corner coefficients, and read the type equivalence from the normalization rotation.

Lean traps: the finite spin coordinates are functions on the finite active-site subtype, not on all of `Plane`. Splitting and reindexing these sums requires subtype/Fintype equivalences and may use classical finite choice. Keep each original-leg pin independently indexed by its leg, even when outside endpoints coincide. Spatial normalization relabels sites and does not require rotating the icosahedral spin support. The rotation sends north to the actual incoming direction; its injectivity gives exactly the stated straight-type equivalence. `Fin 0` is allowed syntactically, but positive current partitions prevent an empty mixture from witnessing this result.

**CoveredRatioStatement — TRUE.** With `c` chosen by `outgoing=incoming`, H1 applied to the common mixture gives `c*Z_next<=Z_current`. The current normalizer is strictly positive from auxiliary validity and the concrete finite spin laws; the original degree bound includes all retained leg factors. Both possible thresholds are positive. The definitions reduce `stepRatio` to `Z_next/Z_current`, and `passageFactor` to the reciprocal of the matching rational threshold. The post-step change is exactly U-to-D at `y` plus deletion of the outgoing bond at both ends.

Route, line 1: Apply H1 to each covered term of the common mixture and sum its inequalities using the nonnegative common weights.  
Route, line 2: Divide using `Z_current>0` and `c>0`, unfold the length-one trace quotient, and cast the rational reciprocal in `passageFactor` to the reals.

Lean traps: `Top.H1Statement` is explicitly assumed here; its truth need not be proved to establish this conditional leaf. Its straight/turn branch must be transported through the mixture's type equivalence. A separate positivity or consistency premise is unnecessary, but the proof of positive current normalizer must actually be supplied or invoked as a proved theorem. Avoid division-order arguments without the strict positivity fact.

**Checks performed.** A single scratch Lean module imported the existing compiled statement layer and printed all eight elaborated statements, `Departure`, and the relevant cast/reciprocal definitions. It compiled successfully with Lean `v4.35.0-rc2`; no proof declarations were added. Read-only package/build symlinks are under `scratch/`. The [inspection source](scratch/Inspect.lean) and [compiler output](scratch/Inspect.log) show the actual binders and proof fields; no relevant instance argument was silently dropped.

The standard-library-only [case-check script](scratch/check_cases.py) passed at 350 decimal digits: all 35 coordinate monomials of total degree at most four for the specified icosahedron; 32 U/D tip cases including `k=0`, zero fields and aligned unit fields, with replacements also tested against unbounded probe vectors; 54 y-monotonicity cases including diagonals; six remainder cases near zero and one; seven rational enclosure cases; all sixteen incoming/outgoing direction combinations; and the exact 13-site/20-slot template geometry. These are supplementary checks, not machine-checked proofs of the universally quantified leaves. The verdicts rest on the definition audit and paper routes above.
