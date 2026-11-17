STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Finding |
|---|---|---|---|
| [AKLT.Blueprint.Rec.CrudeLogEnclosureStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:79) | TRUE | medium | The integrated geometric remainder is exactly the stated rational enclosure. |
| [AKLT.Blueprint.Rec.StepRatioPositiveStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:84) | TRUE | medium | The original and traced auxiliary networks both have positive normalizers. |
| [AKLT.Blueprint.Rec.FreeRatioUpperStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:89) | TRUE | hard | Degree-admissible free pair positivity gives J⁰ ≤ I⁰. |
| [AKLT.Blueprint.Rec.PinnedRatioUpperStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:94) | TRUE | medium | Pointwise I ≥ 1/2 and J ≤ 6/5 give the bound; smaller cases also satisfy it. |
| [AKLT.Blueprint.Rec.DStepTrivialStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:99) | TRUE | medium | The sole unpinned D bond integrates to one before the site is removed. |
| [AKLT.Blueprint.Rec.OneStepTrivialStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:105) | TRUE | medium | The pre-step U bond and isolated post-step D site each integrate to one. |
| [AKLT.Blueprint.Rec.BetaPrimePositiveStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:110) | TRUE | medium | Both logarithmic-mean arguments are at least 2/3, including the diagonal case. |
| [AKLT.Blueprint.Rec.BetaPrimeUniformStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesResponse.lean:117) | TRUE | hard | The three-factor mean bound and free positivity give the required logarithmic-mean comparison. |

All eight leaves are true and self-sufficient as written. No correction or additional mathematical premise is needed. None is vacuous. Difficulty estimates concern formalization from the concrete definitions, including the necessary geometry and finite-sum identities; they do not assert that the other blueprint leaf Props have already been proved.

Audited repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The initial repository status was clean. The source repository was read only throughout this audit. The paper references are Definition `d:domain`, Definition `d:trace`, Definition `d:ratios`, and Lemma `l:response` in [sec6-walks.tex](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:240), together with Lemmas `l:moments`, `l:finitefacts`, and `l:35` in [sec2-moments.tex](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35). No Lean proofs were written.

**Definition trace and inherited hypotheses.**

The exact eight declarations were read from `AKLT.Blueprint.Rec.NodesResponse` and inspected with Lean. Their domain-specific dependencies were followed through:

- [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:25): `Departure`, `crudeLogUpper`, and the two-neighbour notation `responseI₂`.
- [Defs/Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:9): `logarithmicMean`, `reciprocalLogMean`, `stepRatio`, `removeSite`, `removedPairMean`, `responseBetaPrime`, and the local factors `responseI`, `responseJ` used in the argument.
- [Defs/Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10): `Network`, `active`, `Present`, `bonds`, `presentNeighbours`, `LocalRules`, `Auxiliary`, `AdmissibleStart`, `spins`, `partition`, `expectation`, `traceStep`, `traceNetwork`, and `traceRatio`.
- [Defs/PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:10): `PinAssignment`; [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:10): `Vec3`, `dot`, `normSq`, `UnitVector`, the explicit icosahedral vectors and their normalization, `Status`, `SpinLetter`, `spinVector`, and `spinWeight`.
- [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:10): `Plane`, `latticeDist`, `Adjacent`, the compass enumeration and unit steps, `neighbours`, `positiveNeighbours`, `internalBonds`, `originalLegs`, `setDistance`, `boundaryDepth`, and `protectedSites`.

`Departure` is a structure with genuine proof fields `auxiliary : D.Auxiliary`, `start : D.AdmissibleStart y`, and `present : o ∈ D.presentNeighbours y`. These fields retain the hypotheses needed by the paper. In particular:

- `y` is active and outside the original protected layer. Its status is U with at most three present neighbours or D with at most one. Presence of `o` excludes degree zero and implies `o ≠ y`.
- Auxiliary validity bounds each active site's present bonds plus original legs by four, requires kept half-bonds to lie inside the original volume and among physical neighbours, and fixes every protected site's status to U. It allows asymmetric kept sets; actual bonds require both ends to keep them, which is sufficient here.
- An active site outside the protected layer has distance at least three from the original exterior. Thus `y` has no original leg, and each of its neighbours has distance at least two from the exterior and also has no original leg. A neighbour may still be protected: absence of legs is the fact used.
- Removing `y` only deletes bonds. Tracing a U departure deletes the selected present bond and changes U to D, leaving at most two present bonds there; tracing a D departure removes the site. Both operations preserve auxiliary validity and the original leg conventions.

For clarity, the following reasoning uses mathematical intermediate facts from the paper, derived from the explicit finite laws. A definition named `FiniteFactsStatement`, `ThreeFactorMeanStatement`, or another `...Statement` is itself only a Prop and supplies no theorem merely by being imported. No H1/local-pattern bound, consistency assumption, or pin-compatibility assumption is required by these eight leaves.

**Common finite-law and positivity checks.**

The literal weights are U: twelve atoms of mass `1/12` plus a zero atom of mass zero; D: the same twelve atoms of mass `1/20` plus a zero atom of mass `2/5`. Both have total mass one and zero first moment, and their second moments are respectively `1/3` and `1/5`. The active-site sums use these laws and omit X sites. Every spin has norm at most one.

A strictly positive normalizer follows without assuming every configuration has positive weight: choose an icosahedral atom at each active site successively. Its mass is positive under either law. Each original pin or previously assigned adjacent spin forbids at most one of the twelve unit atoms, and there are at most four incident factors. At least eight choices remain, producing one strictly positive summand. This applies to the original, removed-site, and traced networks for either pin choice, and the empty network has its single empty configuration and partition one.

After deleting `y`, each of its distinct present neighbours has lost one bond and has at most three remaining bond factors. A pair insertion adds exactly one degree at each of its two endpoints. All separate degrees are therefore at most four. Expanding free bond products and the inserted scalar product into coordinate monomials gives nonnegative coefficients and nonnegative U/D moment tensors, so every such free pair expectation is nonnegative. This is the degree check required for the free-ratio and beta-prime bounds.

At a U departure with three neighbours `o,f,g`, integrating `y` gives
`Z_pre = Z_removed * I`, `Z_post = Z_removed * J`, where
`I = 1 + (P_fg + P_fo + P_go)/3` and `J = 1 + P_fg/5`, and each `P` denotes the corresponding normalized removed-site pair expectation. With two neighbours the factors are `I₂ = 1 + P_fo/3` and `1`. These are genuine finite-product identities; changing the kept flag at `o` erases only its edge to `y` and leaves every other factor unchanged.

**Individual verdicts and two-line proof routes.**

**`CrudeLogEnclosureStatement` — TRUE; medium.**

For rational 0<s<1, its real coercion has the same strict bounds, so reciprocalLogMean s=(-log s)/(1-s). With t=(1-s)/(1+s), 0<t<1; integrating 1/(1-u^2)=1+u^2+u^4/(1-u^2) over [0,t] and bounding the last denominator by 1-t^2 gives exactly crudeLogUpper s. All denominators are strictly positive.

Route: Rewrite the reciprocal logarithmic mean and use -log s=2*integral_0^t 1/(1-u^2) du.  
Integrate the first two terms and bound the remainder by t^5/(5*(1-t^2)); transport the rational expression through the real cast.

**`StepRatioPositiveStatement` — TRUE; medium.**

Departure.auxiliary supplies the finite degree-four network rules, and Departure.start and Departure.present ensure traceStep is another auxiliary network. At a U departure at most three bonds become at most two after the selected present bond is erased; at a D departure the site is removed. The protected layer is unchanged. All active laws have positive-mass icosahedral atoms, and at most four incident factors exclude at most four of twelve atoms in a greedy choice, so both partition normalizers are strictly positive. stepRatio is their positive quotient.

Route: Show traceNetwork D [y,o]=traceStep D y o preserves auxiliary validity using the admissible degree bounds and the present outgoing bond.  
Apply finite-network strict positivity to the original and traced partition sums, then use positivity of division.

**`FreeRatioUpperStatement` — TRUE; hard.**

Admissibility and the present outgoing bond leave exactly the U degree-one/two/three cases or the D degree-one case. Deleting y leaves at most three bond factors at each distinct present neighbour, so inserting a pair dot product has separate degree at most four. The explicit U/D moments make each free pair insertion nonnegative. Thus for U degree three I0-J0=(2/15)Pfg+(1/3)(Pfo+Pgo)>=0 after normalized averaging; for degree two I0-1=Pfo/3>=0. Factorization gives stepRatio=J0/I0; the D and U degree-one cases have ratio one. All denominators are positive.

Route: Integrate y in each admissible U case and use degree-admissible free scalar-product positivity in removeSite D y to show J0<=I0.  
Divide by the positive I0; use the mass-one identities for D and one-bond U departures.

**`PinnedRatioUpperStatement` — TRUE; medium.**

The departure and its original legs are unpinned because y is outside protectedSites G. For a U site with three present neighbours, all spin norms are at most one, so the sum of their three pair dot products is at least -3/2. Consequently the integrated local factors obey I>=1/2 and J<=6/5 pointwise, and their normalized averages give stepRatio=J/I<=12/5. Two-neighbour U gives I>=2/3 and J=1, hence ratio<=3/2; one-neighbour U and admissible D give ratio one. Auxiliary validity supplies the positive normalizers.

Route: Integrate the unpinned departure and bound the three-neighbour local factors by I>=1/2 and J<=6/5 using the squared-norm identity.  
Average under the positive removed-site law and divide; handle two neighbours by 3/2 and the trivial cases by one.

**`DStepTrivialStatement` — TRUE; medium.**

Departure.start gives an active unprotected D site with at most one present neighbour, and Departure.present forces that neighbour to be o. Such a site has no original leg. Its D law has mass one and mean zero, so integrating its sole bond gives one. traceStep removes y and its outgoing bond; erasing y from the kept set at o changes no other bond. Both partitions are equal and strictly positive, for either pin choice.

Route: Use admissibility and presence to identify the only present bond, and integrate lambda_D(1+n_y dot n_o)=1.  
Reindex the remaining finite product as the traced network and cancel the common positive normalizer for true and false.

**`OneStepTrivialStatement` — TRUE; medium.**

The one-neighbour hypothesis and Departure.present identify {o} as the whole present-neighbour set. Departure.start excludes original legs at y. Integrating the pre-step U site and its single bond gives one; traceStep changes y to D and drops the sole bond, leaving an isolated D site of total mass one. All other bonds and original pins agree, and the common partition is positive.

Route: Integrate the unpinned U departure factor 1+n_y dot n_o, using mass one and zero first moment.  
Integrate the isolated post-step D site to one and cancel the equal positive partitions for both pin choices.

**`BetaPrimePositiveStatement` — TRUE; medium.**

Removing the unprotected y preserves auxiliary validity, hence its pinned and free expectations have strictly positive partition normalizers. Unit-ball support bounds each removed pair mean between -1 and 1, so each logarithmicMean argument 1+P/3 lies in [2/3,4/3]. The defined logarithmicMean is strictly positive on positive arguments, including equal arguments via its explicit diagonal branch. Therefore 1/(3*logarithmicMean(...)) is strictly positive. No H1 or covered-pattern premise is needed.

Route: Bound the two normalized removed-site pair means in [-1,1], giving positive I2 arguments at least 2/3.  
Use positivity of the logarithmic mean, treating its diagonal branch explicitly, and positivity of the reciprocal denominator.

**`BetaPrimeUniformStatement` — TRUE; hard.**

Because y is an active unprotected site, it has boundary depth at least three. The distinct present neighbours f and o are nonadjacent, have no original legs, and after deleting y have at most three remaining factors. On each positive conditioning fibre their independent U/D conditional means have norm at most 3/5, so each pair mean is in [-9/25,9/25] and both I2 arguments are in [22/25,28/25]. Free degree-four scalar-product positivity additionally gives I2(false)>=1. Logarithmic-mean monotonicity yields betaPrime<=reciprocalLogMean(22/25)/3<=crudeLogUpper(22/25)/3=24332081/68523180<35510/100000. The exact rational gap is 250109/34261590000.

Route: Use nonadjacent conditional independence and the three-factor U/D mean bound to obtain I2(true)>=22/25; use free pair positivity for I2(false)>=1.  
Apply logarithmic-mean monotonicity and the crude enclosure at 22/25, then clear the positive rational denominator to reach 35510/100000.

**The sharp beta-prime calculation.**

Distinct neighbours `f,o` of `y` are nonadjacent in the ambient square lattice. Given all other spins in the removed-site network, their laws are independent on each conditioning fibre with positive probability. Neither has a leg, and each has at most three remaining factors. Lemma `l:35` applies to either U or D law, with neighbour vectors in the closed unit ball, giving conditional mean norms at most `3/5`. Hence `|E P_fo| ≤ 9/25`, which yields both `I₂` values in `[22/25,28/25]`. Free pair positivity strengthens the second argument to `I₂⁰ ≥ 1`.

Therefore
`L(I₂ᵗʳᵘᵉ,I₂ᶠᵃˡˢᵉ) ≥ L(22/25,1) > 0`, and
`β′ ≤ reciprocalLogMean(22/25)/3 ≤ B(22/25)/3`.
Exact rational arithmetic gives
`B(22/25)/3 = 24332081/68523180` and
`35510/100000 - 24332081/68523180 = 250109/34261590000 > 0`.
Using only the two interval lower bounds would give `β′ ≤ 25/66`, which is too weak. The extra free lower bound is established from the existing hypotheses, so it is not a missing premise.

**Lean traps checked.**

- No instance premise was silently dropped: Lean's printed `Departure` contains all three proof fields and has no extra type or instance parameters. `Network G` by itself has no validity fields; each argument must use `a.auxiliary` and `a.start` explicitly.
- `presentNeighbours` is a `Finset` of actual mutually kept bonds, not the kept set and not all four geometric neighbours. The explicit `o ≠ f` in the two-neighbour leaves prevents `{o,f}` from collapsing to a singleton. The one-neighbour case also uses `a.present` to identify its sole member as `o`.
- The partition sums are over functions from the finite subtype `D.active` to `SpinLetter`. The derived `Fintype` instances include all thirteen letters at U sites, with the extra letter carrying zero weight. Finite reindexing must retain this convention. An empty active subtype has one function, so its partition is one.
- Pins are indexed by the subtype of `originalLegs G`, with an independent unit vector on every original leg. The volume `G` stays fixed under tracing/removal; every surviving original leg remains in the product. Erased half-bonds and flags into X sites create no new pins.
- `protectedSites` uses classical decidability of an extended-natural infimum; `logarithmicMean` uses classical real equality. Classical reasoning is available in these noncomputable definitions and does not introduce another mathematical premise. Geometry proofs must work with the defined ambient integer lattice and `ℕ∞` depth.
- The crude statement quantifies `s : ℚ`, compares it with 0 and 1 in ℚ, then casts `s` and `crudeLogUpper s` to ℝ. Lean's fully explicit print confirms this. In `crudeLogUpper`, subtraction and division are rational; the beta-prime upper bound is division in ℝ. There is no truncated natural subtraction or natural-number division in these expressions.
- Real division is total, so cancellation requires the positive normalizers above. For the crude enclosure, `1-s`, `1+s`, and `1-t²` are positive under `0<s<1`; the endpoints are excluded. For beta-prime both mean arguments are positive. The diagonal branch `L(x,x)=x` is essential: using only the raw divided difference would give `0/0` and invalidate strict positivity.
- The conditional argument averages only positive-probability fibres; it does not claim rotational covariance of arbitrary functions or probabilities at zero-mass conditioning events. Only the finite moments through degree four are used.

**Non-vacuity and verification.**

A concrete admissible family uses the 13-site diamond `G = {(i,j) : |i|+|j| ≤ 2}`, with `y=(0,0)`. Its centre has boundary depth three, and all other sites are protected U sites. Give all original legs the unit pin `(1,0,0)` and keep only a selected symmetric star at `y`. Auxiliary networks allow the remaining protected kept sets to be empty. Taking U status at `y` and star degrees one, two, or three realizes all U cases; taking D status there and degree one realizes the D case. The outgoing bond is present. In the two-neighbour example the removed endpoints are independent unpinned U sites, so both `I₂` values equal one and `β′=1/3>0`. These witnesses rule out contradictory hypotheses and an empty `Departure` domain. The crude domain is also inhabited, for example by `s=1/2`.

The proof-free [Lean inspection module](/home/ubuntu/aklt/reports/TS_REC_02/scratch/Inspect.lean) completed with exit status zero under Lean `4.35.0-rc2`, using the existing repository and package `.olean` files. It prints all eight exact statements, the `Departure` constructor, key unfolded definitions, and fully explicit casts for the crude and beta-prime uniform statements. See [inspect.log](/home/ubuntu/aklt/reports/TS_REC_02/scratch/inspect.log). Only one Lean process ran at a time; no repository module was built.

The [finite sanity checker](/home/ubuntu/aklt/reports/TS_REC_02/scratch/sanity_checks.py) verified the beta-prime rational endpoint and gap exactly, numerically checked all 35 monomials through total degree four for each explicit U/D law, and checked the concrete diamond networks before tracing, after tracing, and after removal. It evaluated both finite partition ratios in the four admissible examples and the two removed-site pair expectations. All checks passed; see [sanity_checks.log](/home/ubuntu/aklt/reports/TS_REC_02/scratch/sanity_checks.log). Floating-point examples supplement the mathematical truth audit and do not certify the universal leaves.
