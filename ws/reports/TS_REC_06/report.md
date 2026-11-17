STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Reason |
|---|---|---|---|
| [`AKLT.Blueprint.Rec.TraceTelescopeStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:49) | TRUE | medium | Positive consecutive prefix normalizers telescope; the empty product is one. |
| [`AKLT.Blueprint.Rec.CoordinateStepStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:59) | TRUE | hard | The unpinned departure has precisely the U/D moment bounds and the stated coefficient. |
| [`AKLT.Blueprint.Rec.PairExpansionStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:70) | TRUE | hard | Finite bond-consuming iteration enumerates exactly the stopped direction words. |
| [`AKLT.Blueprint.Rec.PairTerminalFactorStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:81) | TRUE | medium | The target stays U, or stays D and is isolated after its sole bond is deleted. |
| [`AKLT.Blueprint.Rec.PairDegreeStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:97) | TRUE | medium | Original legs are counted; arrival deletion pays for the terminal insertion. |
| [`AKLT.Blueprint.Rec.ProductExposureStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:108) | TRUE | medium | Ordered telescoping, a positive log estimate, and c ≤ 1 give the inclusive prefix. |
| [`AKLT.Blueprint.Rec.OnePointPointwiseStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:117) | TRUE | hard | A common step majorant handles both pin choices and at most twelve uncovered U departures. |
| [`AKLT.Blueprint.Rec.OnePointSumStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:129) | TRUE | medium | The same incoming direction embeds the sum in H2; the geometric tail starts at the protected distance. |

All eight leaves are TRUE as written. No missing mathematical premise, counterexample, or unintended vacuity was found. The two one-point leaves are conditional on H1; the sum leaf also assumes the full `OpenTrailBound CV q` contract. Their arguments use those inputs directly. This audit does not independently establish H1 or H2.

Audited repository: `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository was read only. No proofs were written. Difficulty estimates include the finite-sum reindexing needed by a writer starting from these concrete definitions.

**Definitions and paper checked.**

The eight exact statements are in [NodesWalk.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesWalk.lean:49). I traced their relevant definitions through:

- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): the ambient integer plane, compass steps/reversal, adjacency, neighbours, single-orientation internal bonds, original legs, extended set distance, square, and original protected layer.
- [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8): coordinates, dot product, squared norm, arbitrary unit pins, the explicit twelve icosahedral vectors, the extra zero label, U/D weights, and site functionals.
- [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9) and [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10): pin assignment, active sites, mutual presence, bonds, present neighbours, local/auxiliary rules, the dependent spin sum and zero extension, partitions/expectations, admissible start, trace step/network/coefficient/ratio.
- [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9): rational thresholds and passage factors, direction words and clamped vertices, unoriented word bonds, incoming direction, straightness, departure counts and revisits, trail weights, H2, vertex lists, stopped predicates/finsets, and the target predicate.
- [Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:9), [Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:29), [Top/Response.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Response.lean:10), and [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:15): the complete covered-template data and partition functions, semantic H1, actual step quotient, normalization rotation, corrected `CoveredDepartureV2`, prefix trace, uncovered count, finite stopped sum, common maximum, distance convention, target factor, and constants.

Paper comparison used [sec6-walks.tex](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:50), especially d:trace (50–98), p:pairwalk and its site identities (100–237), l:exposure (437–485), covered-template/H1 transfer (488–651), and l:onepoint (695–775). The explicit laws and finite positivity argument were checked in [sec2-moments.tex](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8), including l:finitefacts (126–193).

**Why the hypotheses suffice.**

`Auxiliary` explicitly supplies the four-factor bound at every active site and requires every original protected site to remain U. An original leg starts at a site of exterior depth one, hence at a protected site. An admissible departure is outside that layer and therefore has no original legs. Its U/D alternatives give respectively at most three/one present bonds. A U departure leaves at most two bonds at its new D site; a D departure deletes its only possible bond before removal. Thus no additional unused present bond is destroyed. Induction makes every needed trail bond present and every prefix auxiliary.

The explicit U and D laws are normalized, nonnegative, and supported in the unit ball. With at most four factors at a site, one can select a positive-weight icosahedral letter avoiding at most four forbidden antipodes. Doing this over the finite active set yields a positive summand, hence a strictly positive partition, for every prefix and either pin choice. This supplies all denominator nonvanishing facts from the hypotheses; they need not be added as premises.

The corrected matcher is material to the one-point statements. It compares a rotated pattern kept set **after intersection with the original G**. The passage template lies inside G because its centre is outside the width-two protected layer. Passage and nearest-neighbour sites have no original legs. Tips have at most three external factors; corners have their two specified external directions. The paper's tip replacement and corner-slot mixture therefore transfer H1 to every covered departure accepted by V2, including boundary corners with original legs. Consistency of arbitrary auxiliary kept sets is unnecessary: a covered departure already supplies the required non-tip matching, and an uncovered departure uses the uniform bound.

**`TraceTelescopeStatement` — TRUE; medium.**

Every prefix of an initially present bond-distinct stopped trail is auxiliary and every departure remains admissible: U departures leave at most two bonds and D departures consume their only possible bond. LocalRules bounds every active site by four incident factors, and protected sites remain U with all original legs, so every prefix normalizer is strictly positive. stepRatio is exactly the quotient of consecutive prefix normalizers; the product cancels to traceRatio. At n=0 the trace is D and both sides equal one.

Proof route (two steps):

1. Establish prefix/traceStep compatibility and preservation of Auxiliary; obtain positivity of every prefix partition from the concrete finite spin laws.
2. Unfold the two ratios and telescope the nonzero consecutive normalizers over Fin n, including the empty product.

Lean traps: Division in ℝ is total, so cancellation requires the derived positivity at every prefix. Relate `take (i.val + 1)` to the consecutive `traceStep` before telescoping. Do not cancel a hypothetical zero normalizer.

**`CoordinateStepStatement` — TRUE; hard.**

AdmissibleStart places u outside the original protected layer, hence u has no original legs, and supplies status U with at most three present neighbours or status D with at most one. Since u differs from the active target v, its coordinate can be integrated first. The explicit icosahedral laws satisfy the U degree-four identity with coefficient 1/3 and the D degree-two identity with coefficient 1/5. Each term has exactly the traceStep law and deleted bond, including when the selected neighbour is v. Zero neighbours give zero on both sides. Consistent kept sets are unnecessary because only mutually present bonds enter partition.

Proof route (two steps):

1. Split the dependent finite configuration sum into the spin at u and the remaining spins; isolate all factors incident to u.
2. Apply the U/D site moment identity with the kth basis vector and reassemble each residual sum as the stated traceStep partition.

Lean traps: The configuration index type depends on `D.active`; D-to-X changes that type and needs a finite reindexing. U-to-D keeps the site but changes its law, including the positive zero atom. `u ≠ v` makes the fixed coordinate independent of the departure spin; if the selected neighbour equals v, the residual observable is its squared coordinate. The coefficient’s else branch is D because `AdmissibleStart` excludes X.

**`PairExpansionStatement` — TRUE; hard.**

The target predicate includes activity and precisely the paper's U bound of three incident bond-plus-original-leg factors or D bound of one present bond. A nonterminal coordinate step consumes one initially present unoriented bond; no other unused bond is destroyed by an admissible departure. Thus branches terminate in an empty sum or at their first hit of S union {v}, and successful branches are exactly the direction words counted by stoppedNetworkTrails. Their length is at most D.bonds.card, within stoppedSum's inclusive cutoff. Dividing the finite unnormalized expansion by the positive initial partition gives the coefficient, traceRatio and terminal expectation as written.

Proof route (two steps):

1. Iterate the coordinate identity by induction on the number of remaining present bonds and identify successful branches with stopped direction words.
2. Sum the three coordinates, use the length bound, and divide by the positive initial partition, inserting and cancelling each positive terminal partition.

Lean traps: `D.bonds` stores one oriented representative, while `wordBond` is an unoriented two-point finset; establish the correspondence without a factor of two. `Finset.range (D.bonds.card + 1)` includes length `D.bonds.card`. The coefficient is rational and is cast to ℝ before multiplication. Failed branches contribute an empty sum, not an extra terminal term.

**`PairTerminalFactorStatement` — TRUE; medium.**

The stopping condition forbids every earlier visit to v, so its status is unchanged and it is still active after arrival. For an initial U target, every positive-weight spin has norm squared one, even if v is protected and retains original legs. For an initial D target, Auxiliary excludes v from the protected layer, so it has no original legs. AdmissibleTarget allows at most the arrival bond at v, and traceStep deletes that bond; the terminal target is isolated with its normalized D law, whose squared-norm mean is 12/20=3/5. These values do not depend on pins.

Proof route (two steps):

1. Use first-hit stopping to preserve the target status and split into the U and D cases of AdmissibleTarget.
2. Use the unit support in the U case; in the D case factor out the isolated site sum and cancel the positive remaining normalizer.

Lean traps: `targetFactor` has an unrestricted else branch, but `AdmissibleTarget` restricts it to D here. A U spin is unit only at positive-weight labels: the common `SpinLetter` type also contains the zero label with U weight zero. The D law is normalized and has squared-norm mean 3/5, not one; keep its zero mass 2/5.

**`PairDegreeStatement` — TRUE; medium.**

The unmarked bound is exactly LocalRules, including original legs, and tracing never adds a bond or a leg. Before termination, the moving site has no legs and at most three present bonds when U or one when D; the untouched target has factorDegree at most three when U or one when D. At a protected terminal other than v the arrival removes one factor from a bound of four. At terminal v the arrival removes one from its initial bound of three (U), or its sole bond (D); the two indicator terms correctly count the degree-two self insertion. The zero-length stopped pair class is empty because u is outside S and differs from v.

Proof route (two steps):

1. Track monotone present-neighbour sets and the admissible moving endpoint along prefixes, retaining the fixed original-leg count.
2. Separate unmarked, distinct moving/target, protected terminal, and terminal self-pair cases; use the deleted arrival bond in each terminal bound.

Lean traps: `factorDegree` uses actual present neighbours plus every original leg at x, even when the free partition omits pin factors. It does not count only kept half-edges. Both natural-number indicator terms are one when the moving endpoint equals v. At a terminal protected endpoint use the deleted arrival bond; do not infer the terminal bound solely from prefix LocalRules.

**`ProductExposureStatement` — TRUE; medium.**

For positive b and c, the exponential mean-value estimate gives |b-c| <= max(b,c)*|log c-log b|. The hypotheses imply max(b_i,c_i) <= x_i, bound every preceding b factor by x, and bound every following c factor by one. The finite ordered telescoping identity therefore gives exactly the inclusive prefix product indexed by j.val <= i.val. For n=0 the two products are one and the sum is zero. Positivity hypotheses make every logarithm legitimate.

Proof route (two steps):

1. Telescope the difference of products in the natural Fin n order, with b factors before the exposed index and c factors after it.
2. Apply the positive exponential/log estimate termwise, bound the suffix by one and the prefix by x, then use the triangle inequality.

Lean traps: All scalars and logarithms are real. Positivity of b and c is essential for the log estimate. The filter uses `j.val ≤ i.val`, so its product includes the exposed factor at i. The empty finite index type gives 0 ≤ 0.

**`OnePointPointwiseStatement` — TRUE; hard.**

The statement explicitly assumes H1 and counts only evolving U departures that fail the corrected CoveredDepartureV2 matcher. At an evolving D departure, coefficient times stepRatio is 1/5 for both pin choices; this equals a revisit weight and is bounded by a first-departure weight if the site was initially D. An evolving U departure cannot be a lattice revisit. For a covered U departure, H1 transfers through the covered-template mixture to the pinned ratio bound passageFactor, while the free ratio is at most one. An uncovered U departure costs at most 12/5 relative to its lattice weight. Multiplying the same majorants for both pin choices, telescoping positive ratios, and using uncoveredCount <= 12 gives exactly exceptionFactor times trailWeight. Neither Consistent nor an extra assumption on initially D sites is required.

Proof route (two steps):

1. Use trace admissibility, positive telescoping ratios, the covered H1 ratio bound, the free ratio bound, and the universal pinned bound 12/5 at every step.
2. Compare evolving status with previous departures, multiply common step majorants, bound the exception power by twelve, and take the maximum only at the end.

Lean traps: `uncoveredCount` uses evolving prefix statuses and the V2 matcher, not the older exact-set matcher. `wordRevisit` counts earlier departures, not arrivals. An initially D first departure has coefficient 1/5 and a first-departure lattice weight at least 1/3, so only an inequality is available; do not identify traceCoefficient with trailBaseWeight in general. The incoming predecessor uses natural subtraction only in the guarded positive-index branch. Prove both pin choices against the same product before taking their maximum.

**`OnePointSumStatement` — TRUE; medium.**

OpenTrailBound explicitly includes 1 <= CV and 0 < q < 1 as well as the all-start, all-incoming, all-length bound. The absent incoming bond excludes precisely the initial reversal in IsTrail; initial bond distinctness already gives the remaining IsTrail condition. Every stopped network trail is therefore among the H2 words with the same initial data. Its nearest-neighbour length is at least protectedDistance G u. The active start makes G nonempty, so the original protected layer is nonempty and its extended distance is finite before toNat is used. Apply the pointwise estimate, enlarge each nonnegative finite length sum, and bound the resulting geometric tail by exceptionFactor*CV*q^distance/(1-q), the stated onePointConstant. The same incoming direction and exception bound are quantified uniformly over every stopped word.

Proof route (two steps):

1. Apply the pointwise estimate and embed each stopped-word class into IsTrail using the absent incoming bond; establish the distance lower bound.
2. Enlarge the finite sum to the nonnegative all-length geometric tail starting at protectedDistance G u and evaluate it using 0 < q < 1.

Lean traps: `OpenTrailBound` includes `1 ≤ CV`, `0 < q`, and `q < 1`, so `1 - q` is positive. `protectedDistance` uses `ENat.toNat`, which would map infinity to zero; an active start implies nonempty finite G, a nonempty protected layer, and finite distance. Use the same fixed incoming direction in the H2 enlargement. `onePointSum` places the maximum inside each summand; it is not a maximum of the two complete sums.

**Common Lean and boundary checks.**

No instance parameter was silently dropped: these are closed Props, and inspection of their elaborated definitions retained all stated binders. Products and sums over words use the finite type `Fin n → Compass`; configuration sums use functions on the subtype of a finite active finset. Neither the infinite ambient plane nor ℝ is being enumerated. Classical decidability may be needed for predicate finsets, `CoveredDepartureV2`, or protected-site membership; this is a proof-local issue, not a missing premise.

Rational coefficients, thresholds, passage factors, and weights must be transported to ℝ with their arithmetic identities. The pure product estimate and CV/q constants already live in ℝ. All exponents in the two requested one-point conclusions are natural-number powers. The clamped `wordVertex` and prefix `take` are used only at indices bounded by n.

At length zero the telescope has ratio one. The pair and one-point stopped classes at length zero are empty under their start hypotheses, because the start lies outside S and, for the pair, differs from v. With no present neighbours the coordinate sum is empty and its numerator vanishes by the first moment. Empty G cannot admit a start; this harmless boundary case does not make the universal leaves vacuous.

**Checks performed.**

A single scratch Lean process imported the existing `NodesWalk` object file and printed all eight definitions plus the start, target and H2 contracts. It also synthesized the finite word instances at lengths zero and three. It exited successfully. This inspected elaboration without adding any theorem or building the repository. See [Inspect.lean](scratch/Inspect.lean) and [inspect.log](scratch/inspect.log). Scratch Mathlib/package access uses a symlink to the repository's existing packages.

The deterministic [diagnostic script](scratch/checks.py), seed 6006, passed 360 numerical U/D site-identity checks, the U/D terminal squared-norm means, and 2,600 product-exposure checks including n=0. Across 250 sampled lattice networks it checked 14,769 prefixes and 4,082 successful stopped trails, including five terminal D targets: prefix degree bounds, preserved protected statuses, departure admissibility, preservation of unused bonds, the exact rational evolving-status coefficient formula, and D-target isolation all passed. Results are in [checks.json](scratch/checks.json). These samples support the definition audit; the verdicts rest on the arguments above, and no global H1/H2 verification is claimed.

Corrections required: none. The machine-readable deliverable is [verdicts.jsonl](verdicts.jsonl).
