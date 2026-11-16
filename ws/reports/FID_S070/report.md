STATUS: PASS
BLOCKING: 0

DECL: inducedBoundary PASS

This is the induced boundary in `paper/sec4-periodic-gap.tex:51–54` and the conditioning argument of Lemma `l:planeenergy`, `paper/sec3-quantum-frames.tex:709–719`. The underlying boundary convention is Definition `d:framemodel`, `paper/sec3-quantum-frames.tex:499–507`: one frame letter per exterior neighbour site, including when several crossing bonds share that site.

The relevant use, `lean/AKLT/Blueprint/Top/Quantum.lean:84–87`, explicitly assumes `V ⊆ W`. For an exterior neighbour `z` of `V`, either `z ∈ W`, in which case `z ∈ W \ V` and the definition supplies `σ z`, or `z ∉ W`, in which case its adjacency to a site of `V ⊆ W` makes it an exterior neighbour of `W` and the definition supplies `η z`. Consequently neither extension's fallback letter is used. It does not use letters inside `V` to define its boundary. For `V = W` it recovers `η`; for empty `V` its boundary has empty domain.

Checked Mathlib meanings: a finset used as a type is its membership subtype (`Mathlib/Data/Finset/Defs.lean:159–180`); `Finset.mem_biUnion` and `Finset.mem_image` give the existential membership conditions (`Mathlib/Data/Finset/Union.lean:202`, `Mathlib/Data/Finset/Image.lean:293`). Thus `exteriorSites`, the image of the second endpoints of `originalLegs`, identifies shared exterior sites correctly. Subtype proof fields do not add different physical sites. The retained label is interpreted using the colour of `z` by `planeWeight`, so it remains a letter in the correct site alphabet.

DECL: conditionalPlaneLaw PASS

This is conditioning off a subset as in Definition `d:framemodel`, `paper/sec3-quantum-frames.tex:508–509`, and Lemma `l:planeenergy`, `paper/sec3-quantum-frames.tex:709–719`; see also the explicit consistency convention at `paper/sec4-periodic-gap.tex:51–54`.

Write `p = planeLaw κ W η` and `Eσ(τ) := ∀ x ∈ W \ V, τ x = σ x`. Expanding `conditionOn`, `normalize`, and `marginal` gives, at a configuration `v` on `V`, exactly

`(∑ τ, if Eσ(τ) ∧ τ|V = v then p τ else 0) / (∑ τ, if Eσ(τ) then p τ else 0)`.

Here restrictions are genuine restrictions because the use at `lean/AKLT/Blueprint/Top/Quantum.lean:84–87` supplies `V ⊆ W`. `Finset.mem_sdiff` means membership in `W` and nonmembership in `V` (`Mathlib/Data/Finset/SDiff.lean:58`), so precisely the complement inside the original volume is fixed. The result is a weight on `V → IcoLetter`, rather than on full configurations carrying redundant exterior coordinates. Equality in the consistency statement is therefore pointwise equality on the same configuration space as the smaller-volume plane law.

The caller also supplies proper plane colouring and an actual frame-valued boundary. The imported plane weight has the paper's plus interaction, one factor per internal bond and crossing bond, and site factor `12^(-|W|)` (`lean/AKLT/Defs/FrameModel.lean:37–47`). The twelve labels give the twelve distinct vectors of the site's rotated frame. By `paper/sec3-quantum-frames.tex:341–355,519–524`, all these weights are strictly positive. The event contains `σ`, so both the original partition sum and the conditioning denominator are positive. Although real division by zero is totalized to zero in Mathlib (`Mathlib/Algebra/GroupWithZero/Basic.lean:402`), that branch cannot affect the claimed consistency. The original normalization cancels in the fibre quotient; there is no extra factor from normalizing twice.

Checked finiteness: `Finset.fintypeCoeSort` enumerates exactly the members of `W` or `V` (`Mathlib/Data/Fintype/Sets.lean:226–231`), finite products of finite alphabets are finite (`Mathlib/Data/Fintype/Pi.lean:134–136`), and `∑ τ` is a sum over `Finset.univ` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:30`). These are full finite sums, not averages or sums over an empty type. Empty `V` gives the unit mass on its single empty configuration; `V = W` gives the original law. Empty `W` is included, as the paper requires at `paper/sec3-quantum-frames.tex:523–524,718–719`.

DECL: conditionalTorusLaw PASS

This is the torus conditional block law in Lemma `l:planeenergy`, `paper/sec3-quantum-frames.tex:709–719`, formed from the antiferromagnetic torus law of Definition `d:framemodel`, `paper/sec3-quantum-frames.tex:490–497`.

`AgreeOutside U σ τ` is explicitly `∀ x, x ∉ U → σ x = τ x` (`lean/AKLT/Defs/Probability.lean:39–41`), so the arguments fix the intended outside letters. `conditionOn` divides the restricted mass by its full fibre mass, and `marginal` pushes it to `τ|U`. Thus the result is exactly the conditional probability on configurations of `U`. The values of `σ` inside `U` are irrelevant. The underlying `torusWeight` retains the minus interaction and counts each physical bond once; conditioning does not introduce a plane gauge or change the interaction sign.

Its use at `lean/AKLT/Blueprint/Top/Quantum.lean:94–98` requires proper torus colouring before comparing two such laws. Hence every atom is positive, and every prescribed outside configuration has a positive fibre, since it is extended by `σ` itself. The denominator and empty-block checks are the same finite-sum checks as for `conditionalPlaneLaw`. For `U = ∅` there is one empty block configuration of mass one; for the whole torus the conditional law is the original law.

Checked Mathlib/domain meanings: `U → IcoLetter` uses the finset membership subtype, not functions from a finset-valued object. Its finite function-space instance enumerates every assignment once (`Mathlib/Data/Fintype/Sets.lean:226`, `Mathlib/Data/Fintype/Pi.lean:134`). `Size` requires each period to be at least three (`lean/AKLT/Challenge/Main.lean:16–23`), supplying `NeZero`; Mathlib's `ZMod.fintype` requires that condition (`Mathlib/Data/ZMod/Defs.lean:155–157`). In particular, the infinite `ZMod 0 = ℤ` branch is excluded. Odd periods are allowed, and size three creates neither loops nor repeated unoriented bonds. The external-neighbour agreement in the caller is precisely the Markov dependence asserted in the paper; equality compares weights on the common block alphabet.

DECL: sitesInVolume PASS

This auxiliary definition has no separate named paper counterpart. It implements the subset of physical coordinates of a finite product used in conditioning off a subset (`paper/sec3-quantum-frames.tex:709–714`) and in the consistency convention (`paper/sec4-periodic-gap.tex:51–54`). There are no uses of this helper elsewhere in the supplied Lean tree.

For `x : W`, `x ∈ sitesInVolume W V` is equivalent to `x.val ∈ V`. Its physical image is consequently exactly `W ∩ V`; when `V ⊆ W`, it represents all and only the sites of `V` inside the `W`-indexed product. It includes no exterior sites and introduces no multiplicity. Empty and full subvolumes give the empty finset and the full finset of `W`, respectively.

Checked Mathlib meanings: `Finset.fintypeCoeSort` makes `Finset.univ : Finset W` equal to `W.attach` (`Mathlib/Data/Fintype/Sets.lean:226–231`), and `Finset.mem_filter` is conjunction with the filter predicate (`Mathlib/Data/Finset/Filter.lean:127–128`). Thus the universe is the finite subtype of sites belonging to `W`, despite the infinite ambient plane. No subset hypothesis is needed to form this intersection; its subvolume interpretation uses `V ⊆ W`.

DECL: ParallelClearance PASS

This expresses exactly the parallel-side assertion of Lemma `l:shellgeom`, `paper/sec5-window.tex:27–34`. The half-planes consist of lattice sites, as expressly stipulated at `paper/sec5-window.tex:13–15`. The proof checks distances from a shell side to both parallel exterior half-planes (`paper/sec5-window.tex:78–99`), matching the independent choices of the two signs here.

For either coordinate `j`, `ε = ±1` selects the supporting coordinate `b = y_j + ε k_i`. For nonnegative `k_i`, the witness `z ∈ square a u`, `z_j = b`, and `supDist z y = k_i` is equivalent to the corresponding finite shell side meeting the physical square: its other coordinate lies in `[y_other-k_i, y_other+k_i]`. Thus the antecedent checks an actual side segment, not its infinite supporting line. `Fin 2` selects exactly the two coordinates, and the sign hypotheses select exactly the two sides and two parallel exterior half-planes.

For `δ = +1`, that exterior half-plane starts at `a_j + u + 1`, so the distance is `u + 1 - (b-a_j)`. For `δ = -1`, it ends at `a_j - u - 1`, so the distance is `u + 1 + (b-a_j)`. The witness puts `b` inside the square's coordinate interval, making these quantities positive. They are constant along the entire side. This is exactly the formula `u + 1 - δ*(b-a_j)`; in particular, the `+1` is required by the paper's lattice convention.

Checked Mathlib/arithmetic meanings: `Finset.mem_Icc` uses inclusive endpoints (`Mathlib/Order/Interval/Finset/Defs.lean:301`), and `Finset.mem_product` is coordinatewise membership (`Mathlib/Data/Finset/Prod.lean:61`). `supDist` uses the maximum of integer absolute coordinate differences; the cast of `Int.natAbs` is absolute value (`Mathlib/Algebra/Order/Ring/Int.lean:50`). `shellRadius` is the integer floor of `i*s` (`Mathlib/Algebra/Order/Floor/Defs.lean:248,291–300`), and `shellSpacing` is the nonnegative fourth root of natural `u`, computed by two real square roots (`Mathlib/Analysis/Real/Sqrt.lean:112,144–178`). All depth subtraction takes place in `ℤ`, with no truncated natural subtraction. The final comparison casts that integer depth to `ℝ`; `s/3` is real division, with no integer rounding and nonzero denominator.

The use at `lean/AKLT/Blueprint/Top/Windows.lean:11–17` supplies positive `l₀`, `u ≥ max(16,6(l₀+1))^4`, the exterior-seed distance condition, `2 ≤ i ≤ floor(s)+1`, and nonexceptionality. These are the paper's hypotheses (`paper/sec4-periodic-gap.tex:10–27`, `paper/sec5-window.tex:27–34`). They ensure positive shell radii and exclude the exceptional near-corner example discussed at `paper/sec5-window.tex:19–25`. No intersecting side or parallel edge is omitted, and no clearance requirement is imposed on a side missing the physical square.

Non-blocking remarks:

- The helpers are total functions. Their intended probabilistic and nested-volume interpretations use the explicit hypotheses in their callers; those hypotheses are present. Values outside those hypotheses do not weaken the reviewed interface uses.
- Read all of `Specification.lean` and its recursive local import closure, and examined the relevant interface uses and paper passages. Judgments above concern only the five assigned declarations. Paths beginning `lean/` and `paper/` are relative to `/home/ubuntu/aklt/review/FID_S/`; Mathlib paths are relative to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/`.
- Supplemental Python checks passed: 81 nested pairs of volumes in a 2×2 patch for boundary closure; 1,728 exact rational conditional-pushforward identities, including empty/full blocks; and 7,840 checks of the side-intersection predicate and signed lattice-distance formula. These supplement the general arguments above. No Lean process was run, and inputs were not modified.
