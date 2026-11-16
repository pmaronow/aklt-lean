STATUS: PASS
BLOCKING: 0

DECL: originalLegs PASS

Paper: `sec2-moments.tex:97–119`, Definition `d:pinmodel`, especially line 100: the original legs are exactly the ordered pairs `(x,z)` with `x ∈ G`, `z ∉ G`, and ambient nearest-neighbour distance one.

Lean: `AKLT/Defs/Geometry.lean:54–55`. Expanding `Finset.mem_biUnion`, `Finset.mem_image`, and `Finset.mem_sdiff` gives exactly those membership conditions. The four constructors in the explicit `Fintype Compass` instance and their steps give precisely `x + (±1,0)` and `x + (0,±1)`. Addition on `ℤ × ℤ` is coordinatewise (`Mathlib/Algebra/Notation/Prod.lean:65–82`, including its generated additive declarations). The coordinate differences in `latticeDist` are integer subtraction followed by `Int.natAbs`, so distance one is precisely this four-point neighbourhood; there is no natural-number subtraction or periodic identification.

The finset operations remove duplicate ordered pairs, not distinct legs sharing an outside endpoint. Thus independent pins on such legs remain possible, as required at paper lines 118–119. `PinAssignment` and `pinnedSum` use `originalLegs G`, retaining a leg only when its tail survives (`AKLT/Defs/PinModel.lean:8–22`); the definition does not create legs into removed sites. Any finite volume, including the empty volume and volumes with holes, is allowed, with no connectivity assumption or `Fintype Plane` requirement. Relevant Mathlib membership rules are in `Data/Finset/Union.lean:191–203`, `Image.lean:278–294`, and `SDiff.lean:49–59`.

DECL: setDistance PASS

Paper: `sec1-result.tex:118–127` explicitly defines distance to a set as the minimum, with value infinity for the empty set. Definition `d:moment` repeats the ambient ℓ¹/ℓ∞ and empty-set conventions at `sec2-moments.tex:20–23`; the ℓ∞ use also appears in Definition `d:shells`, `sec4-periodic-gap.tex:13–21`.

Lean: `AKLT/Defs/Geometry.lean:58–59`. The index `y : S` is the subtype of all plane sites belonging to `S`; `y.val` is the actual site. No finiteness or inhabitedness assumption restricts the set. The infimum is taken after casting each natural distance into `ℕ∞`, not in `ℕ`. Mathlib defines `ℕ∞` as `WithTop ℕ`, with natural cast `WithTop.some` (`Data/ENat/Defs.lean:16–23`), and supplies its complete linear order (`Data/ENat/Lattice.lean:28–29`). In particular, `ENat.iInf_natCast_eq_top` says that this infimum is top exactly when the index type is empty (`Lattice.lean:41–44`). For a nonempty set it is finite, and `ENat.iInf_eq_natCast_iff` characterizes a finite value as an attained lower bound (`Lattice.lean:74–77`). Thus the expression is exactly the minimum distance, even for infinite nonempty sets, and is infinity for the empty set.

The generic `metric` parameter is an auxiliary abstraction: every use supplies either `latticeDist` or `supDist`, whose integer-coordinate absolute differences give precisely the paper's two ambient distances. No metric axioms need to be added to this definition. Finset-to-set coercions at its callers preserve exactly the same members (`Data/Finset/Defs.lean:100–127`).

DECL: boundaryDepth PASS

Paper: the distance `d(x, ℤ² \ G)` occurs in the protected-set formula at `sec2-moments.tex:101`; the same auxiliary quantity is explicitly named `b_G(x) = d(x,G^c)` at `sec5-window.tex:237` and described as an ambient distance function at `sec5-window.tex:642–645`.

Lean: `AKLT/Defs/Geometry.lean:62–63` applies the verified `setDistance` to `latticeDist` and the full ambient complement `{z | z ∉ G}`. This is distance to exterior lattice sites, rather than distance to the inner boundary, and consequently has no off-by-one shift: an inside site with an outside nearest neighbour has depth one. The complement is that of the original parameter `G`, with no removal set or induced-path restriction, matching `sec5-window.tex:5–10` and `sec1-result.tex:125–127`.

For every finite `G`, its complement in `ℤ²` is nonempty, so the extended-natural value is finite for every `x`. It is zero outside `G`, including everywhere when `G` is empty, and positive inside `G`. The infinite complement requires no finite-type instance: the complete-order infimum used by `setDistance` supports this domain directly. Finset membership/coercion has its ordinary extensional meaning (`Data/Finset/Defs.lean:100–127`).

DECL: protectedSites PASS

Paper: `sec2-moments.tex:97–102`, Definition `d:pinmodel`, defines `S(G) = {x ∈ G : d(x, ℤ² \ G) ≤ 2}`. Its continued use as the original protected set is explicit at `sec2-moments.tex:349–350` and `sec7-recursion.tex:4–7`.

Lean: `AKLT/Defs/Geometry.lean:66–68` filters precisely `G` by `boundaryDepth G x ≤ 2`. `Finset.mem_filter` gives membership in `G` conjoined with the predicate (`Data/Finset/Filter.lean:126–128`). The literal `2` is finite two in `ℕ∞`; comparison of finite natural casts is ordinary natural comparison (`Data/ENat/Basic.lean:285–287`), and infinity is greater than finite two, not an accidental zero. With the verified depth definition, this selects exactly the first two interior layers, including depth two, and excludes exterior sites and depth three. Empty `G` gives the empty finset. The local `classical` supplies decidability for filtering; it adds no mathematical hypothesis or finiteness restriction. All dependencies are on the original `G`, as required.

DECL: decay PASS

This is an auxiliary definition for the response factor in Definition `h:P`, `sec2-moments.tex:338–350`, especially the assumption `0 < θ < 1` at line 339 and the power at line 347.

Lean: `AKLT/Defs/Geometry.lean:71`. For finite `r = (n : ℕ∞)`, `ENat.toNat_natCast` gives `r.toNat = n`, so `decay θ r = θ ^ n`, the ordinary natural power of a real number, including value one at distance zero (`Data/ENat/Basic.lean:117–140`; natural powers and `pow_zero` are in `Algebra/Group/Monoid.lean:372–410`). Mathlib's conversion alone would send infinity to zero, but the explicit test `r = ⊤` returns zero before that conversion can affect the result. Thus infinity is not mistakenly assigned `θ ^ 0 = 1`.

The only external use of `decay` is the bound in `ResponseProperty` (`AKLT/Defs/PinModel.lean:44–53`), which explicitly requires `2 ≤ A` and `0 < θ < 1` and supplies exactly the minimum of the two distances to the original protected set. Although the paper does not separately define powers at infinity, zero is the limiting decay value in this parameter range. Moreover, infinity cannot arise for an admissible pair: its endpoints force `G` to be nonempty, and a site of maximal first coordinate in any nonempty finite `G` has an exterior east neighbour, hence belongs to `S(G)`. Distances to `S(G)` are therefore finite. The helper's unrestricted real parameter and its stipulated infinity value introduce no additional requirement or changed case in the paper's property.

Non-blocking remarks:

- The whole geometry file was reviewed, together with its relevant imported Mathlib notions and the declarations that consume these five definitions. Judgments above concern only the five assigned declarations.
- All five definitions are total on their stated domains. Their coordinate subtraction is in `ℤ`; none uses division, truncated natural subtraction, an unintended torus quotient, or an extra mathematical instance hypothesis. The broader domains of the auxiliary definitions cause no discrepancy in their uses.
- Verification was by source inspection and the exact membership/order characterizations cited above; no Lean processes were launched. Inputs were not modified.
