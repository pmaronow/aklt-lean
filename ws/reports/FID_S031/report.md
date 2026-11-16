STATUS: PASS
BLOCKING: 0

DECL: farVolume PASS

Matches `F_i` in Definition `d:shells`, `sec4-periodic-gap.tex:10–18`. At `AKLT/Defs/Geometry.lean:92–94`, membership is precisely membership in `square a u` together with `(i - 1)s < |x-y|∞`.

The supporting objects have the intended meanings. `Plane` is the ambient `ℤ × ℤ`, and `supDist` is the maximum of the natural absolute values of the two integer coordinate differences (`Geometry.lean:8,14`). `Int.natCast_natAbs` (`Mathlib/Algebra/Order/Group/Unbundled/Int.lean:44`) identifies these absolute values with the ordinary integer absolute values. `square` is the Cartesian product of the two closed integer intervals from `a_j-u` to `a_j+u` (`Geometry.lean:74–76`), hence exactly the translated physical square, including its boundary. Checked `Finset.mem_product` (`Mathlib/Data/Finset/Prod.lean:61`) and `Finset.mem_Icc` (`Mathlib/Order/Interval/Finset/Defs.lean:301`), including the integer locally finite order instance (`Mathlib/Data/Int/Interval.lean:29–44`).

`shellSpacing u = √(√(u : ℝ))` is the nonnegative real fourth root, with no rounding. Checked `Real.sqrt_nonneg` and `Real.sq_sqrt` (`Mathlib/Analysis/Real/Sqrt.lean:144,178`). The subtraction in `((i : ℝ) - 1)` is real subtraction, so there is no truncated natural subtraction. The right-hand distance is coerced exactly from `ℕ` to `ℝ`; the comparison is strict, as in the paper. `Finset.mem_filter` (`Mathlib/Data/Finset/Filter.lean:127`) adds exactly this predicate and no further restriction.

DECL: shell PASS

Matches `D_i` and `k_i` in Definition `d:shells`, `sec4-periodic-gap.tex:14,19`. At `Geometry.lean:97–99`, membership is exactly `x ∈ C_u(a)` and `(supDist x y : ℤ) = ⌊(i : ℝ) * s⌋`.

The distance is the ambient maximum-coordinate distance checked above. Its cast to `ℤ` preserves its exact nonnegative integer value. `shellRadius` (`Geometry.lean:86`) uses integer floor, not natural floor, rounding to nearest, or truncation toward zero. Checked the notation and `Int.le_floor`/`Int.floor_le` in `Mathlib/Algebra/Order/Floor/Defs.lean:272–300`; these characterize the ordinary floor. The index is an integer, matching the paper's integer indices and preserving the ordinary predecessor used by consumers. The finite filter includes only sites of the original translated square, with no quotienting or extra thickness.

DECL: nearShell PASS

Matches `A_i` in Definition `d:shells`, `sec4-periodic-gap.tex:20–21`. At `Geometry.lean:102–105`, the definition filters precisely `D_i` by distance at most `l₀` to `{z : ℤ² | z ∉ C_u(a)}`. Thus the exterior is that of the original square, rather than that of the shell or remaining far volume. The metric is `supDist`, as required by `sec2-moments.tex:20–22` and explicitly confirmed for square geometry by `sec5-window.tex:10–15`.

Checked the distance construction at `Geometry.lean:58–59`: it takes the infimum of the natural distances, embedded in `ℕ∞`, over the subtype of all exterior lattice sites. `ℕ∞` is `WithTop ℕ` (`Mathlib/Data/ENat/Defs.lean:16–23`) with a complete linear order (`Mathlib/Data/ENat/Lattice.lean:29`). For a nonempty index type this infimum is attained (`ENat.exists_eq_iInf`, same file:130); for an empty index type it is top, rather than zero (`ENat.iInf_natCast_eq_top`, same file:41). The exterior of this finite square is nonempty, so here the value is the actual finite minimum. Comparison with `(l₀ : ℕ∞)` is ordinary comparison of natural distances (`Mathlib/Data/ENat/Basic.lean:287`). No `toNat` conversion could turn infinity into zero.

In particular, a site on the square's edge has exterior distance one. More generally, for an interior site with coordinate offsets `v₁,v₂`, the distance is `min(u+1-v₁, u+1+v₁, u+1-v₂, u+1+v₂)`. This agrees with the lattice exterior half-planes in `sec5-window.tex:13–15`, including the offset by one. The cutoff is inclusive, exactly as the paper specifies. The infinite exterior requires no finiteness or `Fintype` assumption.

DECL: window PASS

Matches `B_i = D_i \ A_i` in Definition `d:shells`, `sec4-periodic-gap.tex:22`. `Geometry.lean:108–109` uses precisely finite-set difference with the matching parameters `a,y,u,l₀,i`. Checked `Finset.mem_sdiff` (`Mathlib/Data/Finset/SDiff.lean:58`): membership means membership in the shell and nonmembership in the near shell. Together with the preceding distance check, this is the part of `D_i` at exterior distance strictly greater than `l₀`.

This is also the correct physical-site marginal domain in `WindowProperty` (`AKLT/Defs/FrameModel.lean:83–91`). On the paper's domain `u ≥ 1`, the real spacing satisfies `s ≥ 1`, and `⌊is⌋ > (i-1)s`; hence `B_i ⊆ D_i ⊆ F_i`. Thus the marginal does use sites of its actual far volume, without relying on default values outside that volume. Empty windows have their ordinary empty-site interpretation, explicitly allowed by `sec4-periodic-gap.tex:193–196` and `sec5-window.tex:767–768`.

DECL: exceptionalIndices PASS

Matches `I_0` in Definition `d:shells`, `sec4-periodic-gap.tex:25–27`. `Geometry.lean:112–116` filters the closed integer interval `2 ≤ i ≤ lastShellIndex u`, where `lastShellIndex u = ⌊s⌋ + 1` (`Geometry.lean:89`). Checked the integer-floor and inclusive-interval meanings described above. In particular, the endpoint is the paper's `i₁`, not the smaller trial endpoint `⌊s⌋` used in (W).

The filter says exactly that there exist a physical shell point `x ∈ D_i` and a corner site `z ∈ squareCorners a u` whose distance is strictly less than `s/3`. Both existential choices may depend on `i`, as in the paper; no single common corner or shell point is required. `squareCorners` (`Geometry.lean:79–80`) takes the Cartesian product of `{a₁-u,a₁+u}` and `{a₂-u,a₂+u}`, giving all four actual translated corner sites for `u ≥ 1`, with independent signs. Checked finite insertion/singleton membership (`Mathlib/Data/Finset/Insert.lean:74,365`) and product membership. The corner distance is ambient `ℓ∞`, explicitly stipulated by `sec5-window.tex:11–12`.

The distance is cast to `ℝ`, and `shellSpacing u / 3` is real division by the nonzero real numeral three. There is no integer division, rounding of the cutoff, or division by a parameter that can vanish. Equality at the cutoff is excluded, matching “strictly less.” The result is a finite set of integer indices, without multiplicities or an assumption that the entire ambient lattice is finite.

Non-blocking remarks:

- Read the whole of `Geometry.lean`; its sole import is the Mathlib umbrella. Inspected the relevant imported Mathlib definitions and membership/order laws, and checked the consumers in `FrameModel.lean` and `Blueprint/Top/Windows.lean`. Judgments above concern only the five assigned declarations.
- These definitions are total functions, so they also assign values at `u = 0`, `l₀ = 0`, and exterior seeds outside the paper's stated domain. This harmless extension does not assert any geometric theorem at those parameters. The paper assumes `u ≥ 1`, `l₀ ≥ 1`, and `dist∞(y,C_u(a)) = 1` (`sec4-periodic-gap.tex:11–15`). `WindowProperty` supplies those conditions through `1 ≤ Mstar ≤ u`, `1 ≤ l₀`, and the distance equality (`FrameModel.lean:84–88`); `ShellGeometryStatement` supplies them through its positive width, geometric threshold, and exterior-distance hypothesis (`Blueprint/Top/Windows.lean:12–13`). Both quantify arbitrary translates and seeds. The distinct permitted index ranges in those consumers agree with the paper.
- Natural and integer casts preserve order (`Mathlib/Data/Nat/Cast/Order/Basic.lean:70–75`); maximum commutes with natural casting (`Mathlib/Data/Nat/Cast/Order/Ring.lean:45`). No coordinate subtraction in these objects occurs in `ℕ`. Classical decidability in the filters changes neither membership nor domains. Finiteness comes from integer intervals, products, filters, and difference; no extra finiteness or nonemptiness hypothesis is imposed on a shell or window.
- This was a source-semantic review; no Lean processes were launched and no input files were modified. Paper citations refer to `/home/ubuntu/aklt/review/FID_S/paper/`, AKLT citations to `/home/ubuntu/aklt/review/FID_S/lean/`, and Mathlib citations to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`.
