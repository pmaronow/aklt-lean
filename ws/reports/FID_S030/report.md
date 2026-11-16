STATUS: PASS
BLOCKING: 0

Reviewed declarations in `lean/AKLT/Defs/Geometry.lean`, read that file in full, and traced its imported Mathlib notions and relevant consumers. Paper and Lean paths below are relative to `/home/ubuntu/aklt/review/FID_S/`; Mathlib paths are relative to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`. Only the five assigned declarations are judged.

DECL: square PASS

`Geometry.lean:74` matches Definition `d:shells`, `paper/sec4-periodic-gap.tex:10–12`: `C_u(a) = a + {-u,...,u}²`. Since `Plane = ℤ × ℤ` (`Geometry.lean:8`), membership means exactly `a₁-u ≤ x₁ ≤ a₁+u` and `a₂-u ≤ x₂ ≤ a₂+u`. Mathlib's `Finset.Icc` includes both endpoints (`Order/Interval/Finset/Defs.lean:277–302`); `Finset.product` is Cartesian product (`Data/Finset/Prod.lean:45–69`). All coordinate arithmetic, including subtraction, takes place in `ℤ`; the natural radius is cast before subtraction, so there is no truncated natural subtraction. The integer `LocallyFiniteOrder` instance enumerates precisely these finite intervals (`Data/Int/Interval.lean:29–44`), without requiring a finite ambient plane. Thus the square has `(2u+1)²` distinct physical lattice sites, with no periodic identification.

DECL: squareCorners PASS

`Geometry.lean:79` is the correct auxiliary object for the corner-site condition defining `I₀` in `paper/sec4-periodic-gap.tex:25–27`. The product of the two endpoint pairs gives exactly `(a₁±u, a₂±u)`, with signs chosen independently and the translation retained. Mathlib's finite-set insertion uses ordinary membership and removes duplicates (`Data/Finset/Insert.lean:347–366`); its Cartesian-product membership is coordinatewise (`Data/Finset/Prod.lean:61`). For the paper's `u ≥ 1` these are four distinct sites of `square a u`. Its consumer `exceptionalIndices` (`Geometry.lean:112–116`) tests proximity to these actual sites. The distance is `supDist`, the maximum of the absolute integer coordinate differences, hence ambient ℓ∞ distance, as required explicitly by `paper/sec5-window.tex:10–15`; see `Int.natCast_natAbs`, `Algebra/Order/Group/Unbundled/Int.lean:40–44`.

DECL: shellSpacing PASS

`Geometry.lean:83` matches `s = u^(1/4)` in `paper/sec4-periodic-gap.tex:14`. Both square roots are `Real.sqrt`, with the natural input cast exactly to `ℝ`. This is the nonnegative real square root, not an integer root: `Analysis/Real/Sqrt.lean:109–113,144–150,178` gives nonnegativity and the square identity. Thus `s ≥ 0` and `s⁴ = (u : ℝ)`, and for positive `u` it is the positive fourth root. Equivalently, `Real.sqrt_eq_rpow` and `Real.rpow_mul` (`Analysis/SpecialFunctions/Pow/Real.lean:986–990,415–419`) identify it with real exponent `1/4`. No rounding or natural-number division occurs.

DECL: shellRadius PASS

`Geometry.lean:86` is exactly `k_i = floor(i s)` from `paper/sec4-periodic-gap.tex:14`. The integer index is cast to `ℝ`, multiplied by the unrounded spacing, and only then floored. Mathlib's unadorned floor notation means `Int.floor : ℝ → ℤ` (`Algebra/Order/Floor/Defs.lean:247–272`), characterized by `k ≤ r < k+1` (`Defs.lean:292–300`; `Algebra/Order/Floor/Ring.lean:125–130`). It therefore handles negative indices by mathematical floor as well. The shell consumer compares the integer-cast ambient distance directly with this integer radius (`Geometry.lean:99`), with no conversion to a natural radius that could collapse negative values to zero. In the paper's trial range `i ≥ 2`, the radius is positive.

DECL: lastShellIndex PASS

`Geometry.lean:89` matches `i₁ = floor(s)+1` in `paper/sec4-periodic-gap.tex:14`. The floor has the same integer meaning just checked, and the addition takes place in `ℤ`. In particular, an integral spacing still gives `i₁ = s+1`. Its consumer uses the closed integer interval `Finset.Icc 2 (lastShellIndex u)` (`Geometry.lean:114`), exactly the inclusive exceptional-index range in `paper/sec4-periodic-gap.tex:25`. Keeping this extra endpoint agrees with the shell-geometry range (`paper/sec5-window.tex:28–31`) and the final surgery index (`paper/sec4-periodic-gap.tex:91,110–111,153–154`).

Non-blocking remarks:

- The definitions are total at `u = 0`, whereas `d:shells` assumes integer `u ≥ 1`. This is a harmless extension of the formulas: `square` and `squareCorners` then both equal `{a}`, spacing and radii are zero, and the last index is one. The relevant propositions enforce the paper's domain: `WindowProperty` has `1 ≤ Mstar ≤ u` (`lean/AKLT/Defs/FrameModel.lean:83–88`), while `ShellGeometryStatement` requires `geometryThreshold l₀ ≤ u` (`lean/AKLT/Blueprint/Top/Windows.lean:12`), whose threshold is at least `16⁴`. No zero-radius case enters those assertions.
- The exterior-seed hypothesis and index bounds belong to the consuming propositions, not to these independent geometric formulas. Those consumers retain the distance-one seed condition and integer index bounds. No additional hypothesis, division by zero, hidden finite-plane assumption, or vacuous interpretation was found in the assigned declarations. This review used source inspection; no Lean process was run.
