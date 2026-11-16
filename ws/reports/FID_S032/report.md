STATUS: PASS
BLOCKING: 0

DECL: geometryThreshold PASS

`AKLT.Defs.geometryThreshold`, at `lean/AKLT/Defs/Geometry.lean:118–119`, exactly defines the paper's geometric threshold. Lemma `l:shellgeom`, `paper/sec5-window.tex:27–28`, explicitly sets
\(M_{\mathrm g}(l_0)=\max\{16,6(l_0+1)\}^4\).
The Lean expression `(max 16 (6 * (l₀ + 1))) ^ 4` has the same constants, parentheses, and fourth power of the entire maximum.

All operands and the result are natural numbers. Mathlib's `Nat.instLinearOrder` uses ordinary `Nat.le` (`Mathlib/Data/Nat/Basic.lean:34–44`), and `max_def` identifies `max a b` with `if a ≤ b then b else a` (`Mathlib/Order/Defs/LinearOrder.lean:133`). The natural-number algebra instances use `Nat.add`, `Nat.mul`, and ordinary natural powers (`Mathlib/Algebra/Group/Nat/Defs.lean:30–51`). Thus this is exact, unbounded integer arithmetic, with no coercion, rounding, truncated subtraction, division, sign convention, or overflow issue. The definition has no implicit finiteness, nonemptiness, or user-supplied instance assumptions.

The paper's shell setup requires integer `l₀ ≥ 1` and integer `u ≥ 1` (`paper/sec4-periodic-gap.tex:10–15`). The only use of `geometryThreshold` is `ShellGeometryStatement` (`lean/AKLT/Blueprint/Top/Windows.lean:11–13`), which explicitly requires `1 ≤ l₀` and `geometryThreshold l₀ ≤ u`. Positive integers are faithfully represented by these natural numbers with the positivity hypothesis. The threshold is always at least `16^4 = 65536`, so the latter hypothesis also supplies the paper's positivity of `u`. The threshold depends only on `l₀`, before quantification over translations, exterior seeds, and radii, as intended; no additional geometric or analytic assumption is embedded in it.

Non-blocking remarks:

- The function also assigns a value at `l₀ = 0`. This harmless total extension does not enlarge the domain of the consuming statement, which excludes zero explicitly.
- As an arithmetic cross-check, the values at `l₀ = 1`, `2`, and `64` are respectively `65536`, `104976`, and `23134410000`. The last equals `390^4`, agreeing with the paper's explicit `M_g(64)` at `paper/sec5-window.tex:600`.
- Read the entire `Geometry.lean` and its sole consumer file; checked the relevant arithmetic and order meanings supplied by its `Mathlib` import. No Lean process was needed, and no input was modified. Other declarations are outside this verdict.
