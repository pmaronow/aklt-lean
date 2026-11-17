STATUS: COMPLETE

| Leaf | Paper label | Verdict | Reason | Fix | Difficulty |
| --- | --- | --- | --- | --- | --- |
| `AKLT.Blueprint.Win.TailThresholdStatement` | `t:cutMOS` | TRUE | The supplied bound is at most one once the radius dominates the square of the finite positive tail constant. | None | medium |
| `AKLT.Blueprint.Win.FrameWeightPositiveStatement` | `l:threeframes` | TRUE | Proper colouring makes every interaction a cross-frame interaction with a strictly positive lower bound. | None | easy |

Audited the read-only repository on `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, against the manuscript sources. Both leaves are self-sufficient implications with their dependencies explicitly included as hypotheses. Neither requires a missing premise or has an unintended vacuity. No proofs were written and no repository files were changed.

**`AKLT.Blueprint.Win.TailThresholdStatement`**

Exact statement, from [NodesTail.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTail.lean:15):

```lean
def TailThresholdStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 →
    (∀ u : ℕ, 1 ≤ u → tailCost θ u ≤ tailConstant θ * shellSpacing u ^ (-2 : ℤ)) →
    ∃ M : ℕ, 1 ≤ M ∧ geometryThreshold 64 ≤ M ∧
      ∀ u : ℕ, M ≤ u → tailCost θ u ≤ 1
```

The complete project-definition dependency trace is:

- [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:140): `tailCost θ u = 4 * (2 * (u : ℝ) + 1)^2 * θ^(shellSpacing u / 12 - 1)` and `tailConstant θ = 36 * θ⁻¹ * (Nat.factorial 10 : ℝ) * (12 / (-Real.log θ))^10`.
- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:83): `shellSpacing u = Real.sqrt (Real.sqrt (u : ℝ))`.
- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:119): `geometryThreshold l₀ = (max 16 (6 * (l₀ + 1)))^4`, hence `geometryThreshold 64 = 390^4 = 23134410000`.

The exact witness suggested by the paper is available: with `K = tailConstant θ`, take `M = max (geometryThreshold 64) (max 1 (Nat.ceil (K^2)))`. Here `K` is finite and positive because `θ > 0` and `Real.log θ < 0`. The relation `(shellSpacing u)^2 = Real.sqrt (u : ℝ)` explains why the square `K^2` is the correct radius threshold. This matches [sec5-window.tex, lines 714–733](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:714). The exponential estimate from the preceding paragraph of the paper is already an explicit hypothesis of this leaf.

Two-line proof route:

1. Choose a natural `M` dominating `geometryThreshold 64`, `1`, and the real number `K^2`.
2. For `u ≥ M`, obtain `K ≤ (shellSpacing u)^2` using square-root monotonicity, rewrite the integer power `−2` as a reciprocal, and apply the assumed tail bound.

Lean traps checked:

- The exponent inside `tailCost` is real: `/ 12 - 1` uses real division and subtraction. The exponent `(-2 : ℤ)` in the hypothesis is an integer power. Rewriting it requires the integer-power inverse laws before using a real division inequality.
- `M ≥ 1` ensures `u ≥ 1` and strictly positive spacing. Thus the reciprocal cannot invoke Lean's totalized inverse at zero.
- `Nat.ceil` must act on the real `K^2`; compare its result with `u` in `ℕ`, then cast the inequality to `ℝ`. `Nat.le_ceil` supplies the required real lower bound. There is no rational truncation or natural-number subtraction in these definitions.
- The quantifier order gives one threshold for every later integer radius. It may depend on `θ` and has no volume, colouring, boundary, or placement dependency.
- There are no instance arguments to be silently dropped. The hypotheses `0 < θ < 1` are consistent, and the supplied estimate is precisely the paper's preceding exponential bound, so this is not an unintended vacuous implication.

Difficulty: **medium**, mainly for square-root, ceiling, cast, and integer-power bookkeeping.

**`AKLT.Blueprint.Win.FrameWeightPositiveStatement`**

Exact statement, from [NodesCut.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:100):

```lean
def FrameWeightPositiveStatement : Prop :=
  AKLT.Blueprint.Top.ThreeFramesStatement →
    ∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ F : Finset Plane,
    ∀ η : FrameBoundary F, ∀ σ : PlaneConfiguration F, 0 < planeWeight κ F η σ
```

The project-definition dependency trace is:

- [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:10): `ProperPlaneColouring κ` requires distinct colours at every adjacent pair in the entire plane. `PlaneConfiguration F` is `F → IcoLetter`; `exteriorSites F` is the image of `originalLegs F` under the second projection; `FrameBoundary F` is `exteriorSites F → IcoLetter`. `extendLetters` and `extendBoundary` use the given label on their respective finite domains and the valid label `(0, 0, 0)` elsewhere.
- [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:37): `planeWeight` is `(1 / 12 : ℝ)^F.card`, multiplied by a finite product of `1 + dot` factors over `internalBonds F`, then a finite product over `originalLegs F`. Every endpoint vector is `frameVector` at that endpoint's colour, including exterior endpoints.
- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): `Plane = ℤ × ℤ`; `latticeDist` sums the natural absolute values of integer coordinate differences; `Adjacent x y` means this distance is one. `positiveNeighbours` lists the east and north sites, and `internalBonds` keeps those lying in `F`. `neighbours` uses the four constructors of `Compass` and their unit `step` vectors; `originalLegs` pairs each site of `F` with its neighbours outside `F`. Both edge sets therefore contain only adjacent pairs.
- [Top/Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Quantum.lean:13): the full `ThreeFramesStatement` was read. Its conjuncts include rotation orthogonality and determinant, positivity and upper bounds for `frameBound` and `frameRatio`, injectivity/unit norms/antipodality and degree-four moment identities, both cross-frame interaction bounds and separation up to signs, and attainment. This leaf uses only `0 < frameBound` and the universally quantified lower bound for `1 + dot` at distinct colours.
- [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:33): `frameRotation` is the displayed real rational matrix; `frameVector j a = (frameRotation ^ j.val).mulVec (icoVector a)`; `frameBound = (5 - Real.sqrt 5) / 505`; `frameRatio = frameBound / (2 - frameBound)`.
- [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9): `Vec3 = Fin 3 → ℝ`, `dot` sums the three coordinate products, and `normSq a = dot a a`. `IcoLetter = Fin 3 × Fin 2 × Fin 2`; `signValue` gives the two independent signs; `goldenRatio = (1 + sqrt 5) / 2`; `icoRadius = sqrt (goldenRatio + 2)`. `icoVector` uses the three coordinate families `(0,a,b)`, `(a,b,0)`, `(b,0,a)` divided by that radius. `moment` averages over all twelve labels, and `DegreeFour p` means `p.totalDegree ≤ 4`. These cover the remaining project definitions inside the frame premise.

Every interaction factor is covered by the supplied cross-colour lower bound. The site-weight power is strictly positive over `ℝ`, and all products are finite. The statement agrees with [Lemma l:threeframes](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:341), the positivity explanation after [Definition d:framemodel](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:490), and the use in [sec5-window.tex](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:163).

Two-line proof route:

1. Extract positive `frameBound` and its cross-colour plus-interaction lower bound; use edge membership and proper colouring to obtain distinct colours for every factor.
2. Apply `Finset.prod_pos` to both edge products and multiply by the positive real power `(1 / 12)^F.card`; empty products equal one.

Lean traps checked:

- Both products use `∏ e ∈ edgeFinset`, with an explicit membership condition. No `Fintype Plane` is needed; finite subtypes and their function spaces have the required instances automatically.
- A boundary assigns frame-letter labels at exterior sites, and `planeWeight` evaluates each label in that exterior site's frame. This makes the cross-frame premise applicable to every original leg. No additional hypothesis on boundary directions is needed.
- `(1 / 12 : ℝ)` is a positive real number. All dot products and frame bounds are also real; there is no natural-number division or rational/real mismatch.
- `F = ∅` is allowed: both edge sets are empty, the site exponent is zero, and the weight equals one. Its configuration and boundary spaces each contain one assignment. This intended empty case does not make the general statement vacuous; proper plane colourings and nonempty finite volumes also exist.
- The default extensions always return an `IcoLetter`. Their dependent membership tests are indexing devices and do not discard the colouring hypothesis. Standard `classical` reasoning is available if needed during product/membership simplification; it is not a missing mathematical premise.

Difficulty: **easy**, with routine edge-membership and finite-product bookkeeping. The frame theorem itself is explicitly assumed.

**Verification artifacts.** [audit.lean](/home/ubuntu/aklt/reports/TS_WIN_10/audit.lean) contains inspection directives only. It imports the two existing compiled modules, prints both declarations and their principal definitions, synthesizes finite/nonempty instances for the empty configuration and boundary spaces, checks the relevant library declarations, and reduces the geometric threshold. Lean `4.35.0-rc2` completed successfully with exit code zero; see [audit.log](/home/ubuntu/aklt/reports/TS_WIN_10/audit.log). Package builds were reused through the local `.lake/packages` symlink; one Lean process was used and no module was rebuilt in the repository. These checks establish elaboration and instance behavior, while the truth verdicts come from the definition and manuscript audit above.
