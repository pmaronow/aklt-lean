STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_WIN035/AKLT/W/WIN035/Main.lean): the three escape cases and the exact requested theorem.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_WIN035/AKLT/W/WIN035/Geometry.lean): outward steps, metric inequalities, square membership, and exterior membership of `y`.
- [Paths.lean](/home/ubuntu/aklt/wt/LW_WIN035/AKLT/W/WIN035/Paths.lean): target paths and escape from a finite set using an increasing natural potential.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_WIN035/AKLT/W/WIN035/Audit.lean): exact-type import check and axiom checks for every exported theorem.
- [build.log](/home/ubuntu/aklt/reports/LW/WIN035/build.log), [audit.log](/home/ubuntu/aklt/reports/LW/WIN035/audit.log): successful verification output.

All source changes are confined to `AKLT/W/WIN035/`. Frozen statement files and other project sources were not edited. The earlier partial report remains in `report.luna.md`.

## Result and proof

The requested declaration is proved without residual assumptions:

```lean
theorem AKLT.W.WIN035.main :
    AKLT.Blueprint.Win.ComplementEscapeStatement
```

Write `ρ(z) = supDist z y`, `k = shellRadius u i`, `t(z) = |ρ(z) - k|`, `h(z) = squareDepth a u z`, and `T = shellSpacing u / 12`.
For a point inside the square and outside the taper, either `t > T` or `h < t + 32`.

1. If `ρ ≥ k` and `t > T`, use outward steps from `y`. They increase `ρ` by one, so `t` cannot decrease. All sites in the upper radial region stay outside the taper. The natural measure `(square a u).sup (fun v => supDist v y) + 1 - ρ(z)` strictly decreases while the path stays in the square.
2. If `ρ < k` and `t > T`, use the earlier attempt's target-path idea, with a shorter integer-arithmetic proof of distance decrease. Each step toward `y` decreases Manhattan distance and does not increase `ρ`, so it cannot decrease `t` in this region. The endpoint `y` lies outside the square: otherwise the setup's set distance would be zero instead of one.
3. If `h < t + 32`, take outward steps from `a`. While starting inside the square, each step lowers `h` by exactly one, and nearest-neighbour Lipschitz continuity gives `t(next) ≥ t(current) - 1`. Thus the strict clearance inequality persists. The finite-square maximum of `supDist · a` supplies the decreasing termination measure. This works at `z = a` too, using the positive direction when the maximal coordinate displacement is zero.

A point already outside the square uses a reflexive path. The three paths are mapped into the taper complement by `joined_mono`.

No scale estimates or exceptional-index arguments are needed for this leaf: the only consequence of `CutSetup` used is that `y` is outside the square. No other blueprint leaf is imported as a proved lemma. The old residual assembly has been replaced by complete proofs of all three cases.

## Exported declarations and statements

The following is the complete `#check` output from `Audit.lean`, including both coordinate-step definitions and every exported theorem. Coercions in `supDist_lipschitz` and `offset_lipschitz` are to `ℤ`; the radial-band comparisons in the escape theorems are in `ℝ`.

```text
AKLT.W.WIN035.main : AKLT.Blueprint.Win.ComplementEscapeStatement
AKLT.W.WIN035.stepAway (c z : AKLT.Defs.Plane) : AKLT.Defs.Plane
AKLT.W.WIN035.stepAway_adj (c z : AKLT.Defs.Plane) : AKLT.Defs.Adjacent z (AKLT.W.WIN035.stepAway c z)
AKLT.W.WIN035.stepAway_supDist (c z : AKLT.Defs.Plane) :
  AKLT.Defs.supDist (AKLT.W.WIN035.stepAway c z) c = AKLT.Defs.supDist z c + 1
AKLT.W.WIN035.supDist_lipschitz {z w : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent z w) (c : AKLT.Defs.Plane) :
  ↑(AKLT.Defs.supDist z c) ≤ ↑(AKLT.Defs.supDist w c) + 1
AKLT.W.WIN035.offset_lipschitz {z w : AKLT.Defs.Plane} (h : AKLT.Defs.Adjacent z w) (y : AKLT.Defs.Plane) (u : ℕ)
  (i : ℤ) : ↑(AKLT.Blueprint.Win.radialOffset y u i z) ≤ ↑(AKLT.Blueprint.Win.radialOffset y u i w) + 1
AKLT.W.WIN035.mem_square_iff (a z : AKLT.Defs.Plane) (u : ℕ) : z ∈ AKLT.Defs.square a u ↔ AKLT.Defs.supDist z a ≤ u
AKLT.W.WIN035.setup_y_exterior {a y : AKLT.Defs.Plane} {u : ℕ} {i : ℤ} (hs : AKLT.Blueprint.Win.CutSetup a y u i) :
  y ∉ AKLT.Defs.square a u
AKLT.W.WIN035.joined_step {R : AKLT.Defs.Plane → AKLT.Defs.Plane → Prop} {S : Set AKLT.Defs.Plane}
  {x y : AKLT.Defs.Plane} (hx : x ∈ S) (hy : y ∈ S) (hxy : R x y) : AKLT.Blueprint.Win.JoinedIn R S x y
AKLT.W.WIN035.stepToward (x y : AKLT.Defs.Plane) : AKLT.Defs.Plane
AKLT.W.WIN035.stepToward_adj (x y : AKLT.Defs.Plane) (h : x ≠ y) : AKLT.Defs.Adjacent x (AKLT.W.WIN035.stepToward x y)
AKLT.W.WIN035.stepToward_dist_lt (x y : AKLT.Defs.Plane) (h : x ≠ y) :
  AKLT.Defs.latticeDist (AKLT.W.WIN035.stepToward x y) y < AKLT.Defs.latticeDist x y
AKLT.W.WIN035.stepToward_supDist_le (x y : AKLT.Defs.Plane) :
  AKLT.Defs.supDist (AKLT.W.WIN035.stepToward x y) y ≤ AKLT.Defs.supDist x y
AKLT.W.WIN035.joined_to_point {S : Set AKLT.Defs.Plane} (y : AKLT.Defs.Plane)
  (hclosed : ∀ x ∈ S, x ≠ y → AKLT.W.WIN035.stepToward x y ∈ S) (x : AKLT.Defs.Plane) :
  x ∈ S → AKLT.Blueprint.Win.JoinedIn AKLT.Defs.Adjacent S x y
AKLT.W.WIN035.joined_mono {R : AKLT.Defs.Plane → AKLT.Defs.Plane → Prop} {S T : Set AKLT.Defs.Plane} (hST : S ⊆ T)
  {x y : AKLT.Defs.Plane} (h : AKLT.Blueprint.Win.JoinedIn R S x y) : AKLT.Blueprint.Win.JoinedIn R T x y
AKLT.W.WIN035.escape_of_increasing (F : Finset AKLT.Defs.Plane) (S : Set AKLT.Defs.Plane) (f : AKLT.Defs.Plane → ℕ)
  (hstep : ∀ z ∈ F, z ∈ S → ∃ v ∈ S, AKLT.Defs.Adjacent z v ∧ f z < f v) (z : AKLT.Defs.Plane) :
  z ∈ S → ∃ w ∉ F, AKLT.Blueprint.Win.JoinedIn AKLT.Defs.Adjacent S z w
AKLT.W.WIN035.outer_escape (a y : AKLT.Defs.Plane) (u : ℕ) (i : ℤ) (z : AKLT.Defs.Plane)
  (hρ : AKLT.Defs.shellRadius u i ≤ ↑(AKLT.Defs.supDist z y))
  (ht : AKLT.Defs.shellSpacing u / 12 < ↑(AKLT.Blueprint.Win.radialOffset y u i z)) :
  ∃ w ∉ AKLT.Defs.square a u,
    AKLT.Blueprint.Win.JoinedIn AKLT.Defs.Adjacent {v | v ∉ AKLT.Blueprint.Win.taper a y u i} z w
AKLT.W.WIN035.inner_escape (a y : AKLT.Defs.Plane) (u : ℕ) (i : ℤ) (z : AKLT.Defs.Plane) (hy : y ∉ AKLT.Defs.square a u)
  (hρ : ↑(AKLT.Defs.supDist z y) < AKLT.Defs.shellRadius u i)
  (ht : AKLT.Defs.shellSpacing u / 12 < ↑(AKLT.Blueprint.Win.radialOffset y u i z)) :
  ∃ w ∉ AKLT.Defs.square a u,
    AKLT.Blueprint.Win.JoinedIn AKLT.Defs.Adjacent {v | v ∉ AKLT.Blueprint.Win.taper a y u i} z w
AKLT.W.WIN035.low_clearance_escape (a y : AKLT.Defs.Plane) (u : ℕ) (i : ℤ) (z : AKLT.Defs.Plane)
  (hz : AKLT.Blueprint.Win.squareDepth a u z < ↑(AKLT.Blueprint.Win.radialOffset y u i z) + 32) :
  ∃ w ∉ AKLT.Defs.square a u,
    AKLT.Blueprint.Win.JoinedIn AKLT.Defs.Adjacent {v | v ∉ AKLT.Blueprint.Win.taper a y u i} z w
```

## Axiom audit

Full `#print axioms` output for every exported theorem:

```text
'AKLT.W.WIN035.stepAway_adj' depends on axioms: [propext, Classical.choice]
'AKLT.W.WIN035.stepAway_supDist' depends on axioms: [propext, Quot.sound]
'AKLT.W.WIN035.supDist_lipschitz' depends on axioms: [propext, Quot.sound]
'AKLT.W.WIN035.offset_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.mem_square_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.setup_y_exterior' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.joined_step' does not depend on any axioms
'AKLT.W.WIN035.stepToward_adj' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.stepToward_dist_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.stepToward_supDist_le' depends on axioms: [propext, Quot.sound]
'AKLT.W.WIN035.joined_to_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.joined_mono' does not depend on any axioms
'AKLT.W.WIN035.escape_of_increasing' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.outer_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.inner_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.low_clearance_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN035.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the allowed axioms `propext`, `Classical.choice`, and `Quot.sound` occur. There are no unproved residual propositions, proof placeholders, added assumptions, or forbidden proof mechanisms.

## Builds and timings

With `$HOME/.elan/bin` added to `PATH`:

```text
lake build AKLT.W.WIN035.Main
```

Succeeded after the final source cleanup: **18.55 seconds wall time**. Lake reported 4.4 seconds for `Geometry`, 3.6 seconds for `Paths`, and 3.3 seconds for `Main`. Dependencies were already built. No warnings were emitted.

```text
lake env lean AKLT/W/WIN035/Audit.lean
```

Succeeded: **3.74 seconds wall time**. In particular,
`#check (AKLT.W.WIN035.main : AKLT.Blueprint.Win.ComplementEscapeStatement)` succeeds through an import of `Main`.

## Open issues

None.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.WIN035.main : AKLT.Blueprint.Win.ComplementEscapeStatement` in `AKLT/W/WIN035/Main.lean`.
- Helpers are in `Geometry.lean` and `Paths.lean`; `Audit.lean` checks the exact type and all exported theorem axioms.
- All three escape cases are proved; no residual statements or conditional assembly remain.
- Only allowed axioms occur: `propext`, `Classical.choice`, `Quot.sound`.
- Main build and import-level exact-type audit both pass.
- No frozen definitions or files outside the task directory were changed.
- Deviation: the low-clearance path also handles the square centre directly; scale estimates are unnecessary.
- Limitations: none. Open declaration names: none.
- Orchestrator action: accept the leaf and include the four Lean files; no further mathematical premise or decision is required.
