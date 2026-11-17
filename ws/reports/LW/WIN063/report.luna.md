STATUS: PARTIAL

## Files

- `/home/ubuntu/aklt/wt/LW_WIN063/AKLT/W/WIN063/Main.lean`
- `/home/ubuntu/aklt/reports/LW/WIN063/report.md`

## Delivered declarations

The exact requested declaration `AKLT.W.WIN063.main : AKLT.Blueprint.Win.FrameFibreSumStatement` is not proved in this partial delivery.

The finite-configuration reindexing is proved:

- `AKLT.W.WIN063.marginalNumerator_eq_sum_glue {κ} (hBF : B ⊆ F) (η) (s)` states that `marginalNumerator κ F B η s` equals the sum of `planeWeight` over glued configurations `glueConfig s n`, for `n : PlaneConfiguration (F \ B)`.
- `AKLT.W.WIN063.configEquiv hBF` is the equivalence from configurations on `F` to configurations on `B × (F \ B)`; `glueConfig` and `splitConfig` define its inverse maps.

The complementary term is related to the defined frame partition sum:

- `AKLT.W.WIN063.complementaryFrameTerm κ G τ n` is one summand of the complementary frame sum, written over configurations on `G`.
- `AKLT.W.WIN063.framePinnedSum_eq_complementaryFrameTerm κ G τ` proves its sum equals `framePinnedSum κ G ∅ τ`.
- `AKLT.W.WIN063.main_of_residual_factorization (hfactor)` proves `AKLT.Blueprint.Win.FrameFibreSumStatement` assuming the residual below.

The explicit remaining obligation is the closed proposition `AKLT.W.WIN063.Residual_FibreIntegrandFactorization`. It asks, for each fixed split configuration, for the pointwise identity

`planeWeight κ F η (glueConfig s n) = windowWeight κ B s * complementaryFrameTerm κ (F \ B) (cutPins κ (F \ B) F B unit η s) n`.

This is smaller than the original summed statement: the sum reindexing, scalar extraction, and identification with `framePinnedSum` are already proved. The unresolved work is to partition the internal-bond and original-leg products, mapping every bond crossing from `B` into `F \ B` to the corresponding original leg of the complementary volume, and to use the no-exterior-neighbour hypothesis for the boundary factors.

All declarations exported from `AKLT.W.WIN063` in `Main.lean` are listed here; the residual and principal conditional theorem are described above.

- `mem_pos (x y) : y ∈ positiveNeighbours x ↔ y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1)`.
- `mem_orig (G) (x y) : (x,y) ∈ originalLegs G ↔ x ∈ G ∧ y ∉ G ∧ y ∈ neighbours x`.
- `mem_bonds (G) (x y) : (x,y) ∈ internalBonds G ↔ x ∈ G ∧ y ∈ G ∧ y ∈ positiveNeighbours x`.
- `add_east (x) : x + (1,0) = (x.1+1,x.2)`; `add_north (x) : x + (0,1) = (x.1,x.2+1)`; `add_west (x) : x + (-1,0) = (x.1 + -1,x.2)`; `add_south (x) : x + (0,-1) = (x.1,x.2 + -1)`.
- `neigh_pos_cover {x y} (h : y ∈ neighbours x) : y ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours y`.
- `adjacent_of_mem_neighbours {x y} (h : y ∈ neighbours x) : Adjacent x y`.
- `pos_asymm {x y} (h : y ∈ positiveNeighbours x) : x ∉ positiveNeighbours y`.
- `pos_mem_neigh {x y} (h : y ∈ positiveNeighbours x) : y ∈ neighbours x ∧ x ∈ neighbours y`.
- `glueConfig {F B} (s : PlaneConfiguration B) (n : PlaneConfiguration (F \ B)) : PlaneConfiguration F`, using `s` on `B` and `n` on `F \ B`.
- `splitConfig {F B} (hBF : B ⊆ F) (σ : PlaneConfiguration F) : PlaneConfiguration B × PlaneConfiguration (F \ B)`.
- `configEquiv {F B} (hBF : B ⊆ F) : PlaneConfiguration F ≃ PlaneConfiguration B × PlaneConfiguration (F \ B)`.
- `sdiffEmptySubtypeEquiv (G) : ↥(G \ ∅) ≃ ↥G`.
- `configSdiffEmptyEquiv (G) : PlaneConfiguration (G \ ∅) ≃ PlaneConfiguration G`.
- `complementaryFrameTerm (κ) (G) (τ : PinAssignment G) (n : PlaneConfiguration G) : ℝ`, the single summand displayed in the file.
- `configSdiffEmptyEquiv_same (G) (n) (z : G) : (configSdiffEmptyEquiv G n) z = n ⟨z.1, by simp⟩`.
- `frameSpins_sdiffEmpty (κ) (G) (n : PlaneConfiguration (G \ ∅)) (z) : frameSpins κ n z = frameSpins κ (configSdiffEmptyEquiv G n) z`.
- `framePinnedSum_eq_complementaryFrameTerm (κ) (G) (τ) : framePinnedSum κ G ∅ τ = ∑ n : PlaneConfiguration G, complementaryFrameTerm κ G τ n`.

## Axioms

`#print axioms` was run on every exported theorem in `Main.lean`:

```text
mem_pos: [propext, Classical.choice, Quot.sound]
mem_orig: [propext, Classical.choice, Quot.sound]
mem_bonds: [propext, Classical.choice, Quot.sound]
add_east: [propext]
add_north: [propext]
add_west: [propext]
add_south: [propext]
neigh_pos_cover: [propext, Classical.choice, Quot.sound]
adjacent_of_mem_neighbours: [propext, Classical.choice, Quot.sound]
pos_asymm: [propext, Classical.choice, Quot.sound]
pos_mem_neigh: [propext, Classical.choice, Quot.sound]
marginalNumerator_eq_sum_glue: [propext, Classical.choice, Quot.sound]
configSdiffEmptyEquiv_same: [propext, Classical.choice, Quot.sound]
frameSpins_sdiffEmpty: [propext, Classical.choice, Quot.sound]
framePinnedSum_eq_complementaryFrameTerm: [propext, Classical.choice, Quot.sound]
main_of_residual_factorization: [propext, Classical.choice, Quot.sound]
```

Only the allowed axioms occur. No `sorry`, `admit`, or user-declared axioms are used.

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/WIN063/Main.lean` — succeeds.
- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.WIN063.Main` — succeeds; 13.85 s total, module replay/build reported as 6.3 s.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/win063_axioms.lean` — succeeds; prints the axiom list above.

## ORCH-SUMMARY

- Delivered compiled partial module `AKLT/W/WIN063/Main.lean` and this report.
- Proved configuration splitting/reindexing and the complementary sum identification.
- Open exact proposition: `AKLT.W.WIN063.Residual_FibreIntegrandFactorization`.
- Consequently the requested declaration `AKLT.W.WIN063.main` is not yet present.
- No falsehood or missing-hypothesis counterexample was found; this is unfinished product bookkeeping.
- All exported theorem axioms are among `propext`, `Classical.choice`, and `Quot.sound`.
- Build: `lake build AKLT.W.WIN063.Main` succeeds.
