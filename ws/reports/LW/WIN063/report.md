STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_WIN063/AKLT/W/WIN063/Main.lean`: configuration splitting, complementary sum identification, pointwise weight factorization, and the requested theorem.
- `/home/ubuntu/aklt/wt/LW_WIN063/AKLT/W/WIN063/Edges.lean`: lattice membership lemmas and the symmetric edge product splitting theorem.
- `/home/ubuntu/aklt/reports/LW/WIN063/Check.lean`: archived source of the independent exact-type and axiom checks.
- `/home/ubuntu/aklt/reports/LW/WIN063/validation.log`: complete successful validation output.

The earlier report is preserved as `report.luna.md`.

## Result and proof

The requested declaration is present with exactly the required name and type:

```lean
theorem AKLT.W.WIN063.main : AKLT.Blueprint.Win.FrameFibreSumStatement
```

Split each configuration on `F` into its restrictions to `B` and `G = F \ B`. Reindex the marginal numerator as a sum over configurations on `G` using this equivalence.

For the pointwise factorization, orient every physical edge positively. The original-leg orientation map is injective, and reversing an edge preserves its interaction factor. Because `B` has no neighbour outside `F`, the edges meeting `F` are the disjoint union of the bonds internal to `B` and the edges meeting `G`. This yields `split_edge_products` for any symmetric real edge factor. Fill the spins with the glued configuration inside `F` and the boundary letters outside `F`. The pins from `cutPins` then agree with the filled spin at each exterior endpoint of an original leg of `G`.

The cardinality identity `|F| = |B| + |F \ B|` splits the site weights. Consequently `fibre_integrand_factorization` proves the exact identity of individual weight summands. Sum that identity, extract the window weight, and identify the remaining sum with `framePinnedSum`.

This algebraic argument does not use the ThreeFrames or proper-colouring hypotheses; `main` accepts them as specified by the frozen statement. Unit norms are used to form the prescribed pins. Empty windows and empty complementary volumes are included.

No other blueprint leaf is imported or used. The previous explicit residual has been proved and removed; there are no residual assumptions.

## Exported declarations and axiom checks

Below are the exact `#check` signatures for every public declaration and the `#print axioms` output for every public theorem. All names are in `AKLT.W.WIN063`. The independent check also contains:

```lean
example : AKLT.Blueprint.Win.FrameFibreSumStatement := AKLT.W.WIN063.main
```

```text
AKLT.W.WIN063.main : AKLT.Blueprint.Win.FrameFibreSumStatement
AKLT.W.WIN063.mem_pos (x y : AKLT.Defs.Plane) :
  y ∈ AKLT.Defs.positiveNeighbours x ↔ y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1)
'AKLT.W.WIN063.mem_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.mem_orig (G : Finset AKLT.Defs.Plane) (x y : AKLT.Defs.Plane) :
  (x, y) ∈ AKLT.Defs.originalLegs G ↔ x ∈ G ∧ y ∉ G ∧ y ∈ AKLT.Defs.neighbours x
'AKLT.W.WIN063.mem_orig' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.mem_bonds (G : Finset AKLT.Defs.Plane) (x y : AKLT.Defs.Plane) :
  (x, y) ∈ AKLT.Defs.internalBonds G ↔ x ∈ G ∧ y ∈ G ∧ y ∈ AKLT.Defs.positiveNeighbours x
'AKLT.W.WIN063.mem_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.add_east (x : AKLT.Defs.Plane) : x + (1, 0) = (x.1 + 1, x.2)
'AKLT.W.WIN063.add_east' depends on axioms: [propext]
AKLT.W.WIN063.add_north (x : AKLT.Defs.Plane) : x + (0, 1) = (x.1, x.2 + 1)
'AKLT.W.WIN063.add_north' depends on axioms: [propext]
AKLT.W.WIN063.add_west (x : AKLT.Defs.Plane) : x + (-1, 0) = (x.1 + -1, x.2)
'AKLT.W.WIN063.add_west' depends on axioms: [propext]
AKLT.W.WIN063.add_south (x : AKLT.Defs.Plane) : x + (0, -1) = (x.1, x.2 + -1)
'AKLT.W.WIN063.add_south' depends on axioms: [propext]
AKLT.W.WIN063.neigh_pos_cover {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.neighbours x) :
  y ∈ AKLT.Defs.positiveNeighbours x ∨ x ∈ AKLT.Defs.positiveNeighbours y
'AKLT.W.WIN063.neigh_pos_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.adjacent_of_mem_neighbours {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.neighbours x) :
  AKLT.Defs.Adjacent x y
'AKLT.W.WIN063.adjacent_of_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.pos_asymm {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.positiveNeighbours x) :
  x ∉ AKLT.Defs.positiveNeighbours y
'AKLT.W.WIN063.pos_asymm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.pos_mem_neigh {x y : AKLT.Defs.Plane} (h : y ∈ AKLT.Defs.positiveNeighbours x) :
  y ∈ AKLT.Defs.neighbours x ∧ x ∈ AKLT.Defs.neighbours y
'AKLT.W.WIN063.pos_mem_neigh' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.split_edge_products {F B : Finset AKLT.Defs.Plane} (hBF : B ⊆ F)
  (hNo : AKLT.Blueprint.Win.NoBond ↑B {z | z ∉ F}) (f : AKLT.Defs.Plane × AKLT.Defs.Plane → ℝ)
  (hsymm : ∀ (e : AKLT.Defs.Plane × AKLT.Defs.Plane), f e.swap = f e) :
  (∏ e ∈ AKLT.Defs.internalBonds F, f e) * ∏ e ∈ AKLT.Defs.originalLegs F, f e =
    (∏ e ∈ AKLT.Defs.internalBonds B, f e) *
      ((∏ e ∈ AKLT.Defs.internalBonds (F \ B), f e) * ∏ e ∈ AKLT.Defs.originalLegs (F \ B), f e)
'AKLT.W.WIN063.split_edge_products' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.glueConfig {F B : Finset AKLT.Defs.Plane} (s : AKLT.Defs.PlaneConfiguration B)
  (n : AKLT.Defs.PlaneConfiguration (F \ B)) : AKLT.Defs.PlaneConfiguration F
AKLT.W.WIN063.splitConfig {F B : Finset AKLT.Defs.Plane} (hBF : B ⊆ F) (σ : AKLT.Defs.PlaneConfiguration F) :
  AKLT.Defs.PlaneConfiguration B × AKLT.Defs.PlaneConfiguration (F \ B)
AKLT.W.WIN063.configEquiv {F B : Finset AKLT.Defs.Plane} (hBF : B ⊆ F) :
  AKLT.Defs.PlaneConfiguration F ≃ AKLT.Defs.PlaneConfiguration B × AKLT.Defs.PlaneConfiguration (F \ B)
AKLT.W.WIN063.marginalNumerator_eq_sum_glue {κ : AKLT.Defs.Plane → Fin 3} {F B : Finset AKLT.Defs.Plane} (hBF : B ⊆ F)
  (η : AKLT.Defs.FrameBoundary F) (s : AKLT.Defs.PlaneConfiguration B) :
  AKLT.Blueprint.Win.marginalNumerator κ F B η s = ∑ n, AKLT.Defs.planeWeight κ F η (AKLT.W.WIN063.glueConfig s n)
'AKLT.W.WIN063.marginalNumerator_eq_sum_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.sdiffEmptySubtypeEquiv (G : Finset AKLT.Defs.Plane) : ↥(G \ ∅) ≃ ↥G
AKLT.W.WIN063.configSdiffEmptyEquiv (G : Finset AKLT.Defs.Plane) :
  AKLT.Defs.PlaneConfiguration (G \ ∅) ≃ AKLT.Defs.PlaneConfiguration G
AKLT.W.WIN063.complementaryFrameTerm (κ : AKLT.Defs.Plane → Fin 3) (G : Finset AKLT.Defs.Plane)
  (τ : AKLT.Defs.PinAssignment G) (n : AKLT.Defs.PlaneConfiguration G) : ℝ
AKLT.W.WIN063.configSdiffEmptyEquiv_same (G : Finset AKLT.Defs.Plane) (n : AKLT.Defs.PlaneConfiguration (G \ ∅))
  (z : ↥G) : (AKLT.W.WIN063.configSdiffEmptyEquiv G) n z = n ⟨↑z, ⋯⟩
'AKLT.W.WIN063.configSdiffEmptyEquiv_same' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.frameSpins_sdiffEmpty (κ : AKLT.Defs.Plane → Fin 3) (G : Finset AKLT.Defs.Plane)
  (n : AKLT.Defs.PlaneConfiguration (G \ ∅)) (z : AKLT.Defs.Plane) :
  AKLT.Blueprint.Win.frameSpins κ n z = AKLT.Blueprint.Win.frameSpins κ ((AKLT.W.WIN063.configSdiffEmptyEquiv G) n) z
'AKLT.W.WIN063.frameSpins_sdiffEmpty' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.framePinnedSum_eq_complementaryFrameTerm (κ : AKLT.Defs.Plane → Fin 3) (G : Finset AKLT.Defs.Plane)
  (τ : AKLT.Defs.PinAssignment G) :
  AKLT.Blueprint.Win.framePinnedSum κ G ∅ τ = ∑ n, AKLT.W.WIN063.complementaryFrameTerm κ G τ n
'AKLT.W.WIN063.framePinnedSum_eq_complementaryFrameTerm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.fibre_integrand_factorization (κ : AKLT.Defs.Plane → Fin 3) {F B : Finset AKLT.Defs.Plane} (hBF : B ⊆ F)
  (hNo : AKLT.Blueprint.Win.NoBond ↑B {z | z ∉ F})
  (unit : ∀ (j : Fin 3) (a : AKLT.Defs.IcoLetter), AKLT.Defs.normSq (AKLT.Defs.frameVector j a) = 1)
  (η : AKLT.Defs.FrameBoundary F) (s : AKLT.Defs.PlaneConfiguration B) (n : AKLT.Defs.PlaneConfiguration (F \ B)) :
  AKLT.Defs.planeWeight κ F η (AKLT.W.WIN063.glueConfig s n) =
    AKLT.Blueprint.Win.windowWeight κ B s *
      AKLT.W.WIN063.complementaryFrameTerm κ (F \ B) (AKLT.Blueprint.Win.cutPins κ (F \ B) F B unit η s) n
'AKLT.W.WIN063.fibre_integrand_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.WIN063.main : AKLT.Blueprint.Win.FrameFibreSumStatement
'AKLT.W.WIN063.main' depends on axioms: [propext, Classical.choice, Quot.sound]
CHECK_ELAPSED_SECONDS=5.49
```


Only the allowed axioms `propext`, `Classical.choice`, and `Quot.sound` occur.

## Builds and verification

Commands were run from `/home/ubuntu/aklt/wt/LW_WIN063` with `$HOME/.elan/bin` on `PATH`.

- `lake build AKLT.W.WIN063.Edges` — succeeded; Lean module build reported 4.5 seconds.
- `/usr/bin/time -f 'BUILD_ELAPSED_SECONDS=%e' lake build AKLT.W.WIN063.Main` — succeeded without warnings; 10.12 seconds wall time, Lean module build reported 5.2 seconds.
- `/usr/bin/time -f 'CHECK_ELAPSED_SECONDS=%e' lake env lean /tmp/win063_check.lean` — succeeded; 5.49 seconds wall time. Its source is archived as `Check.lean` next to this report, and its full output is `validation.log`.
- Source scan of both delivered Lean files found none of the forbidden proof shortcuts or declarations.
- Working tree inspection showed changes only under `AKLT/W/WIN063/`; no existing file outside the assigned directory was edited.

## Open issues

None.

## ORCH-SUMMARY

- STATUS: PROVED.
- Exact deliverable: `AKLT.W.WIN063.main : AKLT.Blueprint.Win.FrameFibreSumStatement`.
- Proof files: `AKLT/W/WIN063/Main.lean` and `AKLT/W/WIN063/Edges.lean`.
- Reused the prior attempt's configuration equivalence and finite-sum reindexing.
- Completed the symmetric edge product split and pointwise weight factorization.
- Removed the previous residual proposition and conditional principal theorem.
- No other blueprint leaf dependencies.
- Exact-type import check passed.
- Every public theorem's axioms are allowed.
- Final module build passed without warnings, 10.12 seconds wall time.
- Open names: none. Limitations or deviations: none.
- No orchestrator decision or additional work is required.
