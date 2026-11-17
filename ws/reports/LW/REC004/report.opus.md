STATUS: PROVED

Files changed (all under /home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/):
- Expansion.lean (new, 295 lines): proves the open residual `Residual_FibreExpansion` as `AKLT.W.REC004.fibreExpansion`.
- Main.lean: imports Expansion and adds `theorem main := main_from_residuals fibreExpansion`. The `#print axioms` lines were moved out of Main.lean, and the docstring of `main_from_residuals` was updated.
- Audit.lean: adds `#check`/`#print axioms` for pad_fields, bond_split3, config_identity, expansion_general, fibreExpansion and main.
No file outside AKLT/W/REC004/ was edited.

Final theorem as it compiles:
  theorem AKLT.W.REC004.main : AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement

#print axioms AKLT.W.REC004.main:
  'AKLT.W.REC004.main' depends on axioms: [propext, Classical.choice, Quot.sound]
(fibreExpansion and expansion_general report the same three axioms.)

Build: cd /home/ubuntu/aklt/wt/LW_REC004 && lake build AKLT.W.REC004.Main
Result: Build completed successfully (8964 jobs), with no warnings or errors. Expansion took 4.6 s, Main 4.5 s, 13.6 s wall in total. `lake build AKLT.W.REC004.Audit` also succeeds.
Source scan: no sorry, admit, axiom, native_decide, implemented_by, unsafe, opaque, extern, #eval or maxHeartbeats.

How the residual was proved (it is true as stated; no restatement was needed):
- Imported leaf REC002 (`AKLT.W.REC002.Bonds`) for spinSum/partition_spinSum, one-site integration `spinSum_insert` and the bond split `bondProduct_remove`.
- Write D' = removeSite D y and W = ((D'.active.erase o).erase g).erase f, so that D'.active = insert o (insert g (insert f W)). Integrating out o, g and f gives a spin sum over W of three nested site functionals.
- `bond_split3`: removing o, g and f in turn splits the bond product into a product over the remaining network and three products of incident factors. This uses the proved nonadjacency of the three neighbours (`neighbours_nonadjacent`).
- `legProduct_update`: the leg factors do not see the three neighbour spins, because no original leg starts at a neighbour (`no_leg_at_neighbour`).
- `pad_fields`: an incident set with at most 3 elements is listed as exactly 3 letters, padded with the zero letter (`neighbour_removed_card` gives the bound, and passing to `removeSite` only shrinks the set). Letters come from `letterOf`, using `extend = spinVector ∘ letterOf`.
- `config_identity`: algebra for one outside configuration. C(n) = (outside weights) * (outside bonds) * (legs) >= 0.
- The index set W -> SpinLetter is reindexed to Fin N with Fintype.equivFin.
- Statuses: s = ![status f, status g, status o], each U or D by `neighbour_survives`.

Remaining residuals: none.
