STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP018/AKLT/W/GAP018/Main.lean)
- [report.md](/home/ubuntu/aklt/reports/LW/GAP018/report.md)

## Exported declaration

`AKLT.W.GAP018.main : AKLT.Blueprint.Gap.ConditionalBlockComparisonStatement`

The fibre decomposition, conditional expectation identities, and weighted block integration lemmas are private implementation details. The proof weights each conditional block Poincare inequality by its exterior fibre mass, identifies conditioning on the block and then on one block site with the original one-site conditional fibre, and sums over labels. The final finite-sum identity retains label multiplicity, including repeated, identical, and empty blocks.

## Axioms

`#print axioms AKLT.W.GAP018.main`:

```text
'AKLT.W.GAP018.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP018.Main` — successful; 12.7 seconds wall time (Lean module build: 7.4 seconds).
- `lake env lean /tmp/printGAP018.lean` — printed the theorem declaration and axiom dependencies above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered the exact requested theorem in `AKLT/W/GAP018/Main.lean`.
- Status: proved and module build successful.
- The only public declaration is `AKLT.W.GAP018.main` with the frozen statement type.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Repeated labels count separately; empty and identical blocks are included by the finite-sum proof.
- No residual statements, limitations, or deviations remain.
- Orchestrator action: none.
