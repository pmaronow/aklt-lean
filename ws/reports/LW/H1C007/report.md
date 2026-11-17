STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C007/AKLT/W/H1C007/Main.lean)

## Exported declaration

```lean
theorem AKLT.W.H1C007.main :
  AKLT.Cert.H1.Production.Leaves.inputCovered
```

The proof derives the covered-site status and kept-bond clauses from the finite raw options accepted by `inputCheck`. It handles center-to-axis bonds from the axial masks, including the missing incoming south bond, and proves cycle-edge reciprocity from `cornerCompatible` after relating mask bits to `keptAt` membership. The ring-option lookup proof uses `List.find?_eq_some_iff_getElem` and the ring-site list's `Nodup` property to establish the selected position without reducing the concrete search.

## Axioms

`#print axioms AKLT.W.H1C007.main`:

```text
'AKLT.W.H1C007.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake env lean AKLT/W/H1C007/Main.lean` — successful.
- `time lake build AKLT.W.H1C007.Main` — successful; Lake reported the target built in 37s, shell wall time 42.872s.
- `lake env lean AKLT/W/H1C007/Axioms.lean` — successful; temporary check file removed after inspection.

## Open issues

No proof gaps or residual assumptions. Lean reports unused-simp-argument and unreachable-fallback-tactic linter warnings in `Main.lean`; they do not affect the build.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C007/Main.lean` with `AKLT.W.H1C007.main` proving the requested `inputCovered` proposition.
- `lake build AKLT.W.H1C007.Main` succeeds.
- Exported theorem axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No helper files or existing files were changed.
- No open mathematical obligations or residual statements remain.
- Build emits only unused-simp-argument and unreachable-fallback-tactic warnings.
- Orchestrator action: accept the proved leaf.
