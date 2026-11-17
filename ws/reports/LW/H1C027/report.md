STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C027/AKLT/W/H1C027/Main.lean)

## Exported declarations

- `AKLT.W.H1C027.find_some_mem_entries`:
  `∀ (t : Catalogue) (x p : Nat), t.find x = some p → (x, p) ∈ t.entries`.
- `AKLT.W.H1C027.main`:
  `AKLT.Cert.H1.Production.Leaves.representativeLookup`.

The proof uses structural induction on the catalogue: any successful `find` follows one branch and therefore identifies a pair present in `entries`. The checked equality between `entries` and the mapped representative list then supplies the representative and its key and pid. No BST ordering premise is used.

## Axioms

`#print axioms main` output:

```text
'AKLT.W.H1C027.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are all permitted axioms.

## Build

- Command: `lake build AKLT.W.H1C027.Main`
- Result: successful, exit code 0.
- Wall time: 13.04 seconds total; Lean reported 5.8 seconds for the target module.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C027.main` with the requested exact statement.
- Generic tree induction establishes successful lookup membership in `Catalogue.entries` without ordering assumptions.
- The representative check turns that membership into a checked representative entry.
- Build passed with `lake build AKLT.W.H1C027.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No open issues or deviations.
