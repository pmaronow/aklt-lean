STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C009/AKLT/W/H1C009/Main.lean): The exact requested theorem, compiler-spec decoding, suffix strides, and accepted tables.
- [Raw.lean](/home/ubuntu/aklt/wt/LW_H1C009/AKLT/W/H1C009/Raw.lean): Raw-option validity, ring lookup, statuses, kept directions, and the explicit sixteen-edge template.
- [Degrees.lean](/home/ubuntu/aklt/wt/LW_H1C009/AKLT/W/H1C009/Degrees.lean): Edge orientation and the one-edge tip / two-edge corner incidence and degree formulas.
- [Edges.lean](/home/ubuntu/aklt/wt/LW_H1C009/AKLT/W/H1C009/Edges.lean): The sixteen raw edge bits agree with actual Defs bonds.
- [Groups.lean](/home/ubuntu/aklt/wt/LW_H1C009/AKLT/W/H1C009/Groups.lean): Group locations, leader indices, inversion membership, degrees, and slot counts.
- [Fields.lean](/home/ubuntu/aklt/wt/LW_H1C009/AKLT/W/H1C009/Fields.lean): Left/right/center bonds, dimensions, dilution, leaf flags, and tip flags.

All six Lean files are transitively imported by `Main.lean`. No source files outside `AKLT/W/H1C009/` were changed. The earlier report remains in `report.luna.md`.

## Exported declarations

```lean
theorem AKLT.W.H1C009.main :
  AKLT.Cert.H1.Production.Leaves.compilerGeometry
```

The theorem has exactly the required closed type. There are no residual assumptions or unproved dependencies. No other blueprint-leaf proofs are imported.

The complete Lean-printed statements of all 43 exported theorems, the three transparent data helpers, and the `LawfulBEq RawOption` instance are in [signatures.log](/home/ubuntu/aklt/reports/LW/H1C009/signatures.log).

## Proof

The input checker supplies valid axial and corner statuses. The proof identifies the raw edge bits with the actual bonds by checking the fixed sixteen-edge topology and decoding the kept directions. It then counts incident bonds at the four corners and four tip endpoints, and applies the definitions of reduction groups and single replacements to derive the compiled slot counts.

For tips, the group is at the tip endpoint and has at most one slot; its dimension therefore does not depend on the adjacent axial status. The dilution flag uses the adjacent ring site, as required. Corners use their own status and the selected representation. Group-leader values are proved equal to the raw leader indices before transferring inversion membership; the Fin equality in that transfer is proved by `Fin.ext`.

Finally, `geometryCheck` identifies every packed specification with `inputSpec`. A list-extensionality proof identifies the dimension lists and suffix products, and `TablesAccepted` supplies the table-check field directly.

## Axioms

`#print axioms AKLT.W.H1C009.main`:

```text
'AKLT.W.H1C009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every exported theorem and the exported instance were audited. All use only the three allowed axioms; `groupPoint_odd` uses only `propext`. The full output is in [check.log](/home/ubuntu/aklt/reports/LW/H1C009/check.log).

## Validation

With `PATH="$HOME/.elan/bin:$PATH"`:

```sh
lake build AKLT.W.H1C009.Main
```

Success, wall time 32.03 seconds. This final build recompiled the changed helper modules and `Main`; its log is [build.log](/home/ubuntu/aklt/reports/LW/H1C009/build.log), with timings in [build-time.txt](/home/ubuntu/aklt/reports/LW/H1C009/build-time.txt). The task's modules emit no warnings; the build replays existing dependency warnings.

A separate import check used:

```lean
import AKLT.W.H1C009.Main
example : AKLT.Cert.H1.Production.Leaves.compilerGeometry := AKLT.W.H1C009.main
#check (AKLT.W.H1C009.main : AKLT.Cert.H1.Production.Leaves.compilerGeometry)
#print axioms AKLT.W.H1C009.main
```

The exact-type check and the full exported-declaration axiom audit passed in 3.76 seconds (`lake env lean /tmp/H1C009Check.lean`). Printing all exported signatures passed in 3.81 seconds (`lake env lean /tmp/H1C009Signatures.lean`).

The source scan found none of the forbidden proof escapes. The import-graph check confirms that every delivered Lean file is imported by `Main.lean`.

## Open issues

None. Validation here used Lean's kernel; the campaign's independent-kernel recheck remains external.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C009/Main.lean` and five transitively imported helpers.
- Exact theorem: `AKLT.W.H1C009.main : AKLT.Cert.H1.Production.Leaves.compilerGeometry`.
- Status: PROVED directly from definitions and the statement's hypotheses.
- No residual statements, missing leaves, or extra assumptions.
- All raw edges, reduction-group slots, dimensions, flags, strides, and tables are covered.
- Tip endpoint groups and adjacent axial moment statuses are kept distinct.
- Final requested build and separate exact-type import check both passed.
- All 43 exported theorems and the exported instance use only allowed axioms.
- No external source files were edited and no sub-agents were used.
- Independent-kernel checking was not run locally; no mathematical issue is open.
- Orchestrator may register the theorem/module and run its standard independent recheck.
