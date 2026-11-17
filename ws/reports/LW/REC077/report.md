STATUS: PROVED FROM DEPS

## Files

- `/home/ubuntu/aklt/wt/LW_REC077/AKLT/W/REC077/Main.lean` — complete proof.
- `/home/ubuntu/aklt/wt/LW_REC077/AKLT/W/REC077/Check.lean` — independent import, exact-type check, and axiom audit.
- `/home/ubuntu/aklt/reports/LW/REC077/report.md` — this report.

The obsolete helper modules from the earlier attempt were removed from the assigned task directory. Its report remains preserved as `report.luna.md`. No source files outside `AKLT/W/REC077/` were changed.

## Exported declaration

```lean
theorem AKLT.W.REC077.main : AKLT.Blueprint.Rec.TraceExposureStatement
```

This theorem has exactly the requested closed type, with no residual assumptions. `Check.lean` also verifies it through an `example` with that exact type.

## Proof and approved dependencies

All five blueprint dependencies below appear in `/home/ubuntu/aklt/state/lw/proved-index.tsv`.

| Blueprint statement in `AKLT.Blueprint.Rec` | Theorem | Imported module |
| --- | --- | --- |
| `StepRatioPositiveStatement` | `AKLT.W.REC010.main` | `AKLT.W.REC010.Main` |
| `FreeRatioUpperStatement` | `AKLT.W.REC011.main` | `AKLT.W.REC011.Main` |
| `TraceDynamicsStatement` | `AKLT.W.REC039.main` | `AKLT.W.REC039.Main` |
| `TraceTelescopeStatement` | `AKLT.W.REC041.main` | `AKLT.W.REC041.Main` |
| `ProductExposureStatement` | `AKLT.W.REC046.main` | `AKLT.W.REC046.Main` |

Trace dynamics supplies an auxiliary prefix and an admissible departure at every index. The proved helper `AKLT.W.REC039.adjacent_mem_neighbours` converts the present-bond premise into membership in `presentNeighbours`, completing each `Departure` record. The ratio lemmas give positivity for both pin choices and the free upper bound of one. Together with the supplied bounds on `x`, these discharge every hypothesis of product exposure. Apply that inequality to the sequences composed with the arbitrary permutation, reindex both full products using `Equiv.prod_comp`, and identify them with the two trace ratios by the telescope lemma. This also handles zero length.

The frozen statement concerns only ordered trace exposure; the broader pair-envelope and boundary arguments mentioned in the suggested route are not required for its conclusion.

## Axiom audit

Command:

```sh
lake env lean AKLT/W/REC077/Check.lean
```

Output:

```text
AKLT.W.REC077.main : AKLT.Blueprint.Rec.TraceExposureStatement
'AKLT.W.REC077.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are precisely the permitted standard axioms. The delivered Lean sources contain no forbidden proof escapes or unproved facts.

## Validation

Commands were run with `$HOME/.elan/bin` on `PATH`.

- `/usr/bin/time -p lake build AKLT.W.REC077.Main` — exit 0; 9.88 seconds wall time; final module compilation 3.2 seconds. Existing dependency modules emit linter warnings; `REC077.Main` compiles without warnings.
- `/usr/bin/time -p lake env lean AKLT/W/REC077/Check.lean` — exit 0; 4.22 seconds wall time; exact type and axiom output shown above.
- Source scan of the delivered task directory found no forbidden constructs.

## Open issues

None. No remaining blueprint leaves or residual statements are required.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC077/Main.lean` with `AKLT.W.REC077.main`.
- Exact type: `AKLT.Blueprint.Rec.TraceExposureStatement`.
- Status: PROVED FROM DEPS.
- Indexed dependencies: REC010, REC011, REC039, REC041, REC046.
- Supporting geometry helper: `AKLT.W.REC039.adjacent_mem_neighbours`.
- Arbitrary permutations and the zero-length case are covered.
- Build and independent exact-type check pass.
- Axioms: propext, Classical.choice, Quot.sound only.
- Removed obsolete inherited helper modules; preserved `report.luna.md`.
- No statement-layer edits, residual assumptions, or sub-agents.
- Open names: none. Limitations: none.
- Orchestrator can register the exact theorem and module in the proved-leaf index.
