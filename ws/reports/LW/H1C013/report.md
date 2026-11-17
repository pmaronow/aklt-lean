STATUS: PROVED

## Files

- [Codec.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Codec.lean)
- [Compiler.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Compiler.lean)
- [Digits.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Digits.lean)
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Geometry.lean)
- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Main.lean)
- [Model.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Model.lean)
- [Radix.lean](/home/ubuntu/aklt/wt/LW_H1C013/AKLT/W/H1C013/Radix.lean)

The exact requested declaration is:

```lean
theorem AKLT.W.H1C013.main : AKLT.Cert.H1.Production.Leaves.basisIndexing
```

No residual propositions or additional blueprint-leaf assumptions remain. No other proved leaf is imported. The earlier attempt's checker extraction lemmas were retained; its unproved codec residual and conditional main theorem were replaced.

## Proof

`Radix.lean` proves a general big-endian mixed-radix encoder's bounds, injectivity, surjectivity, and suffix-stride digit recovery. `Model.lean` identifies the eight ring positions with the semantic reduction groups and proves encoding injectivity. `Digits.lean` reconstructs the exchange basis from the parity bits and identifies the integer weight with twice the rational exchange weight. An exterior D factor has local basis coordinate zero and full digit three; the basis is kept unnormalized.

`Geometry.lean` relates the mixed-radix code to `sectorLabel` using just the required coordinate fields. `Compiler.lean` proves those fields directly from `inputCheck` and `geometryCheck`, by identifying incident bonds and checking the input slot/dimension formulas. Consequently no assumption of `Leaves.compilerGeometry` is needed. `Codec.lean` restricts the encoding bijection to the checked central-weight/parity fibre and preserves its literal list order. `Main.lean` transports this enumeration across the accepted matrix/list length equality.

## Exported declarations and statements

The complete inventory of the 103 explicitly named source declarations and four derived equality instances, with their statements/types, is in [declarations.md](/home/ubuntu/aklt/reports/LW/H1C013/declarations.md). There are 85 explicitly named theorems. All are audited by [Audit.lean](/home/ubuntu/aklt/reports/LW/H1C013/Audit.lean). The principal helper interfaces are `checked_coordinates`, `codec_of_geometry`, `basis_of_digits`, `weight_fullDigit`, and `basisCode_injective`.

## Axioms

The exact-type audit compiled this declaration without assumptions:

```lean
example : AKLT.Cert.H1.Production.Leaves.basisIndexing := AKLT.W.H1C013.main
```

`#print axioms` was run on all 85 named theorems and the four derived equality instances. Every axiom set is a subset of `[propext, Classical.choice, Quot.sound]`. The complete output is [axioms.log](/home/ubuntu/aklt/reports/LW/H1C013/axioms.log). In particular:

```text
'AKLT.W.H1C013.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build and validation

Commands were run from `/home/ubuntu/aklt/wt/LW_H1C013`, with `$HOME/.elan/bin` on `PATH`.

- `lake build AKLT.W.H1C013.Main` — passed, 18.79 s, maximum RSS 6,941,260 KB. The newly built compiler module took 9.9 s and Main took 3.8 s. [build.log](/home/ubuntu/aklt/reports/LW/H1C013/build.log).
- `lake env lean /home/ubuntu/aklt/reports/LW/H1C013/Audit.lean` — passed, 6.07 s; verifies the exact closed type and the axiom audit.
- `lake env leanexport AKLT.W.H1C013.Main -- $(cat /home/ubuntu/aklt/reports/LW/H1C013/names.txt)` — exported the named declarations with their dependency closure, 7.93 s.
- `con-ron --verified --jobs=2 /home/ubuntu/aklt/reports/LW/H1C013/export.ndjson` — accepted 8,752 declarations, 9.29 s, maximum RSS 217,704 KB. [con-ron.log](/home/ubuntu/aklt/reports/LW/H1C013/con-ron.log), [progress and timing](/home/ubuntu/aklt/reports/LW/H1C013/con-ron-progress.log).
- `nanoda_bin /home/ubuntu/aklt/reports/LW/H1C013/nanoda.json` — checked 9,650 declarations with no typechecker errors, 1.78 s, maximum RSS 63,976 KB. [nanoda.log](/home/ubuntu/aklt/reports/LW/H1C013/nanoda.log). NanoDa also printed one auxiliary pretty-printer message, `Unable to print axioms`; its typechecking succeeded with only the three permitted axioms enabled.

All seven delivered Lean files are transitively imported by Main. The source scan found none of the forbidden proof escapes. Existing project files were not edited. Ordinary deprecation/unused-simp linter warnings remain; they do not affect compilation or either independent kernel check.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C013/Main.lean` and six transitively imported helper modules.
- Exact theorem: `AKLT.W.H1C013.main : AKLT.Cert.H1.Production.Leaves.basisIndexing`.
- STATUS: PROVED; no unproved leaves, residual statements, or additional hypotheses.
- Compiler coordinate soundness is proved directly; no dependency on `Leaves.compilerGeometry`.
- Handles the unnormalized basis and the exterior D full digit 3 explicitly.
- Final Lake build passed in 18.79 s; exact-type/axiom audit passed in 6.07 s.
- All 85 named theorems and four equality instances use only the permitted axioms.
- con-ron verified acceptance: 8,752 declarations, 9.29 s.
- NanoDa: 9,650 declarations, no typechecker errors, 1.78 s.
- NanoDa's auxiliary `Unable to print axioms` pretty-printer message is recorded; checking passed.
- Ordinary linter warnings remain. No other limitations or deviations.
- No orchestrator decision or mathematical follow-up is needed.
