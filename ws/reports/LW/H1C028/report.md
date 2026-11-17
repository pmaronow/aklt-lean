STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C028/AKLT/W/H1C028/Main.lean): complete proof; the only file in the task's Lean directory.
- [report.md](/home/ubuntu/aklt/reports/LW/H1C028/report.md): this report.
- The earlier report remains in `report.luna.md`.

## Exported declaration

```lean
theorem AKLT.W.H1C028.main :
  AKLT.Cert.H1.Production.Leaves.representativeCode
```

Its statement unfolds to:

```lean
∀ a : AKLT.Cert.H1.Production.Input,
  AKLT.Cert.H1.Production.inputCheck a = true →
  AKLT.Cert.H1.effectivePatternCode (AKLT.Cert.H1.Production.inputPattern a) =
    AKLT.Cert.H1.Production.rawKey a.axes a.corners a.outgoing
```

All four supporting theorems in this file are private. There are no residual assumptions.

## Proof and reused dependencies

The proof establishes equality of the sixteen semantic and raw bond bits by list extensionality. It then identifies each compiled status digit with its valid raw status and uses the degree-zero criterion to delete precisely the isolated statuses. The plain and reflected encodings agree separately, including the outgoing east/west swap; applying `congrArg₂ min` proves equality of the canonical codes.

The following helper lemmas come from packages of leaves listed in `/home/ubuntu/aklt/state/lw/proved-index.tsv`:

- H1C009, `AKLT.Cert.H1.Production.Leaves.compilerGeometry`: imports `AKLT.W.H1C009.Edges`; uses `raw_edge`, `statusAt_ring`, and `ring_status_range` from namespace `AKLT.W.H1C009`.
- H1C025, `AKLT.Cert.H1.Production.Leaves.rawEncoding`: imports `AKLT.W.H1C025.Encoding`; uses `ring_degree_zero`, `reflected_status`, and `reflected_edges` from namespace `AKLT.W.H1C025`, with its transparent `semanticEdges`, `semanticStatus`, and `edgeLive` definitions.

These are proved helper lemmas, with no additional blueprint premises. No existing files outside the assigned directory were edited.

## Axioms and validation

`#print axioms AKLT.W.H1C028.main` reports:

```text
'AKLT.W.H1C028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `lake build AKLT.W.H1C028.Main`: succeeded, 11.25 seconds wall time; Main compilation reported 5.0 seconds.
- `lake env lean --stdin`: succeeded, 6.36 seconds, importing Main and checking both `#check (AKLT.W.H1C028.main : AKLT.Cert.H1.Production.Leaves.representativeCode)` and an `example` with that exact type. The axiom output was confirmed in this separate import check.
- Forbidden-declaration scan: no matches. The delivered file contains no proof placeholders or unproved residuals.

Open proof issues: none. Independent kernel checks were not invoked locally.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C028/Main.lean` with the exact requested theorem name and type.
- Status: PROVED FROM DEPS, reusing proved helpers from indexed H1C009 and H1C025.
- Both reflected encodings agree; isolated statuses are deleted before encoding.
- Outgoing reflection preserves north and swaps east/west.
- Build and separate exact-type import check succeeded.
- Axioms: propext, Classical.choice, Quot.sound only.
- Open residuals: none; the earlier attempt's four residuals are replaced by a complete proof.
- Limitations: independent kernels not run locally; no statement changes or other deviations.
- Orchestrator: run the campaign's independent checks and register H1C028.
