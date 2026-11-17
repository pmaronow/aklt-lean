STATUS: PROVED

## Files

- `AKLT/W/H1M022/Main.lean`

## Exported declaration

- `AKLT.W.H1M022.main : AKLT.Blueprint.H1.TraceProductPositiveStatement`

The proof factors `A` as `RᴴR` using the C⋆ algebra characterization of nonnegative matrices. It applies PSD preservation under `R B Rᴴ`, cycles the trace, and uses PSD trace nonnegativity. This proves the statement for arbitrary finite index types as required.

## Axioms

`#print axioms AKLT.W.H1M022.main`:

```text
'AKLT.W.H1M022.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.H1M022.Main` — succeeded; module build reported 3.8 s, total command 10.1 s.
- `lake env lean /tmp/H1M022Axioms.lean` — succeeded; 4.1 s. The temporary file imports the leaf and prints the theorem and its axioms.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M022/Main.lean` with `AKLT.W.H1M022.main` at the requested type.
- The target compiles with `lake build AKLT.W.H1M022.Main`.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- No limitations or deviations; no open issues.
