STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M007/AKLT/W/H1M007/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H1M007/report.md`

## Exported declaration

- `AKLT.W.H1M007.main : AKLT.Blueprint.H1.PassageNetworkPositiveStatement`

The proof indexes the retained active sites by `Fin n`, maps the retained bonds into that indexing, and assigns every covered slot to its site. The template geometry gives at most four combined bond and slot factors at each site, so the constructed finite spin network is valid. Reindexing its assignments and factors proves that its unpinned partition is exactly `withoutPassageFunctional π m (fun _ => 1)`. The supplied finite-network positivity then gives the required strict positivity. The `π.Covered` hypothesis is not needed for this leaf proof.

## Axioms

`#print axioms AKLT.W.H1M007.main`:

```text
'AKLT.W.H1M007.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms. A source scan found no forbidden proof escapes or effects.

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; lake build AKLT.W.H1M007.Main`
- Result: success; module build reported 11 seconds (23.25 seconds total command wall time, including Lake startup).

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M007/Main.lean` with `AKLT.W.H1M007.main` at the requested type.
- Proved equality of the finite-network partition and the passage-deleted functional by explicit finite reindexing.
- Constructed a valid network using the four-factor-per-site template bound and all retained slots.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Build passed with `lake build AKLT.W.H1M007.Main`.
- No residual statements or open issues; the Covered premise is unused.
