STATUS: PROVED

## Files

- Lean proof: `/home/ubuntu/aklt/wt/LW_H3C017/AKLT/W/H3C017/Main.lean`
- This report: `/home/ubuntu/aklt/reports/LW/H3C017/report.md`

## Exported declaration

```lean
theorem AKLT.W.H3C017.main : CertData.H3.Bridge.IntervalCoverageLeaf
```

The proof unfolds `intervalCheck` and `intervalEnd`. Induction over the interval list shows that a successful scan starts each nonempty segment at the preceding endpoint. This yields coverage of every `i < limit` and disjointness of distinct indexed segments, giving the required unique `Fin parts.length` witness. No certificate-wide normalization or `native_decide` is used.

## Axioms

`#print axioms AKLT.W.H3C017.main`:

```text
'AKLT.W.H3C017.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are among the permitted axioms.

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C017.Main` — succeeded; 19.8 seconds wall time, with Lake reporting 8.7 seconds for the target module.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/H3C017/Main.lean` — succeeded and printed the axiom list above.

## Open issues and deviations

The proof is complete. The requested lower-cost first attempt could not be made: this workspace exposes no model-selection tool, and the brief prohibits sub-agents. The proof was completed in the available model.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C017.main` with the exact requested type in `AKLT/W/H3C017/Main.lean`.
- Proved from the recursive `intervalEnd` checker by list induction; uniqueness follows from ordered, positive-length intervals.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Requested Lake build succeeded.
- No proof issue remains. The cheaper-model first-attempt instruction was unavailable through the exposed tools; no sub-agents were used per brief.
- Orchestrator decision: whether to record that workflow limitation or request a lower-cost rerun elsewhere.
