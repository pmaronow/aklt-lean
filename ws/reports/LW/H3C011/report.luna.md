STATUS: PARTIAL

# H3C011 — `p:automaton10`

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C011/AKLT/W/H3C011/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3C011/report.md`

No existing project files were changed.

## Delivered declaration

`AKLT.W.H3C011.main_from_residuals`

```lean
theorem main_from_residuals
    (hRepresentatives : Residual_Representatives)
    (hRows : Residual_RawRows) :
    CertData.H3.Bridge.RawTrieProjectionLeaf
```

The proof uses the retained `AKLT.Cert.H3.quotient_assembly` theorem. The two residual propositions are closed and are stated in `Main.lean`:

- `AKLT.W.H3C011.Residual_Representatives`: passing the representative batch yields raw representatives that project to their indices.
- `AKLT.W.H3C011.Residual_RawRows`: passing the raw batch yields `CorrectAt` for every raw window.

The requested exact declaration `AKLT.W.H3C011.main : CertData.H3.Bridge.RawTrieProjectionLeaf` is not proved in this partial delivery. The open work is to prove those two residuals from the checker definitions and the available raw replay/row reasoning. In particular, the generic traversal-to-row-soundness bridge remains unresolved. `SpanRepresents` and `RawTrieCoverageLeaf` are preserved in the target interface but are not needed by the conditional assembly theorem.

## Axioms

`#print axioms AKLT.W.H3C011.main_from_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted Lean/Mathlib axioms. No forbidden proof escape hatches occur in the delivered file.

## Build

Command:

```sh
lake build AKLT.W.H3C011.Main
```

Result: successful. The first build took about 25 seconds while building the missing `CertData.H3.Kernel.Soundness` dependency; the subsequent build took about 20 seconds. A direct `lake env lean AKLT/W/H3C011/Main.lean` check took about 10 seconds and printed the axiom list above.

## Limitations and open issues

The task requires the first attempt to use a different cheaper model. This session provides no model-switch tool, and the brief prohibits sub-agents, so that instruction could not be carried out. No full proof attempt on a different model was made.

## ORCH-SUMMARY

- Delivered a compiled conditional assembly in `AKLT/W/H3C011/Main.lean`.
- Exact requested theorem `AKLT.W.H3C011.main` remains open.
- Residuals: `AKLT.W.H3C011.Residual_Representatives`, `AKLT.W.H3C011.Residual_RawRows`.
- `AKLT.W.H3C011.main_from_residuals` assembles them using `AKLT.Cert.H3.quotient_assembly`.
- Build passed: `lake build AKLT.W.H3C011.Main`.
- Axioms are `[propext, Classical.choice, Quot.sound]`.
- No existing source files changed; no forbidden constructs used.
- Cheaper-model first attempt was unavailable in this session; sub-agents were prohibited.
- Orchestrator must prove both residuals or pass them as explicit remaining work.
