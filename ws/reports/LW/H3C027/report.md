STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C027/AKLT/W/H3C027/Main.lean)

## Exported declaration

- `AKLT.W.H3C027.main : CertData.H3.Bridge.FreeRowLeaf`

## Axioms

`#print axioms AKLT.W.H3C027.main`:

```text
'AKLT.W.H3C027.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C027.Main` — passed; module build reported 6.0s, command wall time 10.8s.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/H3C027/Main.lean` — passed and printed the axiom list above.

## Proof outline and open issues

The proof matches the four stored direction entries against the Compass sum. Per direction, quotient correctness identifies straight and turn edges with their arrival relationships. The exact rational ceiling calculations then match the stored diagonal and response constants, so summing the phase contributions gives the stored row term. No residual statements remain.

Model-selection deviation: this session exposed no way to switch to a cheaper model. I followed the leaf-writer instruction not to spawn sub-agents and completed the proof in the assigned model.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C027.main` with the exact requested type in `AKLT/W/H3C027/Main.lean`.
- `lake build AKLT.W.H3C027.Main` passed.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No residual claims or open proof issues.
- Limitation: alternate cheaper-model first attempt could not be routed in this session; no sub-agents were used.
