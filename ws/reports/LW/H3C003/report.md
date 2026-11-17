STATUS: PROVED

## Files

- `/home/ubuntu/aklt/wt/LW_H3C003/AKLT/W/H3C003/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H3C003/report.md`

## Exported declaration

`AKLT.W.H3C003.main : CertData.H3.Bridge.LastWindowCodeLeaf`

The proof establishes the base-four encoding recurrence for appending a direction, proves the encoding bound, then inducts over the word length. The induction reuses `AKLT.Cert.H2.lastWindow_snoc`; the remaining step is a natural-number modulo identity. It does not unfold or normalize certificate data.

Paper label: `p:automaton10`.

## Axioms

Output of `#print axioms AKLT.W.H3C003.main`:

```text
'AKLT.W.H3C003.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

Command:

```sh
export PATH="$HOME/.elan/bin:$PATH"
/usr/bin/time -p lake build AKLT.W.H3C003.Main
```

Result: successful; Lake reported `Built AKLT.W.H3C003.Main (7.1s)`. Total command timing: real 18.43s, user 11.75s, sys 3.11s.

## Open issues and deviations

No proof obligations remain. The brief's cheaper-model-first instruction could not be followed because the available workspace exposes no model-switch control; this limitation was reported before proof work began.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C003.main` with the exact requested type in `AKLT/W/H3C003/Main.lean`.
- `lake build AKLT.W.H3C003.Main` succeeded; total elapsed time 18.43s.
- Axioms are `propext`, `Classical.choice`, and `Quot.sound` only.
- No proof limitations remain.
- Deviation: the first attempt could not use a different cheaper model because no model-switch control was available.
- No orchestrator decision is needed.
