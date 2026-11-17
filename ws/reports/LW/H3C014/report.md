STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C014/AKLT/W/H3C014/Main.lean)

## Exported declaration

- `AKLT.W.H3C014.main : CertData.H3.Bridge.FieldCheckSoundLeaf`

The proof extracts the checked row for each `a : Fin 3741` from `fieldBatch G 0 3741 = true`. It then applies `List.all_eq_true` to the four-element direction-code list and reflects the checked proposition with `of_decide_eq_true`. It does not evaluate or normalize the certificate data. The source proposition is the finite field check associated with paper label `p:automaton10`.

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C014.main' depends on axioms: [propext, Quot.sound]
```

Both are allowed by the leaf rules.

## Build

- Command: `lake build AKLT.W.H3C014.Main`
- Result: succeeded; 8973 jobs completed, module task reported 7.7 s (17.0 s command wall time, including Lake replay).

## Open issues and deviations

- No mathematical issue remains.
- The requested first attempt with a different cheaper model could not be performed: this session has no model-switch tool, and the brief explicitly prohibits sub-agents. The proof was completed with the assigned model.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C014.main` with the exact requested type in `AKLT/W/H3C014/Main.lean`.
- `lake build AKLT.W.H3C014.Main` succeeds.
- Axioms are `[propext, Quot.sound]` only.
- No open proof obligations remain.
- Limitation: the requested cheaper-model first attempt was unavailable; no delegation was used, per brief.
- No orchestrator decision is needed for the proof; note the model-attempt limitation if that workflow constraint is mandatory.
