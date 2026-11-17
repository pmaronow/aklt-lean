STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C002/AKLT/W/H3C002/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3C002/report.md`

## Exported declaration

`AKLT.W.H3C002.main : CertData.H3.Bridge.CodeEncodeLeaf`

Here `CodeEncodeLeaf` is exactly the frozen proposition
`∀ (n : Nat) (w : DirectionWord n), encodeWord w < 4^n ∧ decodeWord n (encodeWord w) = w`.

The proof expands the encoder only enough to establish its head/tail recurrence, then proves the base-4 digit quotient/remainder fact. Induction gives both the range bound and the decode round trip. It does not normalize the certificate.

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C002.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms. No forbidden proof escape or `native_decide` is present.

## Build

Command:

```text
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C002.Main
```

Result: successful, `Built AKLT.W.H3C002.Main`; 18.69 seconds elapsed (12.37 seconds user, 3.90 seconds system). The direct `lake env lean AKLT/W/H3C002/Main.lean` compilation also succeeded.

## Open issues and deviation

The requested first attempt with a different cheaper model could not be performed: this session exposes no model-switch interface, and the brief forbids sub-agents. I disclosed this before proceeding and completed the proof with the assigned model. There are no proof or build issues remaining.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C002.main` with the exact requested type in `AKLT/W/H3C002/Main.lean`.
- Status: PROVED; the requested Lake build succeeded.
- `#print axioms`: `[propext, Classical.choice, Quot.sound]`.
- Open proof/build issues: none.
- Deviation: could not meet the cheaper-model-first constraint because no model switch is exposed and sub-agents are prohibited.
- Orchestrator may decide whether a separate cheaper-model review is needed for that process constraint.
