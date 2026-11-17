STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C009/AKLT/W/H3C009/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3C009/report.md`

## Exported declaration

- `AKLT.W.H3C009.main : CertData.H3.Bridge.RawRowSoundLeaf`

The proof establishes that a successful raw row for a represented replayed walk gives `CorrectAt` for the decoded ten direction code. It proves local helpers for `LegalDirectionLeaf`, `RevisitLeaf`, and `SuccessorCodeLeaf`, and uses them to translate each checked row direction into the quotient admission, kind, successor, and non-revisit arrival clauses.

## Axioms

`#print axioms main`:

```text
'AKLT.W.H3C009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the permitted axioms.

## Build

- Command: `export PATH="$HOME/.elan/bin:$PATH"; time lake build AKLT.W.H3C009.Main`
- Result: success
- Wall time: 17.385 s (`Main` module build reported 12 s)

## Open issues and deviations

No proof issues remain. The requested first attempt with a different cheaper model was unavailable in this execution channel; no alternate-model or delegation control was exposed, so the proof was developed in the active model. The delivered proof contains no `native_decide` or unproved assumptions.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C009.main` with the exact requested type.
- Proved the three named bridge leaves locally and applied them in the row proof.
- `lake build AKLT.W.H3C009.Main` succeeded in 17.385 s wall time.
- `#print axioms main`: `[propext, Classical.choice, Quot.sound]`.
- Open issues: none.
- Deviation: alternate cheaper model was unavailable in this channel; proof used the active model.
