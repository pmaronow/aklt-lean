STATUS: PROVED

# H3C001 — CodeDecodeLeaf

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C001/AKLT/W/H3C001/Main.lean)
- This report: `/home/ubuntu/aklt/reports/LW/H3C001/report.md`

## Exported declaration

`AKLT.W.H3C001.main : CertData.H3.Bridge.CodeDecodeLeaf`

The proof establishes the stronger identity
`encodeWord (decodeWord n c) = c % 4^n` for every `n` and `c`, by induction on `n`; the leaf follows by reducing the modulus under its hypothesis `c < 4^n`. It expands only the word codec (`DirectionWord`, `direction`, `directionCode`, `encodeWord`, and `decodeWord`) and uses natural-number remainder/division identities. It does not normalize the certificate.

The paper location is `p:automaton10`, [app-input-contracts.tex:374](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:374). Its finite reconstruction contract describes the most-significant-first base-four code that the Lean codec implements.

## Axioms

`#print axioms AKLT.W.H3C001.main`:

```text
'AKLT.W.H3C001.main' depends on axioms: [propext, Quot.sound]
```

Both are among the allowed axioms.

## Build

Command: `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C001.Main`

Result: successful. Wall time: 22.203 s for the command; Lake reported 10 s for the target module. No tests were run; the requested module build is the verification performed.

## Open issues

None. The build output also includes existing unused-variable linter warnings from `AKLT/Gen/Packed/Routing.lean`.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C001/Main.lean` with `AKLT.W.H3C001.main` proving the exact requested type.
- The proof uses an inductive modular codec identity and the supplied range bound.
- `#print axioms`: `[propext, Quot.sound]`, both allowed.
- `lake build AKLT.W.H3C001.Main` succeeds; command wall time 22.203 s.
- No tests were run; no open proof obligations or deviations.
- Existing Packed/Routing unused-variable warnings appear in the build output.
- Orchestrator action: none required.
