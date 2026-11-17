STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3M015/AKLT/W/H3M015/Main.lean)

## Exported declaration

`AKLT.W.H3M015.main : AKLT.Blueprint.H3.RewardForgettingStatement`

## Axioms

`#print axioms AKLT.W.H3M015.main`:

```text
'AKLT.W.H3M015.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3M015.Main`
- Result: successful; Lake reported the module build in 7.2 s.
- Inspection command: `printf 'import AKLT.W.H3M015.Main\n#check AKLT.W.H3M015.main\n#print axioms AKLT.W.H3M015.main\n' | lake env lean --stdin`

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3M015.main` with the exact requested statement.
- The proof compares pair sums over nested live sets, proves `betaPrimeBound ≤ betaBound`, and uses nonnegativity for newly added pairs.
- Build succeeded with `lake build AKLT.W.H3M015.Main`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- Open declarations: none.
- Limitations or deviations: none.
- Orchestrator decision or follow-up: none.
