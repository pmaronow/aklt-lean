STATUS: PARTIAL

Files:

- `AKLT/W/H3C035/Main.lean`: compiled reduction of the full early-soundness leaf to exactly two named blueprint leaves. All enumeration helpers are private.
- `/home/ubuntu/aklt/reports/LW/H3C035/report.md`: this report.
- `/home/ubuntu/aklt/reports/LW/H3C035/build.log`: final successful build output and timing.
- The supplied earlier report remains in `report.luna.md`.

Exported declarations (namespace `AKLT.W.H3C035`):

```lean
def ResidualPrefixStep : Prop := CertData.H3.Bridge.PrefixStepLeaf

def ResidualShortValue : Prop := CertData.H3.Bridge.ShortValueLeaf

theorem main_of_residuals
    (hstep : ResidualPrefixStep) (hshort : ResidualShortValue) :
    CertData.H3.Bridge.EarlySoundLeaf
```

The reduction covers every depth through 12. It reuses `AKLT.Cert.H2.Words` for snoc words, trail restriction, fresh bonds, and finite-word enumeration. It proves that `goodStep` enumerates exactly the first-direction trail extensions avoiding the centre and earlier target hits. The per-layer DFS identity splits into target-hit values and the next frontier; telescoping and removing length zero yield `firstDirectionPartialRow`. `PrefixStepLeaf` supplies the represented integer prefix state, and `ShortValueLeaf` supplies the exact rational value at a target hit. There is no remaining enumeration or fixed-depth residual.

Axiom audit:

```text
#print axioms AKLT.W.H3C035.main_of_residuals
'AKLT.W.H3C035.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build:

```text
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.H3C035.Main
Build completed successfully (8974 jobs).
Main module: 4.9 seconds
real 9.52
user 12.54
sys 2.56
```

Only the new task module was compiled; other jobs were prebuilt dependencies. The final source scan found no forbidden proof escape. No whole-certificate normalization, native evaluation, or subagents were used. The supplied earlier Luna attempt was the starting point; no additional model-switch run was performed in this continuation.

Open issues:

- `CertData.H3.Bridge.PrefixStepLeaf` is absent from `/home/ubuntu/aklt/state/lw/proved-index.tsv`; its exact closed statement is retained as `ResidualPrefixStep`.
- `CertData.H3.Bridge.ShortValueLeaf` is absent from that index; its exact closed statement is retained as `ResidualShortValue`.
- Consequently the unconditional requested declaration `AKLT.W.H3C035.main : CertData.H3.Bridge.EarlySoundLeaf` is not proved or declared. No theorem with a different type is presented under that name.

## ORCH-SUMMARY

- Delivered compiled `AKLT/W/H3C035/Main.lean` and the report/build log.
- Proved `main_of_residuals : ResidualPrefixStep → ResidualShortValue → CertData.H3.Bridge.EarlySoundLeaf`.
- `ResidualPrefixStep` is exactly `CertData.H3.Bridge.PrefixStepLeaf`.
- `ResidualShortValue` is exactly `CertData.H3.Bridge.ShortValueLeaf`.
- No other residual remains; the DFS/true-word enumeration and all depths through 12 are handled.
- Open: exactly those two blueprint leaves and the resulting unconditional `AKLT.W.H3C035.main`.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Build succeeded in 9.52 seconds wall time.
- Reused H2 word lemmas; no certificate normalization or native evaluation.
- No subagents or additional model-switch run; supplied Luna attempt preserved as `report.luna.md`.
- Orchestrator should route the two named leaves, then instantiate this reduction to obtain the required `main`.
