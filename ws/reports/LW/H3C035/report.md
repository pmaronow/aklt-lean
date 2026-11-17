STATUS: PROVED FROM DEPS

## Files

- `AKLT/W/H3C035/Main.lean` — the only Lean source in the task directory.
- `/home/ubuntu/aklt/reports/LW/H3C035/report.md` — this report.

## Exported declaration

```lean
theorem AKLT.W.H3C035.main : CertData.H3.Bridge.EarlySoundLeaf
```

This is unconditional and has exactly the requested name and type. All helper declarations in the file are private.

## Proof and reused dependencies

Reused the existing structural DFS proof and discharged its two former residual assumptions using the proved-index entries:

- `AKLT.W.H3C031.main : CertData.H3.Bridge.PrefixStepLeaf`, imported from `AKLT.W.H3C031.Main`.
- `AKLT.W.H3C033.main : CertData.H3.Bridge.ShortValueLeaf`, imported from `AKLT.W.H3C033.Main`.

The proof identifies legal recursive children with one-direction extensions of true trails, relates target hits to `ClosedTrail` with the specified first direction, and sums the resulting contributions by depth. `AKLT.Cert.H2.sum_snoc` supplies the generic word-enumeration identity. The prefix-step invariant transports the semantic state along each word, and the short-value lemma identifies each terminal value with `closedContribution`. Induction on the DFS fuel then gives the finite first-direction row through any cutoff at most twelve, including depth zero and hits exactly at the cutoff.

The former `ResidualPrefixStep` and `ResidualShortValue` definitions were removed. No residual statements remain. No concrete certificate or positive-depth word enumeration was normalized, and no `native_decide` was used.

## Axiom check

The delivered source executes `#print axioms AKLT.W.H3C035.main` during compilation. Output:

```text
'AKLT.W.H3C035.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof escape is present.

## Build

Executed from `/home/ubuntu/aklt/wt/LW_H3C035`:

```bash
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.H3C035.Main
```

Result: exit code 0; `Build completed successfully (8977 jobs).`

Timing: 40.75 seconds wall, 59.56 seconds user, 7.79 seconds system. The target module took 6.6 seconds; Lake also compiled the newly imported dependency modules from their existing sources. Warnings were confined to those dependency sources; the target module produced no warnings.

## Open issues and limitations

No mathematical obligations remain. Existing files outside the assigned task directory were not edited. Independent kernels were not run in this session; their later campaign checks remain external validation.

The requested first attempt on a different cheaper model could not be performed: no model-switch capability is available, and the brief explicitly forbids sub-agents. The existing proof was reused directly, with no sub-agent or delegation.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C035/Main.lean` with the exact unconditional theorem `AKLT.W.H3C035.main`.
- Statement: `CertData.H3.Bridge.EarlySoundLeaf`.
- Status: PROVED FROM DEPS.
- Reused proved leaves: `AKLT.W.H3C031.main` and `AKLT.W.H3C033.main`.
- All previous residuals discharged; open names: none.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Requested build succeeded in 40.75 seconds wall time; target module: 6.6 seconds.
- No whole-certificate normalization or forbidden proof mechanism.
- Only task-directory Lean source and the requested report were edited.
- Limitation: no alternate-model switch was available; no sub-agent was used.
- Independent-kernel checks were not run here.
- Orchestrator may register the delivered theorem after its normal independent checks.
