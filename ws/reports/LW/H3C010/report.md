STATUS: PROVED FROM DEPS

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C010/AKLT/W/H3C010/Main.lean) — complete proof; all helper theorems are private.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_H3C010/AKLT/W/H3C010/Audit.lean) — independent import, exact-type check, and axiom audit.
- [build.log](/home/ubuntu/aklt/reports/LW/H3C010/build.log), [audit.log](/home/ubuntu/aklt/reports/LW/H3C010/audit.log) — final successful validation logs.

## Exported declaration

```lean
theorem AKLT.W.H3C010.main : CertData.H3.Bridge.RawTrieCoverageLeaf
```

This has exactly the requested closed type: for every graph represented by its packed class spans, a successful `rawBatch G 0 4096` implies that each code below `4^10` has class below `3741` if and only if its decoded word is a `RawWindow`. There are no additional hypotheses or residual declarations.

## Dependencies and proof

The proof imports these completed leaves from the supplied proved index:

- `AKLT.W.H3C001.main : CertData.H3.Bridge.CodeDecodeLeaf`.
- `AKLT.W.H3C005.main : CertData.H3.Bridge.RawReplaySoundLeaf`.
- `AKLT.W.H3C006.main : CertData.H3.Bridge.RawReplayCompleteLeaf`.

The earlier attempt's packed-span, fold, and depth-four DFS arguments are reused. A new general replay-splitting lemma joins the six-step prefix and four-step suffix. Failed prefixes force all 256 classes to the sentinel; successful prefixes use replay soundness and code decoding to identify the stem code, then apply the DFS classification. Replay soundness and completeness identify successful full replay with `RawWindow`. Finally, division and remainder by 256 place every memory-ten code in its checked stem.

The former `Residual_1` is fully discharged and removed. The proof uses the generic packed-lane lemmas `repeatLane_eq` and `lane_packFn`; it does not normalize the certificate or use native computation.

## Axioms

Both the module and independent audit print:

```text
'AKLT.W.H3C010.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are exactly within the allowed set. The delivered sources contain no forbidden proof escape.

## Validation

- `lake build AKLT.W.H3C010.Main` — passed; 10.98 seconds wall time, with the target module reported at 5.9 seconds.
- `lake env lean AKLT/W/H3C010/Audit.lean` — passed; 4.78 seconds wall time. It confirms `AKLT.W.H3C010.main : CertData.H3.Bridge.RawTrieCoverageLeaf` and the axiom list above.
- Source scan for forbidden constructs — no matches.

Only files in the assigned task directory and report directory were written, apart from normal Lake build artifacts. Existing statement and library sources were unchanged.

## Open issues and deviation

No mathematical obligations remain. The requested cheaper-model first retry was not performed: the available controls cannot switch the active model, and the brief prohibits sub-agents. The earlier Luna attempt was reused and completed with the active model.

## ORCH-SUMMARY

- Delivered the exact unconditional theorem `AKLT.W.H3C010.main`.
- Statement: `CertData.H3.Bridge.RawTrieCoverageLeaf`.
- Status: PROVED FROM DEPS.
- Reuses indexed leaves H3C001, H3C005, and H3C006.
- Reuses and completes the earlier attempt's private trie lemmas.
- Removed the solved residual interface; no open leaves or residuals remain.
- Final requested build and independent exact-type audit both pass.
- Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No certificate normalization, native computation, or forbidden constructs.
- Deviation: no cheaper-model retry; active-model switching unavailable, sub-agents prohibited.
- Orchestrator can register the theorem and module in the proved index.
