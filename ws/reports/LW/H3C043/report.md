STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C043/AKLT/W/H3C043/Main.lean)

## Exported declaration

`AKLT.W.H3C043.main : CertData.H3.Bridge.SemanticBatchSplitLeaf`

## Proof outline

The proof reduces `intervalCheck` to its `intervalEnd` result, then proves by
induction over the interval list that its chunk sums equal the sum over the
covered range. A generic `List.range` sum-splitting lemma handles each step.
The proof leaves `semanticStem` opaque and never normalizes the full
certificate.

`CertData.H3.Bridge.IntervalCoverageLeaf` is a proposition definition with no
available proof in the imported modules. In keeping with the leaf-writer rule
that other leaves cannot be assumed, this proof works directly from
`intervalEnd` and establishes the stronger sum-splitting fact it needs.

## Axioms

Output of `#print axioms AKLT.W.H3C043.main`:

```text
'AKLT.W.H3C043.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- Command: `lake build AKLT.W.H3C043.Main`
- Result: successful (`Built AKLT.W.H3C043.Main`)
- Timing: 17.9 s wall time for the build command; Lean reported 7.6 s for the
  target module.

## Open issues and deviations

- No proof issues remain.
- The session exposed no model-switch mechanism. No agent was used, honoring the
  instruction not to use sub-agents; therefore the requested cheaper-model first
  attempt could not be performed.
- The suggested reuse of `IntervalCoverageLeaf` was replaced by direct use of
  the underlying `intervalEnd` checker, since that leaf is not proved in the
  imported context.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C043/Main.lean` with the exact requested theorem and type.
- Proof compiles with `lake build AKLT.W.H3C043.Main`.
- The theorem uses only standard axioms: propext, Classical.choice, Quot.sound.
- Semantic certificate computation remains opaque.
- Open proof issues: none.
- Deviation: no mid-turn model switch was available, and no sub-agent was used.
- Deviation: directly proved interval sum splitting from `intervalEnd`; no proved `IntervalCoverageLeaf` was importable.
- No further orchestrator action is needed for the proof.
