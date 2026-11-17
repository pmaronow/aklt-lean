STATUS: PROVED

## Files

- `AKLT/W/REC050/Main.lean`: complete closed proof of the requested leaf.
- `AKLT/W/REC050/Check.lean`: exact-type check and axiom audit.
- `/home/ubuntu/aklt/reports/LW/REC050/report.md`: this report.

## Exported declarations

```lean
theorem AKLT.W.REC050.main : AKLT.Blueprint.Rec.KeptInvariantStatement
```

This is exactly the requested name and type. It has no additional hypotheses or residual statements.

The public helper definition is:

```lean
def AKLT.W.REC050.MutualKept {G : Finset Plane} (D : Network G) : Prop :=
  ∀ x ∈ D.active, ∀ z ∈ D.active, Adjacent x z →
    (z ∈ D.kept x ↔ x ∈ D.kept z)
```

All helper theorems are private. The only import is `AKLT.Blueprint.Rec.NodesClosure`; no other proved blueprint leaf is used.

## Proof

The strengthened prefix invariant tracks Auxiliary validity, the nonlive U/D kept-set rules, a live U kept set equal to the full inside-G set with one neighbour erased, and the live D present-degree bound of one. It simultaneously tracks every unused trail bond as still present in the evolving network.

An interior site has all four neighbours in G. A U departure therefore erases a present outgoing flag from a three-element kept set and leaves a D site with exactly two flags. A D departure removes the site; its present-degree bound ensures that it destroys no unused trail bond. At arrival, an old nonlive U site loses one flag from its full kept set, while an old nonlive D site loses one flag from its two-element set. Initial D starts use the ResponsePair degree hypothesis.

Separate structural inductions prove mutual kept flags through normalization and tracing, and that a previously departed site never becomes U again. The final theorem combines these with the strengthened invariant.

The supplied Main.lean already contained the completed induction when inspected, although report.luna.md described an earlier partial version. This run retained that proof, updated deprecated simplifier lemma names, rebuilt the module, and independently checked the exact closed type and axioms. No frozen statement or file outside REC050 was modified.

## Axiom audit

`lake env lean AKLT/W/REC050/Check.lean` printed:

```text
AKLT.W.REC050.main : AKLT.Blueprint.Rec.KeptInvariantStatement
'AKLT.W.REC050.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are precisely the allowed axioms. No forbidden proof constructs occur in the delivered Lean files.

## Validation

Commands ran with `$HOME/.elan/bin` added to PATH:

- `lake build AKLT.W.REC050.Main`: succeeded without warnings; module compilation 3.9 s, total wall time 10.33 s.
- `lake env lean AKLT/W/REC050/Check.lean`: succeeded; wall time 3.86 s. Its `example` assigns `main` directly to the frozen statement, checking that no residual hypotheses remain.

## Open issues

None for REC050. The former Residual_1, Residual_2, and Residual_3 obligations are discharged and no longer occur in the source.

## ORCH-SUMMARY

- Delivered `AKLT/W/REC050/Main.lean` and `AKLT/W/REC050/Check.lean`.
- Exact theorem: `AKLT.W.REC050.main : AKLT.Blueprint.Rec.KeptInvariantStatement`.
- Status: PROVED; no dependencies on other blueprint leaf proofs.
- Strengthened invariant and unused-bond induction close all former residuals.
- Reused the completed proof already present in the supplied source; the older report was stale.
- Main module rebuilt successfully without warnings; exact-type audit passed.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Open declarations: none. Limitations or deviations: none.
- No orchestrator decision is required; the leaf is ready for validation and indexing.
