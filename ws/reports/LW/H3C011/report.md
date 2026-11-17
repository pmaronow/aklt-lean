STATUS: PROVED FROM DEPS

# H3C011 — `p:automaton10`

The exact requested declaration is proved without residual hypotheses:

```lean
theorem AKLT.W.H3C011.main : CertData.H3.Bridge.RawTrieProjectionLeaf
```

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C011/AKLT/W/H3C011/Main.lean:64): the requested theorem and representative/row helpers.
- [Traversal.lean](/home/ubuntu/aklt/wt/LW_H3C011/AKLT/W/H3C011/Traversal.lean): the supplied symbolic traversal proof, retained unchanged.
- [report.md](/home/ubuntu/aklt/reports/LW/H3C011/report.md): this report.

Only the assigned task and report directories were written. The earlier reports are preserved. The old `Residual_RawRowSound`, `Residual_RawTrieCoverage`, `Residual_RawReplaySound`, and conditional `main_from_residuals` declarations have been removed from the delivery; the proved dependencies now close the theorem directly.

## Proved dependencies and proof route

Each directly imported blueprint proof appears in `/home/ubuntu/aklt/state/lw/proved-index.tsv`:

| Statement | Theorem | Module |
| --- | --- | --- |
| `CertData.H3.Bridge.RawRowSoundLeaf` | `AKLT.W.H3C009.main` | `AKLT.W.H3C009.Main` |
| `CertData.H3.Bridge.RawTrieCoverageLeaf` | `AKLT.W.H3C010.main` | `AKLT.W.H3C010.Main` |
| `CertData.H3.Bridge.RawReplaySoundLeaf` | `AKLT.W.H3C005.main` | `AKLT.W.H3C005.Main` |
| `CertData.H3.Bridge.CodeEncodeLeaf` | `AKLT.W.H3C002.main` | `AKLT.W.H3C002.Main` |
| `CertData.H3.Bridge.RepresentativeBoundsLeaf` | `AKLT.W.H3C013.main` | `AKLT.W.H3C013.Main` |

For a raw window, encoding and coverage give an in-range class. The retained `rawBatch_row` proof extracts its successful replay and checked row from the batch. Replay soundness supplies `WalkRepresents`, and row soundness supplies `CorrectAt`. Representative checks give raw representatives that project to their own indices. The existing `AKLT.Cert.H3.quotient_assembly` combines these facts into `G.quotient.Correct`.

The traversal proof uses the existing packed-lane lemmas `repeatLane_eq` and `lane_packFn` to exclude rejected branches. It reasons symbolically about list folds and replay; it does not normalize the certificate.

## Exported declarations and statements

All declarations below are in namespace `AKLT.W.H3C011`, with the source files' open namespaces (`AKLT.Defs`, `AKLT.Cert.H3`, `AKLT.Cert.H3.Production`, and `CertData.H3.Bridge`).

```lean
theorem main : CertData.H3.Bridge.RawTrieProjectionLeaf
```

The closed proposition is exactly:

```lean
∀ G : Graph, SpanRepresents G →
  (rawBatch G 0 4096).ok = true →
  representativeBatch G 0 3741 = true → G.quotient.Correct
```

The six exported helper theorems are:

```lean
theorem replayRaw_append (a b c : Nat) (w : Walk) :
  replayRaw (a + b) c w =
    (replayRaw a (c / 4 ^ b) w).bind (replayRaw b c)

theorem replayRaw_initial_code (n c : Nat)
    (hc : c < 4 ^ n) (hmax : c < 1048576) (s : Walk)
    (h : replayRaw n c rawInitial = some s) :
  s.code = c

theorem rawDFS_row (G : Graph) (hspan : SpanRepresents G)
    (n : Nat) (hn : n ≤ 4) (w : Walk)
    (hroom : (w.code + 1) * 4 ^ n ≤ 1048576) (c : Nat)
    (hclass : G.classAt (w.code * 4 ^ n + c % 4 ^ n) < 3741)
    (hcheck : (rawDFS G n w).ok = true) :
  ∃ s : Walk, replayRaw n c w = some s ∧ rawRow G s = true

theorem rawBatch_row (G : Graph) (hspan : SpanRepresents G)
    (hbatch : (rawBatch G 0 4096).ok = true)
    (c : Nat) (hc : c < 1048576) (hclass : G.classAt c < 3741) :
  ∃ s : Walk, replayRaw 10 c rawInitial = some s ∧ rawRow G s = true

theorem representatives_of_replaySound (hsound : RawReplaySoundLeaf)
    (G : Graph) (hbatch : representativeBatch G 0 3741 = true) :
  ∀ a : Fin 3741, RawWindow (G.quotient.representative a) ∧
    G.quotient.project (G.quotient.representative a) = a

theorem rows_of_leaves (hrow : RawRowSoundLeaf)
    (hcoverage : RawTrieCoverageLeaf) (hsound : RawReplaySoundLeaf)
    (G : Graph) (hspan : SpanRepresents G)
    (hbatch : (rawBatch G 0 4096).ok = true) :
  ∀ w : DirectionWord 10, RawWindow w → CorrectAt G.quotient w
```

## Axiom audit

Both Lean files contain `#print axioms` for every exported theorem. The successful build produced:

```text
'AKLT.W.H3C011.replayRaw_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.replayRaw_initial_code' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.rawDFS_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.rawBatch_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.representatives_of_replaySound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.rows_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All are permitted axioms. A source scan of the two delivered Lean files found no forbidden proof constructs.

## Build and open issues

```sh
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.H3C011.Main
```

Result: successful, exit code 0. Wall time: **21.36 seconds**; user time: **46.03 seconds**; system time: **8.37 seconds**. The target module took 3.8 seconds; Lake also compiled the required proved-leaf dependencies. The delivered modules had no warnings or errors. Existing packed-library warnings were replayed from the build cache.

No open proof obligations or residual statements remain. No sub-agents were used. The supplied earlier cheaper-model attempt was reused through the subsequent traversal and assembly proof. No whole-certificate computation or forbidden computation mechanism was used.

## ORCH-SUMMARY

- STATUS: PROVED FROM DEPS.
- Exact theorem: `AKLT.W.H3C011.main : CertData.H3.Bridge.RawTrieProjectionLeaf`.
- Files: `AKLT/W/H3C011/Main.lean` and `AKLT/W/H3C011/Traversal.lean`.
- Direct proved leaves: H3C002, H3C005, H3C009, H3C010, H3C013.
- All directly used leaves occur in the supplied proved-leaf index.
- Reuses symbolic traversal, packed-lane lemmas, and `quotient_assembly`.
- Removed the obsolete residual definitions and conditional assembly theorem.
- Open obligations: none.
- All seven exported theorems use only propext, Classical.choice, Quot.sound.
- Build passed: `lake build AKLT.W.H3C011.Main`, 21.36 seconds wall time.
- No whole-certificate normalization, forbidden constructs, or sub-agents.
- No limitations or deviations in the delivered theorem.
- The orchestrator can register H3C011 as proved from the listed dependencies.
