STATUS: PARTIAL

# H3C011 — `p:automaton10`

The projection leaf is reduced to exactly its three suggested blueprint prerequisites:

1. `CertData.H3.Bridge.RawRowSoundLeaf`
2. `CertData.H3.Bridge.RawTrieCoverageLeaf`
3. `CertData.H3.Bridge.RawReplaySoundLeaf`

None of these occurs in `/home/ubuntu/aklt/state/lw/proved-index.tsv`. They remain explicit hypotheses of the delivered reduction, through transparent closed residual definitions. The requested unconditional theorem `AKLT.W.H3C011.main : CertData.H3.Bridge.RawTrieProjectionLeaf` is **not proved or declared**. Do not register this leaf as proved.

The earlier attempt's broad representative and raw-row residuals have been replaced. All traversal, packed-span, code-splitting, representative-check, and quotient-assembly steps needed to use the three prerequisites are now proved.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C011/AKLT/W/H3C011/Main.lean): closed residual definitions and semantic assembly.
- [Traversal.lean](/home/ubuntu/aklt/wt/LW_H3C011/AKLT/W/H3C011/Traversal.lean): symbolic traversal and code arithmetic.
- [report.md](/home/ubuntu/aklt/reports/LW/H3C011/report.md): this report.

Only files in the assigned task and report directories were written. The supplied earlier report remains in `report.luna.md`. No sub-agents were used.

## Exported declarations and statements

All declarations below are in namespace `AKLT.W.H3C011`. The displayed statements use the same open namespaces as the source files.

```lean
def Residual_RawRowSound : Prop :=
  CertData.H3.Bridge.RawRowSoundLeaf

def Residual_RawTrieCoverage : Prop :=
  CertData.H3.Bridge.RawTrieCoverageLeaf

def Residual_RawReplaySound : Prop :=
  CertData.H3.Bridge.RawReplaySoundLeaf

theorem main_from_residuals
    (hrow : Residual_RawRowSound)
    (hcoverage : Residual_RawTrieCoverage)
    (hsound : Residual_RawReplaySound) :
    CertData.H3.Bridge.RawTrieProjectionLeaf
```

The other exported theorems are:

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

## Proof route and reuse

`rawDFS_row` inducts on the remaining depth, extracting each child check from the `RawStats.add` fold. A rejected child checks a packed span equal to the constant invalid class 3741. `SpanRepresents`, `AKLT.Gen.Packed.repeatLane_eq`, and `AKLT.Gen.Packed.lane_packFn` therefore force every code in that span to have class 3741, contradicting the supplied strict class bound. An accepted child continues the replay and eventually reaches a checked row.

`rawBatch_row` extracts the selected six-digit stem, then uses `replayRaw_append` to join it with the four-digit subtree. The code invariant is proved directly from `replayRaw` and `Walk.step`; no decoding prerequisite is added.

For each raw word, `RawTrieCoverageLeaf` supplies its strict class bound, `rawBatch_row` supplies a successful replay and checked row, and `RawReplaySoundLeaf` plus `RawRowSoundLeaf` give `CorrectAt`. Successful representative checks similarly give raw representatives and self-projection. The retained `AKLT.Cert.H3.quotient_assembly` finishes the conditional proof.

The two imported proved leaves are listed in the supplied index:

- `AKLT.W.H3C002.main : CertData.H3.Bridge.CodeEncodeLeaf`
- `AKLT.W.H3C013.main : CertData.H3.Bridge.RepresentativeBoundsLeaf`

No whole-certificate computation, `native_decide`, or new unproved assumption is used. The three residual definitions expose the complete outstanding dependency set.

## Axiom audit

The build executes `#print axioms` for every exported theorem. Its output is:

```text
'AKLT.W.H3C011.replayRaw_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.replayRaw_initial_code' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.rawDFS_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.rawBatch_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.representatives_of_replaySound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.rows_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C011.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A source scan found no forbidden proof constructs in the delivered Lean files.

## Build

```sh
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.H3C011.Main
```

Result: **successful**, exit code 0. Wall time: **13.81 seconds**; user time: 22.24 seconds; system time: 6.19 seconds. Lake reported 4.8 seconds for `Traversal` and 3.8 seconds for `Main`, and also built the two imported proved-leaf modules. There were no warnings or errors in the delivered modules.

## Remaining work

- `Residual_RawRowSound` is exactly `CertData.H3.Bridge.RawRowSoundLeaf`: the semantic correspondence between one successful production `rawRow` check and `CorrectAt` remains a separate unproved leaf.
- `Residual_RawTrieCoverage` is exactly `CertData.H3.Bridge.RawTrieCoverageLeaf`: the equivalence between a strict class bound and semantic raw-window validity remains a separate unproved leaf. The traversal-to-row direction needed here is already proved in `rawBatch_row`.
- `Residual_RawReplaySound` is exactly `CertData.H3.Bridge.RawReplaySoundLeaf`: successful replay must still be shown to produce a raw word and the complete `WalkRepresents` invariant. The numeric code component needed for the traversal was independently proved here.

After these leaves are available as proved dependencies, the exact requested theorem can be declared by applying `main_from_residuals` to them. There is no further representative or traversal residual.

## ORCH-SUMMARY

- STATUS: PARTIAL; no unconditional `AKLT.W.H3C011.main` is claimed.
- Delivered `Main.lean` and `Traversal.lean` in `AKLT/W/H3C011/`.
- `main_from_residuals` reduces `RawTrieProjectionLeaf` to exactly three closed leaves.
- Open: `CertData.H3.Bridge.RawRowSoundLeaf`.
- Open: `CertData.H3.Bridge.RawTrieCoverageLeaf`.
- Open: `CertData.H3.Bridge.RawReplaySoundLeaf`.
- None of these appears in the supplied proved-leaf index.
- Traversal, rejected packed spans, replay splitting, and representative assembly are proved.
- Reuses proved leaves `AKLT.W.H3C002.main` and `AKLT.W.H3C013.main`.
- Reuses retained packed-lane lemmas and `AKLT.Cert.H3.quotient_assembly`.
- Build passed: `lake build AKLT.W.H3C011.Main`, 13.81 seconds wall time.
- All seven exported theorem audits list only propext, Classical.choice, Quot.sound.
- No certificate normalization, forbidden proof constructs, or sub-agents.
- Earlier broad residuals were replaced, and `report.luna.md` was preserved.
- Orchestrator must prove/import the three exact leaves before registering H3C011 as proved.
