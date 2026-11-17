STATUS: PROVED FROM DEPS

## Result

```lean
theorem AKLT.W.H3C034.main : CertData.H3.Bridge.PrefixBatchSoundLeaf
```

The theorem is closed and has exactly the requested name and type. No residual premise remains. The earlier `PrefixStemSoundResidual` has been removed. The supplied earlier attempt's report remains unchanged in `report.luna.md`.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Main.lean) — Exact closed theorem and batch assembly.
- [Tree.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Tree.lean) — Rational evaluator, radix-four reindexing, and finite-tree sum identity.
- [Words.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Words.lean) — Code/snoc identities, last-window code, and trail legality.
- [Flat.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Flat.lean) — Stem decomposition and propagation of accepted endpoint bounds.
- [Semantics.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Semantics.lean) — Replayed hit/frontier values and endpoint lookup binding.
- [Stem.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Stem.lean) — One-stem soundness and the exact length-interval reindexing.
- [ShortOrder.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/ShortOrder.lean) — Total, transitive, antisymmetric short order, including infinity and ties.
- [Short.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Short.lean) — Unconditional ShortValueLeaf proof using the registered comparator.
- [Replay.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Replay.lean) — Replay completeness from replay soundness.
- [ReplaySound.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/ReplaySound.lean) — Replay soundness from the exact step invariant.
- [PrefixStep/Accounting.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/PrefixStep/Accounting.lean) — Relocated registered H3C031 accounting proof.
- [PrefixStep/Main.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/PrefixStep/Main.lean) — Relocated registered H3C031 PrefixStepLeaf proof.
- [Check.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Check.lean) — Independent exact-type check.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_H3C034/AKLT/W/H3C034/Audit.lean) — Signatures and axiom checks for all 85 public theorems.

Verification artifacts in this report directory: [build.log](build.log), [check.log](check.log), [audit.log](audit.log), and [dependency-provenance.json](dependency-provenance.json).

## Proof and reused leaves

The proof expands the recursive evaluator into two disjoint sums: first target hits strictly after the stem depth, and surviving frontier endpoints at length twelve. A target state has no descendants. A hit at the stem depth is excluded from the stem contribution; a hit at length twelve contributes only its short value. Rejected stems contribute zero. The original semantic interval `Icc (depth+1) 12` is reindexed exactly, including depth twelve and empty batches.

Walk legality is connected to injectivity of unoriented trail bonds. Exact step representation proves replay soundness; replay soundness proves replay completeness. The short-value proof uses the registered comparator, a `WithTop ℚ` score with chronological tie breaking, uniqueness of the sorted index list, and exact denominator accounting. Its exponent bound is proved from `n ≤ 12` and the number of first visits. Endpoint acceptance propagates through the DFS to establish the class bounds required by `EndpointBinding`.

The batch fold preserves result-value addition. Every accepted stem is identified with `semanticStem`, then the list sum is identified with `semanticBatch`. The original quotient-correctness premise is accepted by the exact interface; this finite evaluation equality does not require it internally.

Registered dependencies reused:

| Statement | Registered theorem | Use |
| --- | --- | --- |
| `CodeDecodeLeaf` | `AKLT.W.H3C001.main` | Code/word and suffix identities. |
| `CodeEncodeLeaf` | `AKLT.W.H3C002.main` | Exact decoding and last-window code. |
| `EndpointBoxLeaf` | `AKLT.W.H3C019.main` | Valid endpoint lookup rectangle. |
| `ShortComparatorLeaf` | `AKLT.W.H3C032.main` | Exact sorting of reward items. |
| `PrefixStepLeaf` | `AKLT.W.H3C031.main` | Full one-step prefix representation. |

`PrefixStepLeaf` entered the shared proved index during this run. Its canonical source module was absent from this worktree snapshot. To keep all new files inside H3C034, its two registered proof sources were copied into `PrefixStep/` with only their namespace/import prefix relocated to `AKLT.W.H3C034.PrefixStep`, plus provenance comments. The full copied proofs compile here. Recorded source hashes and paths are in `dependency-provenance.json`; reversing the relocation reproduces the recorded sources exactly.

No whole certificate is normalized. No sub-agents were used, and no existing source outside the assigned task directory was edited.

## Principal exported declarations

All names below are in namespace `AKLT.W.H3C034`:

```lean
theorem main : CertData.H3.Bridge.PrefixBatchSoundLeaf

theorem main_of_deps :
  CertData.H3.Bridge.PrefixStepLeaf → CertData.H3.Bridge.PrefixBatchSoundLeaf

theorem shortValue_sound : CertData.H3.Bridge.ShortValueLeaf

theorem lastWindowCode : CertData.H3.Bridge.LastWindowCodeLeaf

theorem prefixReplay_sound_of_step :
  CertData.H3.Bridge.PrefixStepLeaf → CertData.H3.Bridge.PrefixReplaySoundLeaf

theorem prefixReplay_complete_of_sound :
  CertData.H3.Bridge.PrefixReplaySoundLeaf → CertData.H3.Bridge.PrefixReplayCompleteLeaf

theorem PrefixStep.main : CertData.H3.Bridge.PrefixStepLeaf
```

The complete Lean-printed inventory of exported declarations and statements, with every public theorem's axiom output, appears below.

## Validation

Commands use `PATH="$HOME/.elan/bin:$PATH"`.

| Command | Result | Wall time |
| --- | --- | --- |
| `lake build AKLT.W.H3C034.Main` | Passed | 29.82 s |
| `lake env lean AKLT/W/H3C034/Check.lean` | Passed | 4.33 s |
| `lake env lean AKLT/W/H3C034/Audit.lean` | Passed; all 85 public theorems audited | 6.45 s |

Independent exact-type check:

```text
AKLT.W.H3C034.main : CertData.H3.Bridge.PrefixBatchSoundLeaf
'AKLT.W.H3C034.main' depends on axioms: [propext, Classical.choice, Quot.sound]
WALL_SECONDS 4.33
```

All audited axioms are among `propext`, `Classical.choice`, and `Quot.sound`. A scan of all fourteen delivered Lean files found none of the forbidden declarations, tactics, evaluator shortcuts, or options. The copied dependency retains one nonsemantic tactic-sequencing style warning.

## Complete exported signatures and axiom audit

```text
AKLT.W.H3C034.main : CertData.H3.Bridge.PrefixBatchSoundLeaf
AKLT.W.H3C034.main_of_deps : CertData.H3.Bridge.PrefixStepLeaf → CertData.H3.Bridge.PrefixBatchSoundLeaf
AKLT.W.H3C034.optionValue (f : AKLT.Cert.H3.Production.PrefixState → ℚ) : Option AKLT.Cert.H3.Production.PrefixState → ℚ
AKLT.W.H3C034.nextNode (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ d : ℕ)
  (s : AKLT.Cert.H3.Production.PrefixState) : Option AKLT.Cert.H3.Production.PrefixState
AKLT.W.H3C034.runNode (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ : ℕ) :
  ℕ → ℕ → AKLT.Cert.H3.Production.PrefixState → Option AKLT.Cert.H3.Production.PrefixState
AKLT.W.H3C034.runNode_add (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n c e : ℕ)
  (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.runNode E X d₀ n (c * 4 ^ n + e) s = AKLT.W.H3C034.runNode E X d₀ n e s
'AKLT.W.H3C034.runNode_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.runNode_split (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n m c e : ℕ)
  (he : e < 4 ^ m) (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.runNode E X d₀ (n + m) (c * 4 ^ m + e) s =
    (AKLT.W.H3C034.runNode E X d₀ n c s).bind (AKLT.W.H3C034.runNode E X d₀ m e)
'AKLT.W.H3C034.runNode_split' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.replayPrefix_eq_runNode (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n c : ℕ)
  (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.Cert.H3.Production.replayPrefix E X d₀ n c s =
    (AKLT.W.H3C034.runNode E X d₀ n c s).bind fun t =>
      if t.walk.pos = AKLT.Cert.H3.Production.target X then none else some t
'AKLT.W.H3C034.replayPrefix_eq_runNode' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.children (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ : ℕ)
  (f : AKLT.Cert.H3.Production.PrefixState → ℚ) (s : AKLT.Cert.H3.Production.PrefixState) : ℚ
AKLT.W.H3C034.level (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ : ℕ)
  (f : AKLT.Cert.H3.Production.PrefixState → ℚ) (n : ℕ) (s : AKLT.Cert.H3.Production.PrefixState) : ℚ
AKLT.W.H3C034.level_zero (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ : ℕ)
  (f : AKLT.Cert.H3.Production.PrefixState → ℚ) (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.level E X d₀ f 0 s = f s
'AKLT.W.H3C034.level_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.sum_codes.{u_1} {R : Type u_1} [AddCommMonoid R] (n : ℕ) (f : ℕ → R) :
  ∑ e, f ↑e = ∑ d, ∑ e, f (↑d * 4 ^ n + ↑e)
'AKLT.W.H3C034.sum_codes' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.level_succ (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ : ℕ)
  (f : AKLT.Cert.H3.Production.PrefixState → ℚ) (n : ℕ) (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.level E X d₀ f (n + 1) s = AKLT.W.H3C034.children E X d₀ (AKLT.W.H3C034.level E X d₀ f n) s
'AKLT.W.H3C034.level_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.children_add (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ : ℕ)
  (f g : AKLT.Cert.H3.Production.PrefixState → ℚ) (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.children E X d₀ (fun t => f t + g t) s =
    AKLT.W.H3C034.children E X d₀ f s + AKLT.W.H3C034.children E X d₀ g s
'AKLT.W.H3C034.children_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.children_sum (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n : ℕ)
  (f : ℕ → AKLT.Cert.H3.Production.PrefixState → ℚ) (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.children E X d₀ (fun t => ∑ k ∈ Finset.range n, f k t) s =
    ∑ k ∈ Finset.range n, AKLT.W.H3C034.children E X d₀ (f k) s
'AKLT.W.H3C034.children_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.hitValue (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType)
  (s : AKLT.Cert.H3.Production.PrefixState) : ℚ
AKLT.W.H3C034.frontierValue (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (s : AKLT.Cert.H3.Production.PrefixState) : ℚ
AKLT.W.H3C034.treeValue (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ : ℕ) : ℕ → AKLT.Cert.H3.Production.PrefixState → ℚ
AKLT.W.H3C034.treeValue_flat (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n : ℕ) (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.treeValue G T E X d₀ n s =
    AKLT.W.H3C034.level E X d₀ (AKLT.W.H3C034.frontierValue G T E X) n s +
      ∑ k ∈ Finset.range (n + 1), AKLT.W.H3C034.level E X d₀ (AKLT.W.H3C034.hitValue E X) k s
'AKLT.W.H3C034.treeValue_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.resultValue_add (E : AKLT.Cert.H3.Production.Exact) (r s : AKLT.Cert.H3.Production.PrefixResult) :
  CertData.H3.Bridge.resultValue E (r.add s) = CertData.H3.Bridge.resultValue E r + CertData.H3.Bridge.resultValue E s
'AKLT.W.H3C034.resultValue_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.resultValue_fold (E : AKLT.Cert.H3.Production.Exact) (xs : List AKLT.Cert.H3.Production.PrefixResult)
  (acc : AKLT.Cert.H3.Production.PrefixResult) :
  CertData.H3.Bridge.resultValue E (List.foldl AKLT.Cert.H3.Production.PrefixResult.add acc xs) =
    CertData.H3.Bridge.resultValue E acc + (List.map (CertData.H3.Bridge.resultValue E) xs).sum
'AKLT.W.H3C034.resultValue_fold' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.prefixDFS_value (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n : ℕ) (s : AKLT.Cert.H3.Production.PrefixState) :
  CertData.H3.Bridge.resultValue E (AKLT.Cert.H3.Production.prefixDFS G T E X d₀ n s) =
    AKLT.W.H3C034.treeValue G T E X d₀ n s
'AKLT.W.H3C034.prefixDFS_value' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.decodeWord_mod (n c : ℕ) : AKLT.Cert.H3.decodeWord n (c % 4 ^ n) = AKLT.Cert.H3.decodeWord n c
'AKLT.W.H3C034.decodeWord_mod' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.lastWindowCode : CertData.H3.Bridge.LastWindowCodeLeaf
'AKLT.W.H3C034.lastWindowCode' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.decodeWord_snoc (n c d : ℕ) (hd : d < 4) :
  AKLT.Cert.H3.decodeWord (n + 1) (c * 4 + d) =
    AKLT.Cert.H2.snoc (AKLT.Cert.H3.decodeWord n c) (AKLT.Cert.H3.direction d)
'AKLT.W.H3C034.decodeWord_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.decodeWord_last (n c : ℕ) :
  AKLT.Cert.H3.decodeWord (n + 1) c =
    AKLT.Cert.H2.snoc (AKLT.Cert.H3.decodeWord n (c / 4)) (AKLT.Cert.H3.direction (c % 4))
'AKLT.W.H3C034.decodeWord_last' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.runNode_snoc (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n c d : ℕ) (hd : d < 4)
  (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.runNode E X d₀ (n + 1) (c * 4 + d) s =
    (AKLT.W.H3C034.runNode E X d₀ n c s).bind (AKLT.W.H3C034.nextNode E X d₀ d)
'AKLT.W.H3C034.runNode_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.runNode_last (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n c : ℕ)
  (s : AKLT.Cert.H3.Production.PrefixState) :
  AKLT.W.H3C034.runNode E X d₀ (n + 1) c s =
    (AKLT.W.H3C034.runNode E X d₀ n (c / 4) s).bind (AKLT.W.H3C034.nextNode E X d₀ (c % 4))
'AKLT.W.H3C034.runNode_last' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.append_one_eq_snoc {n : ℕ} (w : AKLT.Defs.DirectionWord n) (d : AKLT.Defs.Compass) :
  (AKLT.Defs.appendWords w fun x => d) = AKLT.Cert.H2.snoc w d
'AKLT.W.H3C034.append_one_eq_snoc' depends on axioms: [propext, Quot.sound]
AKLT.W.H3C034.direction_step (d : Fin 4) : AKLT.Cert.H3.Production.delta ↑d = (AKLT.Cert.H3.direction ↑d).step
'AKLT.W.H3C034.direction_step' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.advance_eq (x : AKLT.Cert.H3.Production.Point) (d : Fin 4) :
  AKLT.Cert.H3.Production.advance x ↑d = x + (AKLT.Cert.H3.direction ↑d).step
'AKLT.W.H3C034.advance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.transition_walk (E : AKLT.Cert.H3.Production.Exact) (s : AKLT.Cert.H3.Production.PrefixState) (d : ℕ) :
  (AKLT.Cert.H3.Production.transition E s d).walk = s.walk.step d
'AKLT.W.H3C034.transition_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.bond_symm (x y : AKLT.Cert.H3.Production.Point) :
  AKLT.Cert.H3.Production.bond x y = AKLT.Cert.H3.Production.bond y x
'AKLT.W.H3C034.bond_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.bond_iff (x y z t : AKLT.Cert.H3.Production.Point) :
  AKLT.Cert.H3.Production.bond x y = AKLT.Cert.H3.Production.bond z t ↔ {x, y} = {z, t}
'AKLT.W.H3C034.bond_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.legal_iff {n : ℕ} (w : AKLT.Defs.DirectionWord n) (s : AKLT.Cert.H3.Production.PrefixState)
  (hrep : CertData.H3.Bridge.WalkRepresents AKLT.Defs.kernelStart 2 w s.walk) (d : Fin 4) :
  s.walk.legal ↑d = true ↔
    ∀ (i : Fin n),
      AKLT.Defs.wordBond AKLT.Defs.kernelStart w i ≠
        {AKLT.Defs.wordVertex AKLT.Defs.kernelStart w n,
          AKLT.Defs.wordVertex AKLT.Defs.kernelStart w n + (AKLT.Cert.H3.direction ↑d).step}
'AKLT.W.H3C034.legal_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.trail_snoc_iff {n : ℕ} (w : AKLT.Defs.DirectionWord n) (d : AKLT.Defs.Compass) (hn : 1 ≤ n)
  (hw : AKLT.Defs.IsTrail AKLT.Defs.kernelStart AKLT.Defs.kernelIncoming w) :
  AKLT.Defs.IsTrail AKLT.Defs.kernelStart AKLT.Defs.kernelIncoming (AKLT.Cert.H2.snoc w d) ↔
    ∀ (i : Fin n),
      AKLT.Defs.wordBond AKLT.Defs.kernelStart w i ≠
        {AKLT.Defs.wordVertex AKLT.Defs.kernelStart w n, AKLT.Defs.wordVertex AKLT.Defs.kernelStart w n + d.step}
'AKLT.W.H3C034.trail_snoc_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.goodStep_iff {n : ℕ} (w : AKLT.Defs.DirectionWord n) (s : AKLT.Cert.H3.Production.PrefixState)
  (hrep : CertData.H3.Bridge.WalkRepresents AKLT.Defs.kernelStart 2 w s.walk) (hn : 1 ≤ n)
  (hw : AKLT.Defs.IsTrail AKLT.Defs.kernelStart AKLT.Defs.kernelIncoming w) (d₀ : ℕ) (d : Fin 4) :
  AKLT.Cert.H3.Production.goodStep d₀ s.walk ↑d = true ↔
    AKLT.Defs.IsTrail AKLT.Defs.kernelStart AKLT.Defs.kernelIncoming (AKLT.Cert.H2.snoc w (AKLT.Cert.H3.direction ↑d)) ∧
      AKLT.Defs.wordVertex AKLT.Defs.kernelStart (AKLT.Cert.H2.snoc w (AKLT.Cert.H3.direction ↑d)) (n + 1) ≠
        AKLT.Defs.kernelCentre
'AKLT.W.H3C034.goodStep_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.first_snoc_iff {n : ℕ} (w : AKLT.Defs.DirectionWord n) (d d₀ : AKLT.Defs.Compass) (hn : 1 ≤ n) :
  AKLT.Defs.FirstDirection (AKLT.Cert.H2.snoc w d) d₀ ↔ AKLT.Defs.FirstDirection w d₀
'AKLT.W.H3C034.first_snoc_iff' depends on axioms: [propext, Quot.sound]
AKLT.W.H3C034.globalLevel (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ depth code k : ℕ)
  (f : AKLT.Cert.H3.Production.PrefixState → ℚ) : ℚ
AKLT.W.H3C034.globalLevel_eq (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ depth code k : ℕ)
  (f : AKLT.Cert.H3.Production.PrefixState → ℚ) :
  AKLT.W.H3C034.globalLevel E X d₀ depth code k f =
    AKLT.W.H3C034.optionValue (AKLT.W.H3C034.level E X d₀ f k)
      (AKLT.W.H3C034.runNode E X d₀ depth code AKLT.Cert.H3.Production.initial)
'AKLT.W.H3C034.globalLevel_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.runNode_from_hit (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n c : ℕ)
  (s : AKLT.Cert.H3.Production.PrefixState) (hs : s.walk.pos = AKLT.Cert.H3.Production.target X) :
  AKLT.W.H3C034.runNode E X d₀ (n + 1) c s = none
'AKLT.W.H3C034.runNode_from_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.level_from_hit (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n : ℕ)
  (f : AKLT.Cert.H3.Production.PrefixState → ℚ) (s : AKLT.Cert.H3.Production.PrefixState)
  (hs : s.walk.pos = AKLT.Cert.H3.Production.target X) : AKLT.W.H3C034.level E X d₀ f (n + 1) s = 0
'AKLT.W.H3C034.level_from_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.frontier_from_hit (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n : ℕ) (s : AKLT.Cert.H3.Production.PrefixState)
  (hs : s.walk.pos = AKLT.Cert.H3.Production.target X) :
  AKLT.W.H3C034.level E X d₀ (AKLT.W.H3C034.frontierValue G T E X) n s = 0
'AKLT.W.H3C034.frontier_from_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.prefixStem_flat (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ depth code : ℕ) :
  CertData.H3.Bridge.resultValue E (AKLT.Cert.H3.Production.prefixStem G T E X d₀ depth code) =
    AKLT.W.H3C034.globalLevel E X d₀ depth code (12 - depth) (AKLT.W.H3C034.frontierValue G T E X) +
      ∑ k ∈ Finset.range (12 - depth), AKLT.W.H3C034.globalLevel E X d₀ depth code (k + 1) (AKLT.W.H3C034.hitValue E X)
'AKLT.W.H3C034.prefixStem_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.fold_ok_member (xs : List AKLT.Cert.H3.Production.PrefixResult)
  (acc : AKLT.Cert.H3.Production.PrefixResult)
  (h : (List.foldl AKLT.Cert.H3.Production.PrefixResult.add acc xs).ok = true)
  (r : AKLT.Cert.H3.Production.PrefixResult) (hr : r ∈ xs) : r.ok = true
'AKLT.W.H3C034.fold_ok_member' depends on axioms: [propext, Quot.sound]
AKLT.W.H3C034.prefixDFS_endpoint_ok (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n c : ℕ) (s t : AKLT.Cert.H3.Production.PrefixState)
  (hok : (AKLT.Cert.H3.Production.prefixDFS G T E X d₀ n s).ok = true)
  (hrun : AKLT.W.H3C034.runNode E X d₀ n c s = some t) (ht : t.walk.pos ≠ AKLT.Cert.H3.Production.target X) :
  (AKLT.Cert.H3.Production.leafValue G T t).ok = true
'AKLT.W.H3C034.prefixDFS_endpoint_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.runNode_source_not_hit (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ n c : ℕ)
  (s t : AKLT.Cert.H3.Production.PrefixState) (hrun : AKLT.W.H3C034.runNode E X d₀ n c s = some t)
  (ht : t.walk.pos ≠ AKLT.Cert.H3.Production.target X) : s.walk.pos ≠ AKLT.Cert.H3.Production.target X
'AKLT.W.H3C034.runNode_source_not_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.prefixStem_endpoint_ok (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (X : AKLT.Defs.PairType) (d₀ depth code k e : ℕ) (he : e < 4 ^ k)
  (hok : (AKLT.Cert.H3.Production.prefixStem G T E X d₀ depth code).ok = true) (hk : depth + k = 12)
  (s : AKLT.Cert.H3.Production.PrefixState)
  (hrun : AKLT.W.H3C034.runNode E X d₀ (depth + k) (code * 4 ^ k + e) AKLT.Cert.H3.Production.initial = some s)
  (hs : s.walk.pos ≠ AKLT.Cert.H3.Production.target X) : (AKLT.Cert.H3.Production.leafValue G T s).ok = true
'AKLT.W.H3C034.prefixStem_endpoint_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.target_eq (X : AKLT.Defs.PairType) : AKLT.Cert.H3.Production.target X = AKLT.Defs.kernelTarget X
'AKLT.W.H3C034.target_eq' does not depend on any axioms
AKLT.W.H3C034.runNode_replay {E : AKLT.Cert.H3.Production.Exact} {X : AKLT.Defs.PairType} {d₀ n c : ℕ}
  {s : AKLT.Cert.H3.Production.PrefixState}
  (hrun : AKLT.W.H3C034.runNode E X d₀ n c AKLT.Cert.H3.Production.initial = some s)
  (hs : s.walk.pos ≠ AKLT.Cert.H3.Production.target X) :
  AKLT.Cert.H3.Production.replayPrefix E X d₀ n c AKLT.Cert.H3.Production.initial = some s
'AKLT.W.H3C034.runNode_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.replay_runNode {E : AKLT.Cert.H3.Production.Exact} {X : AKLT.Defs.PairType} {d₀ n c : ℕ}
  {s : AKLT.Cert.H3.Production.PrefixState}
  (hrun : AKLT.Cert.H3.Production.replayPrefix E X d₀ n c AKLT.Cert.H3.Production.initial = some s) :
  AKLT.W.H3C034.runNode E X d₀ n c AKLT.Cert.H3.Production.initial = some s ∧
    s.walk.pos ≠ AKLT.Cert.H3.Production.target X
'AKLT.W.H3C034.replay_runNode' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.node_surviving (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf) (E : AKLT.Cert.H3.Production.Exact)
  (hv : CertData.H3.Bridge.ExactValid E) (X : AKLT.Defs.PairType) (d₀ : Fin 4) (n c : ℕ) (hn : 1 ≤ n) (hn12 : n ≤ 12)
  (hc : c < 4 ^ n) (s : AKLT.Cert.H3.Production.PrefixState)
  (hrun : AKLT.W.H3C034.runNode E X (↑d₀) n c AKLT.Cert.H3.Production.initial = some s)
  (hs : s.walk.pos ≠ AKLT.Cert.H3.Production.target X) :
  CertData.H3.Bridge.PrefixRepresents E (AKLT.Cert.H3.decodeWord n c) s ∧
    AKLT.Defs.SurvivingPrefix X (AKLT.Cert.H3.direction ↑d₀) (AKLT.Cert.H3.decodeWord n c)
'AKLT.W.H3C034.node_surviving' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.node_closed (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf)
  (hStep : CertData.H3.Bridge.PrefixStepLeaf) (E : AKLT.Cert.H3.Production.Exact) (hv : CertData.H3.Bridge.ExactValid E)
  (X : AKLT.Defs.PairType) (d₀ : Fin 4) (n c : ℕ) (hn : 2 ≤ n) (hn12 : n ≤ 12) (hc : c < 4 ^ n)
  (s : AKLT.Cert.H3.Production.PrefixState)
  (hrun : AKLT.W.H3C034.runNode E X (↑d₀) n c AKLT.Cert.H3.Production.initial = some s)
  (hs : s.walk.pos = AKLT.Cert.H3.Production.target X) :
  CertData.H3.Bridge.PrefixRepresents E (AKLT.Cert.H3.decodeWord n c) s ∧
    AKLT.Defs.ClosedTrail X (AKLT.Cert.H3.decodeWord n c) ∧
      AKLT.Defs.FirstDirection (AKLT.Cert.H3.decodeWord n c) (AKLT.Cert.H3.direction ↑d₀)
'AKLT.W.H3C034.node_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.closed_parent {X : AKLT.Defs.PairType} {d₀ : AKLT.Defs.Compass} {m c : ℕ} (hm : 1 ≤ m)
  (hw : AKLT.Defs.ClosedTrail X (AKLT.Cert.H3.decodeWord (m + 1) c))
  (hd : AKLT.Defs.FirstDirection (AKLT.Cert.H3.decodeWord (m + 1) c) d₀) :
  AKLT.Defs.SurvivingPrefix X d₀ (AKLT.Cert.H3.decodeWord m (c / 4))
'AKLT.W.H3C034.closed_parent' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.node_closed_complete (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf)
  (hComplete : CertData.H3.Bridge.PrefixReplayCompleteLeaf) (E : AKLT.Cert.H3.Production.Exact)
  (hv : CertData.H3.Bridge.ExactValid E) (X : AKLT.Defs.PairType) (d₀ : Fin 4) (n c : ℕ) (hn : 2 ≤ n) (hn12 : n ≤ 12)
  (hc : c < 4 ^ n) (hw : AKLT.Defs.ClosedTrail X (AKLT.Cert.H3.decodeWord n c))
  (hd : AKLT.Defs.FirstDirection (AKLT.Cert.H3.decodeWord n c) (AKLT.Cert.H3.direction ↑d₀)) :
  ∃ s,
    AKLT.W.H3C034.runNode E X (↑d₀) n c AKLT.Cert.H3.Production.initial = some s ∧
      s.walk.pos = AKLT.Cert.H3.Production.target X
'AKLT.W.H3C034.node_closed_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.node_hit_value (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf)
  (hComplete : CertData.H3.Bridge.PrefixReplayCompleteLeaf) (hStep : CertData.H3.Bridge.PrefixStepLeaf)
  (hShort : CertData.H3.Bridge.ShortValueLeaf) (E : AKLT.Cert.H3.Production.Exact)
  (hv : CertData.H3.Bridge.ExactValid E) (X : AKLT.Defs.PairType) (d₀ : Fin 4) (n c : ℕ) (hn : 2 ≤ n) (hn12 : n ≤ 12)
  (hc : c < 4 ^ n) :
  AKLT.W.H3C034.optionValue (AKLT.W.H3C034.hitValue E X)
      (AKLT.W.H3C034.runNode E X (↑d₀) n c AKLT.Cert.H3.Production.initial) =
    if
        AKLT.Defs.ClosedTrail X (AKLT.Cert.H3.decodeWord n c) ∧
          AKLT.Defs.FirstDirection (AKLT.Cert.H3.decodeWord n c) (AKLT.Cert.H3.direction ↑d₀) then
      AKLT.Defs.closedContribution (AKLT.Cert.H3.decodeWord n c)
    else 0
'AKLT.W.H3C034.node_hit_value' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.leaf_value (G : AKLT.Cert.H3.Production.Graph) (T lookup : AKLT.Cert.H3.Production.Tables)
  (E : AKLT.Cert.H3.Production.Exact) (hbinding : CertData.H3.Bridge.EndpointBinding T lookup)
  (w : AKLT.Defs.DirectionWord 12) (s : AKLT.Cert.H3.Production.PrefixState)
  (hrep : CertData.H3.Bridge.PrefixRepresents E w s) (hok : (AKLT.Cert.H3.Production.leafValue G lookup s).ok = true) :
  CertData.H3.Bridge.resultValue E (AKLT.Cert.H3.Production.leafValue G lookup s) =
    ∑ φ,
      AKLT.Defs.prefixPhases w φ *
        T.data.potential φ (G.quotient.project (AKLT.Defs.lastWindowWord 10 w))
          (AKLT.Defs.wordVertex AKLT.Defs.kernelStart w 12)
'AKLT.W.H3C034.leaf_value' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.shortScore {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n) : WithTop ℚ
AKLT.W.H3C034.shortOrder_iff {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i j : Fin n) :
  AKLT.Defs.shortOrderLE w i j = true ↔
    AKLT.W.H3C034.shortScore w i < AKLT.W.H3C034.shortScore w j ∨
      AKLT.W.H3C034.shortScore w i = AKLT.W.H3C034.shortScore w j ∧ ↑i ≤ ↑j
'AKLT.W.H3C034.shortOrder_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.shortOrder_trans {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i j k : Fin n)
  (hij : AKLT.Defs.shortOrderLE w i j = true) (hjk : AKLT.Defs.shortOrderLE w j k = true) :
  AKLT.Defs.shortOrderLE w i k = true
'AKLT.W.H3C034.shortOrder_trans' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.shortOrder_total {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i j : Fin n) :
  (AKLT.Defs.shortOrderLE w i j || AKLT.Defs.shortOrderLE w j i) = true
'AKLT.W.H3C034.shortOrder_total' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.shortOrder_antisymm {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i j : Fin n)
  (hij : AKLT.Defs.shortOrderLE w i j = true) (hji : AKLT.Defs.shortOrderLE w j i = true) : i = j
'AKLT.W.H3C034.shortOrder_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.sort_reverse {n : ℕ} (w : AKLT.Defs.DirectionWord n) (xs : List (Fin n)) :
  xs.reverse.mergeSort (AKLT.Defs.shortOrderLE w) = xs.mergeSort (AKLT.Defs.shortOrderLE w)
'AKLT.W.H3C034.sort_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.shortValue_sound : CertData.H3.Bridge.ShortValueLeaf
'AKLT.W.H3C034.shortValue_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.direction_inj (a b : Fin 4) (h : AKLT.Cert.H3.direction ↑a = AKLT.Cert.H3.direction ↑b) : a = b
'AKLT.W.H3C034.direction_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.prefixReplay_complete_of_sound (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf) :
  CertData.H3.Bridge.PrefixReplayCompleteLeaf
'AKLT.W.H3C034.prefixReplay_complete_of_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.TraceValid (X : AKLT.Defs.PairType) (d₀ : AKLT.Defs.Compass) {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  Prop
AKLT.W.H3C034.initial_rep (E : AKLT.Cert.H3.Production.Exact) (c : ℕ) :
  CertData.H3.Bridge.PrefixRepresents E (AKLT.Cert.H3.decodeWord 0 c) AKLT.Cert.H3.Production.initial
'AKLT.W.H3C034.initial_rep' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.initial_trace (X : AKLT.Defs.PairType) (d₀ : AKLT.Defs.Compass) (c : ℕ) :
  AKLT.W.H3C034.TraceValid X d₀ (AKLT.Cert.H3.decodeWord 0 c)
'AKLT.W.H3C034.initial_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.trace_snoc {E : AKLT.Cert.H3.Production.Exact} {X : AKLT.Defs.PairType} {d₀ : Fin 4} {n : ℕ}
  {w : AKLT.Defs.DirectionWord n} {s : AKLT.Cert.H3.Production.PrefixState}
  (hrep : CertData.H3.Bridge.PrefixRepresents E w s) (hw : AKLT.W.H3C034.TraceValid X (AKLT.Cert.H3.direction ↑d₀) w)
  (hs : s.walk.pos ≠ AKLT.Cert.H3.Production.target X) (d : Fin 4)
  (hg : AKLT.Cert.H3.Production.goodStep (↑d₀) s.walk ↑d = true) :
  AKLT.W.H3C034.TraceValid X (AKLT.Cert.H3.direction ↑d₀) (AKLT.Cert.H2.snoc w (AKLT.Cert.H3.direction ↑d))
'AKLT.W.H3C034.trace_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.runNode_sound_of_step (hStep : CertData.H3.Bridge.PrefixStepLeaf) (E : AKLT.Cert.H3.Production.Exact)
  (hv : CertData.H3.Bridge.ExactValid E) (X : AKLT.Defs.PairType) (d₀ : Fin 4) (n c : ℕ)
  (s : AKLT.Cert.H3.Production.PrefixState)
  (hrun : AKLT.W.H3C034.runNode E X (↑d₀) n c AKLT.Cert.H3.Production.initial = some s) :
  CertData.H3.Bridge.PrefixRepresents E (AKLT.Cert.H3.decodeWord n c) s ∧
    AKLT.W.H3C034.TraceValid X (AKLT.Cert.H3.direction ↑d₀) (AKLT.Cert.H3.decodeWord n c)
'AKLT.W.H3C034.runNode_sound_of_step' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.prefixReplay_sound_of_step (hStep : CertData.H3.Bridge.PrefixStepLeaf) :
  CertData.H3.Bridge.PrefixReplaySoundLeaf
'AKLT.W.H3C034.prefixReplay_sound_of_step' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.extended_code_lt (depth code k e : ℕ) (hc : code < 4 ^ depth) (he : e < 4 ^ k) :
  code * 4 ^ k + e < 4 ^ (depth + k)
'AKLT.W.H3C034.extended_code_lt' depends on axioms: [propext]
AKLT.W.H3C034.global_frontier (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf)
  (hComplete : CertData.H3.Bridge.PrefixReplayCompleteLeaf) (G : AKLT.Cert.H3.Production.Graph)
  (T lookup : AKLT.Cert.H3.Production.Tables) (E : AKLT.Cert.H3.Production.Exact) (hv : CertData.H3.Bridge.ExactValid E)
  (hb : CertData.H3.Bridge.EndpointBinding T lookup) (X : AKLT.Defs.PairType) (d₀ : Fin 4) (depth code : ℕ)
  (hd12 : depth ≤ 12) (hc : code < 4 ^ depth)
  (hok : (AKLT.Cert.H3.Production.prefixStem G lookup E X (↑d₀) depth code).ok = true) :
  AKLT.W.H3C034.globalLevel E X (↑d₀) depth code (12 - depth) (AKLT.W.H3C034.frontierValue G lookup E X) =
    AKLT.Cert.H3.prefixShard G.quotient T.data X (AKLT.Cert.H3.direction ↑d₀) fun e =>
      AKLT.Cert.H3.decodeWord 12 (code * 4 ^ (12 - depth) + ↑e)
'AKLT.W.H3C034.global_frontier' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.global_hit (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf)
  (hComplete : CertData.H3.Bridge.PrefixReplayCompleteLeaf) (hStep : CertData.H3.Bridge.PrefixStepLeaf)
  (hShort : CertData.H3.Bridge.ShortValueLeaf) (E : AKLT.Cert.H3.Production.Exact)
  (hv : CertData.H3.Bridge.ExactValid E) (X : AKLT.Defs.PairType) (d₀ : Fin 4) (depth code k : ℕ) (hd : 1 ≤ depth)
  (hk : depth + (k + 1) ≤ 12) (hc : code < 4 ^ depth) :
  AKLT.W.H3C034.globalLevel E X (↑d₀) depth code (k + 1) (AKLT.W.H3C034.hitValue E X) =
    ∑ e,
      if
          AKLT.Defs.ClosedTrail X (AKLT.Cert.H3.decodeWord (depth + (k + 1)) (code * 4 ^ (k + 1) + ↑e)) ∧
            AKLT.Defs.FirstDirection (AKLT.Cert.H3.decodeWord (depth + (k + 1)) (code * 4 ^ (k + 1) + ↑e))
              (AKLT.Cert.H3.direction ↑d₀) then
        AKLT.Defs.closedContribution (AKLT.Cert.H3.decodeWord (depth + (k + 1)) (code * 4 ^ (k + 1) + ↑e))
      else 0
'AKLT.W.H3C034.global_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.sum_lengths (f : ℕ → ℚ) (depth : ℕ) :
  ∑ n ∈ Finset.Icc (depth + 1) 12, f n = ∑ k ∈ Finset.range (12 - depth), f (depth + (k + 1))
'AKLT.W.H3C034.sum_lengths' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.sum_fin_eq (f : ℕ → ℚ) (a b : ℕ) (h : a = b) : ∑ e, f ↑e = ∑ e, f ↑e
'AKLT.W.H3C034.sum_fin_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.semanticStem_eq (G : AKLT.Cert.H3.Production.Graph) (T : AKLT.Cert.H3.Production.Tables)
  (X : AKLT.Defs.PairType) (d₀ : AKLT.Defs.Compass) (depth code : ℕ) :
  CertData.H3.Bridge.semanticStem G T X d₀ depth code =
    (AKLT.Cert.H3.prefixShard G.quotient T.data X d₀ fun e =>
        AKLT.Cert.H3.decodeWord 12 (code * 4 ^ (12 - depth) + ↑e)) +
      ∑ k ∈ Finset.range (12 - depth),
        ∑ e,
          if
              AKLT.Defs.ClosedTrail X (AKLT.Cert.H3.decodeWord (depth + (k + 1)) (code * 4 ^ (k + 1) + ↑e)) ∧
                AKLT.Defs.FirstDirection (AKLT.Cert.H3.decodeWord (depth + (k + 1)) (code * 4 ^ (k + 1) + ↑e)) d₀ then
            AKLT.Defs.closedContribution (AKLT.Cert.H3.decodeWord (depth + (k + 1)) (code * 4 ^ (k + 1) + ↑e))
          else 0
'AKLT.W.H3C034.semanticStem_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.prefixStem_sound (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf)
  (hComplete : CertData.H3.Bridge.PrefixReplayCompleteLeaf) (hStep : CertData.H3.Bridge.PrefixStepLeaf)
  (hShort : CertData.H3.Bridge.ShortValueLeaf) (G : AKLT.Cert.H3.Production.Graph)
  (T lookup : AKLT.Cert.H3.Production.Tables) (E : AKLT.Cert.H3.Production.Exact) (hv : CertData.H3.Bridge.ExactValid E)
  (hb : CertData.H3.Bridge.EndpointBinding T lookup) (X : AKLT.Defs.PairType) (d₀ : Fin 4) (depth code : ℕ)
  (hd : 1 ≤ depth) (hd12 : depth ≤ 12) (hc : code < 4 ^ depth)
  (hok : (AKLT.Cert.H3.Production.prefixStem G lookup E X (↑d₀) depth code).ok = true) :
  CertData.H3.Bridge.resultValue E (AKLT.Cert.H3.Production.prefixStem G lookup E X (↑d₀) depth code) =
    CertData.H3.Bridge.semanticStem G T X (AKLT.Cert.H3.direction ↑d₀) depth code
'AKLT.W.H3C034.prefixStem_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.relaxedReward_translate (x t : AKLT.Defs.Plane) (a d : AKLT.Defs.Compass)
  (dead : Finset AKLT.Defs.Plane) :
  AKLT.Defs.relaxedReward (x + t) a d (Finset.image (fun z => z + t) dead) = AKLT.Defs.relaxedReward x a d dead
'AKLT.W.H3C034.PrefixStep.relaxedReward_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.snoc_incoming_last {n : ℕ} (w : AKLT.Defs.DirectionWord n) (d : AKLT.Defs.Compass) :
  AKLT.Defs.wordIncoming AKLT.Defs.kernelIncoming (AKLT.Cert.H2.snoc w d) (Fin.last n) =
    AKLT.Cert.H2.nextIncoming AKLT.Defs.kernelIncoming w
'AKLT.W.H3C034.PrefixStep.snoc_incoming_last' depends on axioms: [propext, Quot.sound]
AKLT.W.H3C034.PrefixStep.walk_incoming_code {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (walk : AKLT.Cert.H3.Production.Walk) (h : CertData.H3.Bridge.WalkRepresents AKLT.Defs.kernelStart 2 w walk) :
  walk.incoming = AKLT.Cert.H3.directionCode (AKLT.Cert.H2.nextIncoming AKLT.Defs.kernelIncoming w)
'AKLT.W.H3C034.PrefixStep.walk_incoming_code' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.direction_code_inverse (d : AKLT.Defs.Compass) :
  AKLT.Cert.H3.direction (AKLT.Cert.H3.directionCode d) = d
'AKLT.W.H3C034.PrefixStep.direction_code_inverse' does not depend on any axioms
AKLT.W.H3C034.PrefixStep.direction_code_lt (d : AKLT.Defs.Compass) : AKLT.Cert.H3.directionCode d < 4
'AKLT.W.H3C034.PrefixStep.direction_code_lt' does not depend on any axioms
AKLT.W.H3C034.PrefixStep.advance_code (x : AKLT.Cert.H3.Production.Point) (d : AKLT.Defs.Compass) :
  AKLT.Cert.H3.Production.advance x (AKLT.Cert.H3.directionCode d) = x + d.step
'AKLT.W.H3C034.PrefixStep.advance_code' does not depend on any axioms
AKLT.W.H3C034.PrefixStep.snoc_witness_old {n : ℕ} (w : AKLT.Defs.DirectionWord n) (d : AKLT.Defs.Compass) (i : Fin n) :
  AKLT.Defs.witnessKappa (AKLT.Cert.H2.snoc w d) i.castSucc = AKLT.Defs.witnessKappa w i
'AKLT.W.H3C034.PrefixStep.snoc_witness_old' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.departures_represents {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (walk : AKLT.Cert.H3.Production.Walk) (h : CertData.H3.Bridge.WalkRepresents AKLT.Defs.kernelStart 2 w walk)
  (z : AKLT.Cert.H3.Production.Point) :
  AKLT.Cert.H3.Production.departures walk z = AKLT.Defs.departureCount AKLT.Defs.kernelStart w n z
'AKLT.W.H3C034.PrefixStep.departures_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.deadMaskAt_lt (walk : AKLT.Cert.H3.Production.Walk) :
  AKLT.Cert.H3.Production.deadMaskAt walk < 16
'AKLT.W.H3C034.PrefixStep.deadMaskAt_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.deadMaskAt_mem (walk : AKLT.Cert.H3.Production.Walk) (c : AKLT.Defs.Compass) :
  c.step ∈ CertData.H3.Bridge.deadSet (AKLT.Cert.H3.Production.deadMaskAt walk) ↔
    AKLT.Cert.H3.Production.advance walk.pos (AKLT.Cert.H3.directionCode c) = AKLT.Defs.kernelCentre ∨
      2 ≤
        AKLT.Cert.H3.Production.departures walk
          (AKLT.Cert.H3.Production.advance walk.pos (AKLT.Cert.H3.directionCode c))
'AKLT.W.H3C034.PrefixStep.deadMaskAt_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.deadMaskAt_image_mem {n : ℕ} (w : AKLT.Defs.DirectionWord n)
  (walk : AKLT.Cert.H3.Production.Walk) (h : CertData.H3.Bridge.WalkRepresents AKLT.Defs.kernelStart 2 w walk)
  (z : AKLT.Cert.H3.Production.Point) (hz : z ∈ AKLT.Defs.neighbours walk.pos) :
  z ∈ Finset.image (fun y => y + walk.pos) (CertData.H3.Bridge.deadSet (AKLT.Cert.H3.Production.deadMaskAt walk)) ↔
    z = AKLT.Defs.kernelCentre ∨ 2 ≤ AKLT.Defs.departureCount AKLT.Defs.kernelStart w n z
'AKLT.W.H3C034.PrefixStep.deadMaskAt_image_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.witness_last_reward {n : ℕ} (w : AKLT.Defs.DirectionWord n) (d : AKLT.Defs.Compass)
  (walk : AKLT.Cert.H3.Production.Walk) (h : CertData.H3.Bridge.WalkRepresents AKLT.Defs.kernelStart 2 w walk) :
  AKLT.Defs.witnessKappa (AKLT.Cert.H2.snoc w d) (Fin.last n) =
    AKLT.Defs.relaxedReward (0, 0) (AKLT.Cert.H2.nextIncoming AKLT.Defs.kernelIncoming w) d
      (CertData.H3.Bridge.deadSet (AKLT.Cert.H3.Production.deadMaskAt walk))
'AKLT.W.H3C034.PrefixStep.witness_last_reward' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.ResidualPhaseNumerators : Prop
AKLT.W.H3C034.PrefixStep.ResidualRewardItems : Prop
AKLT.W.H3C034.PrefixStep.main_from_residuals (hPhase : AKLT.W.H3C034.PrefixStep.ResidualPhaseNumerators)
  (hItems : AKLT.W.H3C034.PrefixStep.ResidualRewardItems) : CertData.H3.Bridge.PrefixStepLeaf
'AKLT.W.H3C034.PrefixStep.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.phase_accounting : AKLT.W.H3C034.PrefixStep.ResidualPhaseNumerators
'AKLT.W.H3C034.PrefixStep.phase_accounting' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.item_accounting : AKLT.W.H3C034.PrefixStep.ResidualRewardItems
'AKLT.W.H3C034.PrefixStep.item_accounting' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.PrefixStep.main : CertData.H3.Bridge.PrefixStepLeaf
'AKLT.W.H3C034.PrefixStep.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.batch_sound_of_replay (hSound : CertData.H3.Bridge.PrefixReplaySoundLeaf)
  (hComplete : CertData.H3.Bridge.PrefixReplayCompleteLeaf) (hStep : CertData.H3.Bridge.PrefixStepLeaf)
  (hShort : CertData.H3.Bridge.ShortValueLeaf) : CertData.H3.Bridge.PrefixBatchSoundLeaf
'AKLT.W.H3C034.batch_sound_of_replay' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.main_of_deps (hStep : CertData.H3.Bridge.PrefixStepLeaf) : CertData.H3.Bridge.PrefixBatchSoundLeaf
'AKLT.W.H3C034.main_of_deps' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H3C034.main : CertData.H3.Bridge.PrefixBatchSoundLeaf
'AKLT.W.H3C034.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

None. The requested unconditional theorem exists and passes the independent exact-type check. The local relocation of the newly registered H3C031 dependency is the only packaging deviation; it requires no external source or compiled artifact at build time.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C034/Main.lean` with exact `AKLT.W.H3C034.main : CertData.H3.Bridge.PrefixBatchSoundLeaf`.
- STATUS: PROVED FROM DEPS; no residual assumptions or open mathematical obligations.
- Reused indexed H3C001, H3C002, H3C019, H3C032, and newly registered H3C031.
- H3C031 sources were relocated into the task directory because its canonical module was absent locally.
- Dependency source hashes and exact relocation provenance are recorded in `dependency-provenance.json`.
- Also proved `shortValue_sound : ShortValueLeaf` and `lastWindowCode : LastWindowCodeLeaf`.
- Replay soundness follows from PrefixStepLeaf; completeness follows from replay soundness.
- Early hits, surviving frontier, chronological ties, zero-reward infinity, and fixed scales are exact.
- No certificate normalization, forbidden proof shortcuts, or sub-agents.
- Main build passed in 29.82 s; independent exact-type check passed in 4.33 s.
- All 85 public theorems passed the axiom audit in 6.45 s.
- Main axioms: `[propext, Classical.choice, Quot.sound]`.
- One inherited nonsemantic tactic-style warning; no other limitation.
- Orchestrator may register the exact closed theorem; no further proof assignment is needed.
