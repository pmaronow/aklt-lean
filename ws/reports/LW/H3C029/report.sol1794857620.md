STATUS: PARTIAL

## Files

- `AKLT/W/H3C029/Main.lean`: one transparent residual and the assembly theorem.
- `AKLT/W/H3C029/Replay.lean`: compiled replay induction, decoder concatenation, trail extension, and initial-state lemmas.
- `/home/ubuntu/aklt/reports/LW/H3C029/build.log`: successful build and axiom audits.

No frozen statement, implementation, or file outside this task's directories was edited. The previous report remains in `report.luna.md`.

## Result and exact remaining dependency

The earlier two residuals merely separated the target's conjuncts. They have been replaced by a reduction to the existing, strictly local blueprint obligation:

```lean
def AKLT.W.H3C029.Residual_prefixStep : Prop :=
  CertData.H3.Bridge.PrefixStepLeaf

theorem AKLT.W.H3C029.main_of_prefixStep
    (hstep : AKLT.W.H3C029.Residual_prefixStep) :
    CertData.H3.Bridge.PrefixReplaySoundLeaf
```

The sole open leaf is **`CertData.H3.Bridge.PrefixStepLeaf`**. It is absent from `/home/ubuntu/aklt/state/lw/proved-index.tsv`. Its exact statement is:

```lean
∀ (E : Exact), ExactValid E → ∀ (n : Nat) (w : DirectionWord n)
  (s : PrefixState), PrefixRepresents E w s → ∀ d : Fin 4,
  IsTrail kernelStart kernelIncoming
    (appendWords w (fun _ : Fin 1 => direction d.val)) →
  PrefixRepresents E
    (appendWords w (fun _ : Fin 1 => direction d.val))
    (transition E s d.val)
```

Its remaining work concerns the phase and base-weight recurrences and the chronological reward-list invariant, including the relation between `deadMaskAt` and `witnessKappa`. This report makes no claim to prove that leaf. `CodeDecodeLeaf` is available in the index; it does not discharge the single-step semantic invariant. The decoder concatenation identity needed here is proved directly from `decodeWord` using natural-number division identities.

There is **no unconditional `AKLT.W.H3C029.main`**. The original exact-type check therefore remains unsatisfied. Once a proof of `PrefixStepLeaf` is available in the permitted index, the requested theorem follows by applying `main_of_prefixStep` to it.

## Exported declarations and statements

All declarations below are in namespace `AKLT.W.H3C029`; names from `AKLT.Defs`, `AKLT.Cert.H3`, `AKLT.Cert.H3.Production`, and `CertData.H3.Bridge` are opened in the source.

```lean
theorem trail_append_of_goodStep {n : Nat} (w : DirectionWord n) (s : Walk)
    (hrep : WalkRepresents kernelStart 2 w s)
    (htrail : IsTrail kernelStart kernelIncoming w)
    (d₀ : Nat) (d : Fin 4) (hgood : goodStep d₀ s d.val = true) :
    IsTrail kernelStart kernelIncoming
      (appendWords w (fun _ : Fin 1 => direction d.val))

theorem replayPrefix_snoc (E : Exact) (X : PairType)
    (d₀ n c : Nat) (s : PrefixState) :
    replayPrefix E X d₀ (n + 1) c s =
      (replayPrefix E X d₀ n (c / 4) s).bind (fun t =>
        if goodStep d₀ t.walk (c % 4) then
          replayPrefix E X d₀ 0 c (transition E t (c % 4)) else none)

theorem transition_walk (E : Exact) (s : PrefixState) (d : Nat) :
    (transition E s d).walk = s.walk.step d

theorem initial_represents (E : Exact) (c : Nat) :
    PrefixRepresents E (decodeWord 0 c) initial

theorem replay_sound_of_prefixStep (hstep : PrefixStepLeaf)
    (E : Exact) (hE : ExactValid E) (X : PairType) (d₀ : Fin 4) (n c : Nat)
    (hc : c < 4 ^ n) (s : PrefixState)
    (hs : replayPrefix E X d₀.val n c initial = some s) :
    PrefixRepresents E (decodeWord n c) s ∧
    IsTrail kernelStart kernelIncoming (decodeWord n c) ∧
    (0 < n → FirstDirection (decodeWord n c) (direction d₀.val)) ∧
    ∀ j ≤ n, wordVertex kernelStart (decodeWord n c) j ≠ kernelCentre ∧
      wordVertex kernelStart (decodeWord n c) j ≠ kernelTarget X
```

The last theorem works at every finite length; the target's bound `n ≤ 12` is unnecessary for the induction. It proves centre and target avoidance at every vertex, including the final vertex. The intermediate and final replay target tests are both retained. Initial reversal is excluded using the centre test; subsequent bond repetitions are excluded by the used-bond test. Sorting, chronological ties, and zero-reward comparisons are not modified.

## Axiom audit

The following is the `#print axioms` output for every exported theorem:

```text
'AKLT.W.H3C029.trail_append_of_goodStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.replayPrefix_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.transition_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.initial_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.replay_sound_of_prefixStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.main_of_prefixStep' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The residual is an explicit theorem parameter, not an axiom. No certificate data was normalized, and no prohibited proof mechanism was used.

## Validation

```text
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H3C029.Main
Build completed successfully (8974 jobs).
```

Measured wall time: **12.81 seconds**. Lake reported 4.3 seconds for `Replay.lean` and 3.5 seconds for `Main.lean`. Intermediate checks used `lake env lean AKLT/W/H3C029/Replay.lean`.

No sub-agents were used. The active model was not changed; the available tools do not provide an in-place model switch.

## ORCH-SUMMARY

- STATUS: PARTIAL.
- Delivered compiled `AKLT/W/H3C029/Main.lean` and `Replay.lean`.
- Replaced the previous two target-conjunct residuals with one local dependency.
- `Residual_prefixStep` is transparently `CertData.H3.Bridge.PrefixStepLeaf`.
- `main_of_prefixStep : Residual_prefixStep → PrefixReplaySoundLeaf` is proved.
- The replay induction covers arbitrary finite lengths, first direction, trail legality, and all vertex avoidance checks.
- Both intermediate and final target checks are retained.
- Exact open leaf: `CertData.H3.Bridge.PrefixStepLeaf`.
- No unconditional `AKLT.W.H3C029.main`; the requested exact-type check remains open.
- All exported theorems use only propext, Classical.choice, Quot.sound.
- Build passed in 12.81 seconds; no frozen files changed; no certificate normalization.
- No sub-agents or active-model switch were used.
- Orchestrator: prove/index `PrefixStepLeaf`, then apply `main_of_prefixStep` to obtain the requested `main`.
