STATUS: PROVED

## Files

- `AKLT/W/H3C031/Main.lean` — the requested exact theorem and the complete transition proof; extends the earlier attempt.
- `AKLT/W/H3C031/Accounting.lean` — reward translation, prefix causality, departure-count and dead-mask accounting.
- `AKLT/W/H3C031/Check.lean` — independent import and exact-name/type check.
- `build.log`, `check.log` in this report directory — final verification output.

## Result

```lean
theorem AKLT.W.H3C031.main : CertData.H3.Bridge.PrefixStepLeaf
```

This theorem has no residual assumptions. Both closed obligations retained from the earlier attempt now have proofs: `phase_accounting : ResidualPhaseNumerators` and `item_accounting : ResidualRewardItems`.

The proof preserves all five components of `PrefixRepresents`. It combines the previous walk/base/timestamp arguments with: preservation of old rewards under snoc; equality of list departure counts with semantic departure counts; the exact four-bit dead-mask interpretation; translation invariance of relaxed rewards, including pair types and the one-live-neighbor case; and the rational phase update obtained from `ExactValid`. The trail premise supplies the nonreversal needed to apply the exact reward/response tables. The argument covers every `n`, including zero.

No certificate is normalized. The only finite case computations concern four compass directions and sixteen local masks, using kernel reduction. No other blueprint leaf is imported or used as a hypothesis. The geometric translation argument adapts the existing proof pattern in `AKLT/W/H3M020/Main.lean`; all required helper proofs are included here.

## Exported declarations and statements

All declarations below are in namespace `AKLT.W.H3C031`, with the same opens as the source files (`AKLT.Defs`, `AKLT.Cert.H3`, `AKLT.Cert.H3.Production`, `CertData.H3.Bridge`). These are signatures; proofs are in the delivered files.

From `Accounting.lean`:

```lean
theorem relaxedReward_translate (x t : Plane) (a d : Compass) (dead : Finset Plane) :
    relaxedReward (x + t) a d (dead.image (fun z => z + t)) =
      relaxedReward x a d dead

theorem snoc_incoming_last {n : Nat} (w : DirectionWord n) (d : Compass) :
    wordIncoming kernelIncoming (AKLT.Cert.H2.snoc w d) (Fin.last n) =
      AKLT.Cert.H2.nextIncoming kernelIncoming w

theorem walk_incoming_code {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) :
    walk.incoming = directionCode (AKLT.Cert.H2.nextIncoming kernelIncoming w)

theorem direction_code_inverse (d : Compass) : direction (directionCode d) = d

theorem direction_code_lt (d : Compass) : directionCode d < 4

theorem advance_code (x : Point) (d : Compass) :
    advance x (directionCode d) = x + d.step

theorem snoc_witness_old {n : Nat} (w : DirectionWord n) (d : Compass) (i : Fin n) :
    witnessKappa (AKLT.Cert.H2.snoc w d) i.castSucc = witnessKappa w i

theorem departures_represents {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) (z : Point) :
    departures walk z = departureCount kernelStart w n z

theorem deadMaskAt_lt (walk : Walk) : deadMaskAt walk < 16

theorem deadMaskAt_mem (walk : Walk) (c : Compass) :
    c.step ∈ deadSet (deadMaskAt walk) ↔
      advance walk.pos (directionCode c) = kernelCentre ∨
        2 ≤ departures walk (advance walk.pos (directionCode c))

theorem deadMaskAt_image_mem {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) (z : Point) (hz : z ∈ neighbours walk.pos) :
    z ∈ (deadSet (deadMaskAt walk)).image (fun y => y + walk.pos) ↔
      z = kernelCentre ∨ 2 ≤ departureCount kernelStart w n z

theorem witness_last_reward {n : Nat} (w : DirectionWord n) (d : Compass)
    (walk : Walk) (h : WalkRepresents kernelStart 2 w walk) :
    witnessKappa (AKLT.Cert.H2.snoc w d) (Fin.last n) =
      relaxedReward (0,0) (AKLT.Cert.H2.nextIncoming kernelIncoming w) d
        (deadSet (deadMaskAt walk))
```

From `Main.lean`:

```lean
theorem main_from_residuals (hPhase : ResidualPhaseNumerators)
    (hItems : ResidualRewardItems) : PrefixStepLeaf

theorem phase_accounting : ResidualPhaseNumerators

theorem item_accounting : ResidualRewardItems

theorem main : CertData.H3.Bridge.PrefixStepLeaf
```

The two closed proposition definitions retained for compatibility with the earlier attempt are:

```lean
def ResidualPhaseNumerators : Prop :=
  ∀ (E : Exact), ExactValid E → ∀ (n : Nat) (w : DirectionWord n)
    (s : PrefixState), PrefixRepresents E w s → ∀ d : Fin 4,
    IsTrail kernelStart kernelIncoming (appendWords w (fun _ : Fin 1 => direction d.val)) →
    ∀ φ : Phase,
      prefixPhases (appendWords w (fun _ : Fin 1 => direction d.val)) φ =
        (phaseNumerator (transition E s d.val) φ : ℚ) / (E.denominator^(n + 1) : Nat)

def ResidualRewardItems : Prop :=
  ∀ (E : Exact), ExactValid E → ∀ (n : Nat) (w : DirectionWord n)
    (s : PrefixState), PrefixRepresents E w s → ∀ d : Fin 4,
    IsTrail kernelStart kernelIncoming (appendWords w (fun _ : Fin 1 => direction d.val)) →
      ∀ item ∈ (transition E s d.val).items,
        ∃ i : Fin (n + 1), i.val = item.time ∧
          item.straight = wordStraight kernelIncoming
            (appendWords w (fun _ : Fin 1 => direction d.val)) i ∧
          (item.reward : ℚ) / E.denominator =
            witnessKappa (appendWords w (fun _ : Fin 1 => direction d.val)) i
```

## Axiom audit

`#print axioms` was run on every exported theorem. Final build output:

```text
'AKLT.W.H3C031.relaxedReward_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.snoc_incoming_last' depends on axioms: [propext, Quot.sound]
'AKLT.W.H3C031.walk_incoming_code' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.direction_code_inverse' does not depend on any axioms
'AKLT.W.H3C031.direction_code_lt' does not depend on any axioms
'AKLT.W.H3C031.advance_code' does not depend on any axioms
'AKLT.W.H3C031.snoc_witness_old' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.departures_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.deadMaskAt_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.deadMaskAt_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.deadMaskAt_image_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.witness_last_reward' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.phase_accounting' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.item_accounting' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every listed axiom is permitted. The delivered files contain none of the forbidden declarations, tactics, evaluator shortcuts or options.

## Build and exact-type check

Commands, with `PATH="$HOME/.elan/bin:$PATH"`:

```text
lake build AKLT.W.H3C031.Main
lake env lean AKLT/W/H3C031/Check.lean
```

The final build succeeded in 63.28 seconds (Accounting: 29 seconds; Main: 22 seconds). It reported one nonsemantic style warning about tactic sequencing in Main. No preexisting source file outside this task directory was edited.

The independent exact-type check succeeded in 11.38 seconds:

```text
AKLT.W.H3C031.main : CertData.H3.Bridge.PrefixStepLeaf
'AKLT.W.H3C031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
ELAPSED_SECONDS=11.38
```

## Open issues and deviations

No mathematical obligations remain open. The earlier missing `AKLT.W.H3C031.main` declaration now exists and imports successfully.

The requested cheaper-model first attempt could not be performed: this session provides no model-switch tool, and the brief explicitly forbids sub-agents. No sub-agent was used; the proof was completed directly in this session. This is a workflow deviation, not an additional mathematical premise.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C031/Main.lean` with the exact theorem `AKLT.W.H3C031.main : CertData.H3.Bridge.PrefixStepLeaf`.
- Added `Accounting.lean` and an independent `Check.lean`, all within the assigned directory.
- Both earlier residuals are proved by `phase_accounting` and `item_accounting`.
- Open mathematical names: none.
- Main axiom audit: `[propext, Classical.choice, Quot.sound]`.
- Final requested Lake build passed: 63.28 seconds.
- Independent import/exact-type check passed: 11.38 seconds.
- No whole-certificate normalization or prohibited proof shortcuts.
- No dependency on an unproved or separately imported blueprint leaf.
- One nonsemantic tactic-style warning remains.
- Workflow deviation: no alternate cheaper-model attempt was available; sub-agents were forbidden and unused.
- Orchestrator can validate and register the proved leaf; no further proof assignment is needed.
