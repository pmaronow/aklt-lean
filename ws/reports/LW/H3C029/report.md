STATUS: PROVED FROM DEPS

## Files

- `AKLT/W/H3C029/Main.lean`: imports the proved single-step leaf and exports the required unconditional theorem.
- `AKLT/W/H3C029/Replay.lean`: retained unchanged from the earlier attempt; supplies the replay induction and path invariants.

Only `Main.lean` was changed in this run. No frozen statement, certificate, or file outside the assigned directories was edited.

## Proof and dependencies

The sole blueprint dependency is the indexed theorem
`AKLT.W.H3C031.main : CertData.H3.Bridge.PrefixStepLeaf`, imported from
`AKLT.W.H3C031.Main`. The previous conditional replay proof is discharged by
this theorem. The obsolete `Residual_prefixStep` definition was removed.

The induction splits replay immediately before its last direction. Successful
`goodStep` checks preserve distinct unoriented bonds, forbid the centre, and
enforce the designated first direction. Replay rejects the target at every
vertex, including the final one, so a target hit cannot enter the surviving
frontier. The step theorem transports the complete `PrefixRepresents`
invariant, including phase numerators, base weight, and chronological reward
items. The empty replay state supplies the base case.

The retained helper proves its decoder append identity directly, so
`CodeDecodeLeaf` is not needed as an additional dependency. No whole-certificate
normalization, native computation, or additional reward-order argument is used.

## Exported declarations and statements

All declarations below are in namespace `AKLT.W.H3C029`. Names in the signatures
use the same open namespaces as the source files.

```lean
theorem main : CertData.H3.Bridge.PrefixReplaySoundLeaf

theorem main_of_prefixStep (hstep : PrefixStepLeaf) :
    CertData.H3.Bridge.PrefixReplaySoundLeaf

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
    (E : Exact) (hE : ExactValid E) (X : PairType) (d₀ : Fin 4)
    (n c : Nat) (hc : c < 4 ^ n) (s : PrefixState)
    (hs : replayPrefix E X d₀.val n c initial = some s) :
    PrefixRepresents E (decodeWord n c) s ∧
    IsTrail kernelStart kernelIncoming (decodeWord n c) ∧
    (0 < n → FirstDirection (decodeWord n c) (direction d₀.val)) ∧
    ∀ j ≤ n, wordVertex kernelStart (decodeWord n c) j ≠ kernelCentre ∧
      wordVertex kernelStart (decodeWord n c) j ≠ kernelTarget X
```

## Axiom checks

The build reports the following `#print axioms` output for every exported
theorem in the delivered files:

```text
'AKLT.W.H3C029.trail_append_of_goodStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.replayPrefix_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.transition_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.initial_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.replay_sound_of_prefixStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.main_of_prefixStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C029.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The imported `AKLT.W.H3C031.main` also reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Build and timing

Executed from `/home/ubuntu/aklt/wt/LW_H3C029`:

```bash
export PATH="$HOME/.elan/bin:$PATH"
/usr/bin/time -f '\nELAPSED=%e seconds\nMAX_RSS=%M KB\nEXIT=%x' lake build AKLT.W.H3C029.Main
```

- Result: `Build completed successfully (8977 jobs).`
- Exit code: `0`.
- Wall time: `27.33 seconds`.
- Lake module timings: dependency `H3C031.Accounting` 11 seconds;
  dependency `H3C031.Main` 6.9 seconds; target `H3C029.Main` 3.5 seconds.
- The retained `H3C029.Replay` was replayed from the existing build cache.
- Only dependency linter warnings appeared; no proof errors.

## Open issues

None. The required theorem has exactly the requested name and type and has no
residual premises.

## ORCH-SUMMARY

- Delivered `AKLT/W/H3C029/Main.lean` and retained helper `Replay.lean`.
- Required theorem: `AKLT.W.H3C029.main : CertData.H3.Bridge.PrefixReplaySoundLeaf`.
- Status: PROVED FROM DEPS.
- Indexed dependency: `AKLT.W.H3C031.main : CertData.H3.Bridge.PrefixStepLeaf`.
- Reused the earlier replay induction and discharged its sole remaining premise.
- No open leaves or residuals remain.
- Decoder append identity is proved locally; no CodeDecodeLeaf dependency is required.
- All exported theorems use only propext, Classical.choice, and Quot.sound.
- Build succeeded in 27.33 seconds; exit code 0.
- No sub-agents were used, as required by the leaf writer brief.
- No certificate normalization or frozen-file changes.
- No orchestrator decision or further proof work is required.
