STATUS: PROVED FROM DEPS

## Files

- `AKLT/W/REC044/Main.lean`: completed proof, retaining the earlier first-hit lemmas and conditional reductions.
- `AKLT/W/REC044/Audit.lean`: exact-type check and signatures/axioms checks for every exported theorem.
- `/home/ubuntu/aklt/reports/LW/REC044/audit.txt`: complete output of the audit.
- `/home/ubuntu/aklt/reports/LW/REC044/audit-time.txt`: measured audit timing.

## Delivered theorem

```lean
theorem AKLT.W.REC044.main : AKLT.Blueprint.Rec.PairTerminalFactorStatement
```

This is unconditional and has exactly the requested name and type. `Audit.lean` checks it with:

```lean
example : AKLT.Blueprint.Rec.PairTerminalFactorStatement := AKLT.W.REC044.main
```

At the first target arrival the status is unchanged. A U target has squared norm one on its positive-weight support. A D target loses its only possible present bond at arrival and has no original pin legs, so all interaction factors are independent of its spin. Finite Fubini then gives the unnormalized numerator as `3 / 5` times the partition. The positive partition normalizer is canceled only at the end.

## Dependencies and completed residuals

Imports of proved leaves are limited to modules listed in the supplied proved index:

- `AKLT.W.REC003.Main` (`TwoFactorizationStatement`): reuse its proved finite-sum support lemmas, principally `partition_repr`, `spinIntegral_site`, and `site_mul_const`. The two-factorization leaf itself is not needed as an assumption.
- `AKLT.W.REC014.Main` (`OneStepTrivialStatement`): reuse `partition_positive`, which proves positivity for every network and both pin choices. The one-step leaf itself is not needed as an assumption.

The original `AKLT.Blueprint.Mom.Assembly` import supplies the already proved site-law decomposition and constant moment identities.

All four closed `Residual_* : Prop` definitions retained from the earlier attempt are now proved:

| Closed proposition | Unconditional proof |
| --- | --- |
| `Residual_FirstHitStatus` | `firstHitStatus` |
| `Residual_FirstHitIsolation` | `firstHitIsolation` |
| `Residual_IsolatedSiteLaw` | `isolatedSiteLaw` |
| `Residual_TracePartitionPositive` | `tracePartitionPositive` |

Every name in this table is in namespace `AKLT.W.REC044`. The two former open residuals are fully discharged; `main` has no residual parameters.

## Validation

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC044.Main` succeeded. The completed Main module compiled in 6.7 seconds; a timed repeat of the full command took 6.43 seconds wall time.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/REC044/Audit.lean` succeeded, including the exact-type check; wall time 4.43 seconds.
- All 26 exported theorems report exactly the allowed axioms `[propext, Classical.choice, Quot.sound]`.
- The delivered Lean files contain none of the forbidden proof escapes. No frozen statement or file outside the assigned directory was changed.

## Exported theorem signatures and complete axioms output

The following is the complete `Audit.lean` output. It records every exported theorem's statement, including the earlier support lemmas and conditional reductions.

```text
AKLT.W.REC044.icoVector_normSq_one : ∀ (j : AKLT.Defs.IcoLetter), AKLT.Defs.normSq (AKLT.Defs.icoVector j) = 1
'AKLT.W.REC044.icoVector_normSq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.dSite_normSq : AKLT.Defs.siteFunctional AKLT.Defs.Status.D AKLT.Defs.normSq = 3 / 5
'AKLT.W.REC044.dSite_normSq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.dSite_mass : (AKLT.Defs.siteFunctional AKLT.Defs.Status.D fun x => 1) = 1
'AKLT.W.REC044.dSite_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.traceStep_present_mono : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (a b x y : AKLT.Defs.Plane), (AKLT.Defs.traceStep D a b).Present x y → D.Present x y
'AKLT.W.REC044.traceStep_present_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.traceNetwork_present_mono : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane) {x y : AKLT.Defs.Plane}, (AKLT.Defs.traceNetwork D l).Present x y → D.Present x y
'AKLT.W.REC044.traceNetwork_present_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.traceStep_no_traced_bond : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (a b : AKLT.Defs.Plane), ¬(AKLT.Defs.traceStep D a b).Present a b ∧ ¬(AKLT.Defs.traceStep D a b).Present b a
'AKLT.W.REC044.traceStep_no_traced_bond' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.traceNetwork_no_traced_bond : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (pre : List AKLT.Defs.Plane) (a b : AKLT.Defs.Plane) (suf : List AKLT.Defs.Plane),
  ¬(AKLT.Defs.traceNetwork D (pre ++ a :: b :: suf)).Present a b ∧
    ¬(AKLT.Defs.traceNetwork D (pre ++ a :: b :: suf)).Present b a
'AKLT.W.REC044.traceNetwork_no_traced_bond' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.traceNetwork_status_of_not_mem_dropLast : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G)
  (l : List AKLT.Defs.Plane), ∀ x ∉ l.dropLast, (AKLT.Defs.traceNetwork D l).status x = D.status x
'AKLT.W.REC044.traceNetwork_status_of_not_mem_dropLast' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.wordVertex_mem_of_mem_dropLast : ∀ {n : ℕ} (u : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n)
  {x : AKLT.Defs.Plane}, x ∈ (AKLT.Defs.wordVertices u w).dropLast → ∃ j < n, AKLT.Defs.wordVertex u w j = x
'AKLT.W.REC044.wordVertex_mem_of_mem_dropLast' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.wordVertices_split_terminal : ∀ {n : ℕ} (u v : AKLT.Defs.Plane) (w : AKLT.Defs.DirectionWord n),
  0 < n →
    AKLT.Defs.wordVertex u w n = v →
      AKLT.Defs.wordVertices u w =
        List.map (AKLT.Defs.wordVertex u w) (List.range (n - 1)) ++ [AKLT.Defs.wordVertex u w (n - 1), v]
'AKLT.W.REC044.wordVertices_split_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.network_present_symm : ∀ {G : Finset AKLT.Defs.Plane} (D : AKLT.Defs.Network G) {x y : AKLT.Defs.Plane},
  D.Present x y → D.Present y x
'AKLT.W.REC044.network_present_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.adjacent_mem_neighbours : ∀ {x y : AKLT.Defs.Plane}, AKLT.Defs.Adjacent x y → y ∈ AKLT.Defs.neighbours x
'AKLT.W.REC044.adjacent_mem_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.originalLeg_root_is_protected : ∀ {G : Finset AKLT.Defs.Plane} {x z : AKLT.Defs.Plane},
  x ∈ G → (x, z) ∈ AKLT.Defs.originalLegs G → x ∈ AKLT.Defs.protectedSites G
'AKLT.W.REC044.originalLeg_root_is_protected' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.firstHitStatus : AKLT.W.REC044.Residual_FirstHitStatus
'AKLT.W.REC044.firstHitStatus' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.firstHit_D_no_neighbours : ∀ (G : Finset AKLT.Defs.Plane) (D : AKLT.Defs.Network G),
  D.Auxiliary →
    ∀ (u v : AKLT.Defs.Plane),
      D.AdmissibleStart u →
        AKLT.Defs.AdmissibleTarget D v →
          u ≠ v →
            ∀ (n : ℕ) (w : AKLT.Defs.DirectionWord n),
              AKLT.Defs.StoppedNetworkTrail D u (insert v (AKLT.Defs.protectedSites G)) w →
                AKLT.Defs.wordVertex u w n = v →
                  D.status v = AKLT.Defs.Status.D →
                    (AKLT.Defs.traceNetwork D (AKLT.Defs.wordVertices u w)).presentNeighbours v = ∅
'AKLT.W.REC044.firstHit_D_no_neighbours' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.firstHit_D_no_original_legs : ∀ (G : Finset AKLT.Defs.Plane) (D : AKLT.Defs.Network G),
  D.Auxiliary →
    ∀ (u v : AKLT.Defs.Plane),
      D.AdmissibleStart u →
        AKLT.Defs.AdmissibleTarget D v →
          u ≠ v →
            ∀ (n : ℕ) (w : AKLT.Defs.DirectionWord n),
              AKLT.Defs.StoppedNetworkTrail D u (insert v (AKLT.Defs.protectedSites G)) w →
                AKLT.Defs.wordVertex u w n = v →
                  D.status v = AKLT.Defs.Status.D → ∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ v
'AKLT.W.REC044.firstHit_D_no_original_legs' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.firstHitIsolation : AKLT.W.REC044.Residual_FirstHitIsolation
'AKLT.W.REC044.firstHitIsolation' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.main_of_residuals : AKLT.W.REC044.Residual_FirstHitStatus →
  AKLT.W.REC044.Residual_FirstHitIsolation →
    AKLT.W.REC044.Residual_IsolatedSiteLaw →
      AKLT.W.REC044.Residual_TracePartitionPositive → AKLT.Blueprint.Rec.PairTerminalFactorStatement
'AKLT.W.REC044.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.main_of_core_residuals : AKLT.W.REC044.Residual_IsolatedSiteLaw →
  AKLT.W.REC044.Residual_TracePartitionPositive → AKLT.Blueprint.Rec.PairTerminalFactorStatement
'AKLT.W.REC044.main_of_core_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.uSite_normSq_mul : ∀ (f : AKLT.Defs.Vec3 → ℝ),
  (AKLT.Defs.siteFunctional AKLT.Defs.Status.U fun z => AKLT.Defs.normSq z * f z) =
    AKLT.Defs.siteFunctional AKLT.Defs.Status.U f
'AKLT.W.REC044.uSite_normSq_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.partition_normSq_U : ∀ {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool),
  ∀ v ∈ E.active,
    E.status v = AKLT.Defs.Status.U → (E.partition τ b fun a => AKLT.Defs.normSq (a v)) = E.partition τ b fun x => 1
'AKLT.W.REC044.partition_normSq_U' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.interaction_update_isolated : ∀ {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool) (v : AKLT.Defs.Plane),
  E.presentNeighbours v = ∅ →
    (∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ v) →
      ∀ (m : AKLT.Defs.Plane → AKLT.Defs.Vec3) (z : AKLT.Defs.Vec3),
        AKLT.W.REC003.interaction E τ b (Function.update m v z) = AKLT.W.REC003.interaction E τ b m
'AKLT.W.REC044.interaction_update_isolated' depends on axioms: [propext, Classical.choice, Quot.sound]
@AKLT.W.REC044.partition_normSq_D : ∀ {G : Finset AKLT.Defs.Plane} (E : AKLT.Defs.Network G)
  (τ : AKLT.Defs.PinAssignment G) (b : Bool),
  ∀ v ∈ E.active,
    E.status v = AKLT.Defs.Status.D →
      E.presentNeighbours v = ∅ →
        (∀ e ∈ AKLT.Defs.originalLegs G, e.1 ≠ v) →
          (E.partition τ b fun a => AKLT.Defs.normSq (a v)) = 3 / 5 * E.partition τ b fun x => 1
'AKLT.W.REC044.partition_normSq_D' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.isolatedSiteLaw : AKLT.W.REC044.Residual_IsolatedSiteLaw
'AKLT.W.REC044.isolatedSiteLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.tracePartitionPositive : AKLT.W.REC044.Residual_TracePartitionPositive
'AKLT.W.REC044.tracePartitionPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.REC044.main : AKLT.Blueprint.Rec.PairTerminalFactorStatement
'AKLT.W.REC044.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC044.main : AKLT.Blueprint.Rec.PairTerminalFactorStatement`.
- The exact requested type checks and `lake build AKLT.W.REC044.Main` succeeds.
- Reused earlier first-hit status, bond deletion, and D-target isolation proofs.
- Proved U-site and isolated D-site unnormalized squared-norm identities.
- Discharged `Residual_IsolatedSiteLaw` and `Residual_TracePartitionPositive`.
- Reused finite-sum support from indexed REC003 and partition positivity from indexed REC014.
- All exported theorem axioms are `[propext, Classical.choice, Quot.sound]`.
- No open leaves, residual obligations, limitations, or required orchestrator decisions.
- No frozen files changed; all Lean work is under `AKLT/W/REC044/`.
