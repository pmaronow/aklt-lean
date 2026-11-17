STATUS: PROVED FROM DEPS

## Files

- `AKLT/W/H3C028/Main.lean`: exact requested theorem, with no residual assumptions.
- `AKLT/W/H3C028/Audit.lean`: checks the requested type and prints axioms for all public theorems in this task directory.
- `AKLT/W/H3C028/Coefficients.lean` and `FreeRow.lean`: retained, unchanged helpers from the earlier attempt; audited but not imported by `Main.lean`.
- `/home/ubuntu/aklt/reports/LW/H3C028/audit-build.log`: complete successful audit build output.
- The earlier report remains in `report.luna.md`.

## Exported declarations

The final main module exports exactly these public theorems:

```lean
theorem AKLT.W.H3C028.main : CertData.H3.Bridge.PlaneSoundLeaf
theorem AKLT.W.H3C028.tableBoundsLeaf : CertData.H3.Bridge.TableBoundsLeaf
```

The retained helper modules export the following statements, all in namespace `AKLT.W.H3C028`:

```lean
theorem compass_univ : (Finset.univ : Finset Compass) =
    {.east, .north, .west, .south}

theorem phase_univ : (Finset.univ : Finset Phase) = {.A, .B, .C, .D}

theorem powersetCard_two_singleton (x : Plane) :
    Finset.powersetCard 2 {x} = ∅

theorem diagonal_eq (φ : Phase) (k : StepKind) :
    diagonal φ k = coefficientCeiling (phaseDiagonal φ k)

theorem response_free (ain d : Compass) (hd : d ≠ ain.reverse) :
    coefficientCeiling (passageFactor (decide (d = ain)) *
      relaxedReward (0,0) ain d ∅ / 3) = response (directionCode ain) (directionCode d) 4

theorem ceiling_zero : coefficientCeiling 0 = 0

theorem transition_row (ain d : Compass) (k : StepKind) (φ : Phase) (z : Phase → Nat)
    (hs : k = .straight → d = ain) (ht : k = .turn → d ≠ ain)
    (hr : k ≠ .revisit → d ≠ ain.reverse) :
    diagonal φ k * z φ +
      (if (φ = .A ∧ k = .turn) ∨ (φ = .B ∧ k = .straight) then
        response (directionCode ain) (directionCode d) 4 * z (if k = .turn then .C else .D)
        else 0) =
      ∑ ψ : Phase, coefficientCeiling (phaseTransition k (relaxedReward (0,0) ain d ∅) φ ψ) * z ψ

theorem quotient_kind {m q : Nat} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (a : Fin q) (d : Compass) (ha : Q.allowed a d = true) :
    (Q.kind a d = .straight → d = Q.arrival a) ∧
    (Q.kind a d = .turn → d ≠ Q.arrival a) ∧
    (Q.kind a d ≠ .revisit → d ≠ (Q.arrival a).reverse)

theorem freeRowLeaf : CertData.H3.Bridge.FreeRowLeaf
```

## Proof and dependencies

The final theorem reuses the existing composition proof and closes its former residual obligations with indexed proved leaves:

- `AKLT.W.H3C027.main : CertData.H3.Bridge.FreeRowLeaf` identifies the checked integer free row with the exact coefficient-ceiling sum.
- `AKLT.W.H3C026.main : CertData.H3.Bridge.RowTermsV2Leaf` identifies the packed local row with the `stationaryCoefficientV2` sum. Its proof uses the checked zero-centre condition supplied by `TableBounds T` and the proved centre-zero bridge.
- `tableBoundsLeaf` reexports `AKLT.W.H3C025.main`. The frozen `PlaneSoundLeaf` already supplies `TableBounds T` as a premise, which the main proof passes to the row identity.

The proof extracts the Boolean check's clauses, proves the finite-square index bounds and inverse indexing, applies the existing generic `packedRowCheck_sound` and `localRowCheck_sound`, and assembles every clause of `PlaneSpec`. The checked centre value remains zero, and the terminal value uses the phase's exact rational reward. It does not normalize a whole certificate.

## Axiom audit

The audit checks the exact declaration:

```text
AKLT.W.H3C028.main : CertData.H3.Bridge.PlaneSoundLeaf
```

Actual `#print axioms` output for every public theorem:

```text
AKLT/W/H3C028/Audit.lean:12:0: 'AKLT.W.H3C028.compass_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:13:0: 'AKLT.W.H3C028.phase_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:14:0: 'AKLT.W.H3C028.powersetCard_two_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:15:0: 'AKLT.W.H3C028.diagonal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:16:0: 'AKLT.W.H3C028.response_free' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:17:0: 'AKLT.W.H3C028.ceiling_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:18:0: 'AKLT.W.H3C028.transition_row' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:19:0: 'AKLT.W.H3C028.quotient_kind' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:20:0: 'AKLT.W.H3C028.freeRowLeaf' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:21:0: 'AKLT.W.H3C028.tableBoundsLeaf' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/H3C028/Audit.lean:23:0: 'AKLT.W.H3C028.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three permitted axioms occur. The task directory contains no forbidden proof placeholders, native decision procedures, or unsafe declarations.

## Build commands and timings

With `$HOME/.elan/bin` prepended to `PATH`:

- `lake build AKLT.W.H3C028.Main` succeeded: **82.28 s wall time**, including rebuilding available H3C026/H3C027 dependency modules; the main module took **4.6 s**.
- `lake build AKLT.W.H3C028.Audit` succeeded: **10.76 s wall time**; the audit module took **3.2 s**. The full output is saved in `audit-build.log`.

There were no errors. Existing imported modules emitted linter/deprecation warnings. No frozen statement or other task's source file was edited.

## Open issues

None. The requested theorem has the exact name and type and has no additional hypotheses beyond the frozen closed proposition. The former `Residual_RowTermsV2` definition and conditional composition theorem have been replaced by the proved `main`.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C028.main : CertData.H3.Bridge.PlaneSoundLeaf` in `AKLT/W/H3C028/Main.lean`.
- Status: PROVED FROM DEPS, using indexed H3C026 and H3C027; H3C025 is reexported.
- The final main module does not import the earlier local coefficient/free-row helpers.
- V2 local rows retain the checked zero-centre condition.
- Both required-module and audit builds succeeded.
- Every public theorem's axioms are `[propext, Classical.choice, Quot.sound]`.
- Open exact names: none. Residual leaves: none.
- Limitations/deviations: none; no sub-agents or frozen-source edits.
- Orchestrator action: accept the completed leaf and index `AKLT.W.H3C028.main` from module `AKLT.W.H3C028.Main`.
