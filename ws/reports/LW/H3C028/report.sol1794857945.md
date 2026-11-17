STATUS: PARTIAL

## Delivered files

- `AKLT/W/H3C028/Main.lean`: assembly of the exact target from one closed residual.
- `AKLT/W/H3C028/FreeRow.lean`: unconditional proof of `CertData.H3.Bridge.FreeRowLeaf`.
- `AKLT/W/H3C028/Coefficients.lean`: exact diagonal and free-response ceilings, phase-row identity, and consequences of quotient correctness.
- `AKLT/W/H3C028/Audit.lean`: type checks for the proved leaves and reduction, and axiom checks for every exported theorem.
- `build.log`, `audit.log` in this report directory: successful final build and audit output.

The requested declaration `AKLT.W.H3C028.main : CertData.H3.Bridge.PlaneSoundLeaf` is **not proved or declared**. The earlier attempt's two residuals have been reduced to one by proving FreeRowLeaf. The remaining exact leaf is `CertData.H3.Bridge.RowTermsV2Leaf`, absent from the proved-leaf index at the final check.

## Main exported declarations

All new declarations below have namespace prefix `AKLT.W.H3C028`.

```lean
theorem freeRowLeaf : CertData.H3.Bridge.FreeRowLeaf

theorem tableBoundsLeaf : CertData.H3.Bridge.TableBoundsLeaf

def Residual_RowTermsV2 : Prop := CertData.H3.Bridge.RowTermsV2Leaf

theorem planeSoundLeaf_of_rowTermsV2
    (hRows : Residual_RowTermsV2) : CertData.H3.Bridge.PlaneSoundLeaf
```

`tableBoundsLeaf` reuses the indexed theorem `AKLT.W.H3C025.main`. The reduction uses `freeRowLeaf`, the generic `packedRowCheck_sound` and `localRowCheck_sound`, and elementary grid-index identities. It retains the checked zero at the centre and uses `stationaryCoefficientV2` in its spatial row. It does not identify the corrected coefficient with the legacy coefficient on the known-site centre edge.

Expanded, the newly proved free-row leaf is:

```lean
∀ (G : Graph) (T : Tables), G.quotient.Correct →
  ∀ (φ : Phase) (a : Fin 3741),
    freeRow G T (phaseCode φ) a.val =
      ∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (freeCoefficient G.quotient φ a d ψ) *
          T.capFn ψ (G.quotient.successor a d)
```

Its proof derives the nonrevisit direction/kind constraints from `MemoryQuotient.Correct`, checks the twelve admitted incoming/outgoing free-response coefficients by exact rational arithmetic, and then sums the four directions and phases. It never normalizes the certificate or any supplied plane.

## Helper exported declarations and statements

The notation and open namespaces here are those in `Coefficients.lean`.

```lean
theorem compass_univ :
  (Finset.univ : Finset Compass) = {.east, .north, .west, .south}

theorem phase_univ :
  (Finset.univ : Finset Phase) = {.A, .B, .C, .D}

theorem powersetCard_two_singleton (x : Plane) :
  Finset.powersetCard 2 {x} = ∅

theorem diagonal_eq (φ : Phase) (k : StepKind) :
  diagonal φ k = coefficientCeiling (phaseDiagonal φ k)

theorem response_free (ain d : Compass) (hd : d ≠ ain.reverse) :
  coefficientCeiling (passageFactor (decide (d = ain)) *
    relaxedReward (0,0) ain d ∅ / 3) =
      response (directionCode ain) (directionCode d) 4

theorem ceiling_zero : coefficientCeiling 0 = 0

theorem transition_row
    (ain d : Compass) (k : StepKind) (φ : Phase) (z : Phase → Nat)
    (hs : k = .straight → d = ain)
    (ht : k = .turn → d ≠ ain)
    (hr : k ≠ .revisit → d ≠ ain.reverse) :
  diagonal φ k * z φ +
    (if (φ = .A ∧ k = .turn) ∨ (φ = .B ∧ k = .straight) then
      response (directionCode ain) (directionCode d) 4 *
        z (if k = .turn then .C else .D)
      else 0) =
    ∑ ψ : Phase,
      coefficientCeiling
        (phaseTransition k (relaxedReward (0,0) ain d ∅) φ ψ) * z ψ

theorem quotient_kind {m q : Nat}
    (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (a : Fin q) (d : Compass) (ha : Q.allowed a d = true) :
  (Q.kind a d = .straight → d = Q.arrival a) ∧
  (Q.kind a d = .turn → d ≠ Q.arrival a) ∧
  (Q.kind a d ≠ .revisit → d ≠ (Q.arrival a).reverse)
```

## Residual and open issue

There is exactly one remaining transparent, closed residual:

```lean
def AKLT.W.H3C028.Residual_RowTermsV2 : Prop :=
  CertData.H3.Bridge.RowTermsV2Leaf
```

This is smaller than PlaneSoundLeaf: it asserts only the equality between a packed spatial row component and the corrected coefficient-ceiling sum, assuming quotient correctness, table bounds, and membership in the five stationary cases. It contains no checker soundness, free-row inequalities, terminal values, or value/cap inequalities.

What remains is the routed/masked spatial-row identification, including boundary pulls, ordinary/known/dead masks, spatial response coefficients, and the zero-centre deletion. The current reduction discharges every other PlaneSpec clause. Once this leaf is available as a proved theorem `h`, the exact requested declaration can be added as:

```lean
theorem AKLT.W.H3C028.main : CertData.H3.Bridge.PlaneSoundLeaf :=
  AKLT.W.H3C028.planeSoundLeaf_of_rowTermsV2 h
```

Here `h` is an explanatory placeholder in this report only; no placeholder proof occurs in delivered Lean files.

## Axiom audit

The successful `Audit.lean` output is:

```text
'AKLT.W.H3C028.compass_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.phase_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.powersetCard_two_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.diagonal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.response_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.ceiling_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.transition_row' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.quotient_kind' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.freeRowLeaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.tableBoundsLeaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C028.planeSoundLeaf_of_rowTermsV2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A source scan found none of the prohibited declarations or tactics. No sub-agents were used. No frozen source file was edited. There are two nonfatal tactic-style linter warnings in Coefficients.lean.

## Build commands and timings

Run with `PATH="$HOME/.elan/bin:$PATH"`:

- `lake build AKLT.W.H3C028.Coefficients` — succeeded; Lake target time 44 s.
- `lake build AKLT.W.H3C028.FreeRow` — succeeded; Lake target time 4.0 s.
- `lake build AKLT.W.H3C028.Main` — succeeded; measured wall time 40.07 s, target time 15 s. This also built the imported indexed H3C025 module (10 s).
- `lake env lean AKLT/W/H3C028/Audit.lean` — succeeded; measured wall time 14.01 s. Checks the exact closed FreeRowLeaf and TableBoundsLeaf types and the implication `RowTermsV2Leaf → PlaneSoundLeaf`.

## ORCH-SUMMARY

- Delivered four Lean files under AKLT/W/H3C028 and this report with build/audit logs.
- Newly proved: AKLT.W.H3C028.freeRowLeaf : CertData.H3.Bridge.FreeRowLeaf.
- Reused indexed dependency: AKLT.W.H3C025.main : CertData.H3.Bridge.TableBoundsLeaf.
- Delivered planeSoundLeaf_of_rowTermsV2 : Residual_RowTermsV2 → PlaneSoundLeaf.
- Only open residual: CertData.H3.Bridge.RowTermsV2Leaf.
- Exact requested AKLT.W.H3C028.main remains unproved and is not declared.
- Build and reduction/type audit passed.
- All exported theorem axioms: propext, Classical.choice, Quot.sound.
- Uses corrected stationaryCoefficientV2 and retains checked centre zero.
- No full-certificate normalization, prohibited tactics, sub-agents, or frozen-file edits.
- Two nonfatal tactic-style warnings remain in Coefficients.lean.
- Orchestrator: supply/prove RowTermsV2Leaf, then apply the delivered reduction.
