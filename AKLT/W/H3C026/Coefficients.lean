import AKLT.W.H3C026.Arithmetic
import AKLT.W.H3C026.Translation

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3

namespace AKLT.W.H3C026

def deadSite (x : Plane) (j : Nat) : Prop :=
  if j < 4 then x = -(direction j).step else ∀ d : Compass, x ≠ -d.step

instance (x : Plane) (j : Nat) : Decidable (deadSite x j) := by
  unfold deadSite
  infer_instance

theorem compass_forall (p : Compass → Prop) :
    (∀ d, p d) ↔ p .east ∧ p .north ∧ p .west ∧ p .south := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _⟩
  · rintro ⟨h₀,h₁,h₂,h₃⟩ d; cases d <;> assumption

theorem response_sum (x : Plane) (ain d : Compass) (hr : d ≠ ain.reverse) (v : Nat) :
    ((List.range 5).map fun j => response (directionCode ain) (directionCode d) j *
      (if deadSite x j then v else 0)).sum =
      coefficientCeiling (passageFactor (decide (d=ain)) *
        relaxedReward x ain d {kernelCentre} / 3) * v := by
  by_cases h₀ : x = -Compass.east.step
  · subst x
    simpa [deadSite, List.range_succ, direction, Compass.step, compass_forall]
      using congrArg (fun n => n*v) (near_response_ceiling ain d ⟨0, by decide⟩ hr).symm
  by_cases h₁ : x = -Compass.north.step
  · subst x
    simpa [deadSite, List.range_succ, direction, Compass.step, compass_forall]
      using congrArg (fun n => n*v) (near_response_ceiling ain d ⟨1, by decide⟩ hr).symm
  by_cases h₂ : x = -Compass.west.step
  · subst x
    simpa [deadSite, List.range_succ, direction, Compass.step, compass_forall]
      using congrArg (fun n => n*v) (near_response_ceiling ain d ⟨2, by decide⟩ hr).symm
  by_cases h₃ : x = -Compass.south.step
  · subst x
    simpa [deadSite, List.range_succ, direction, Compass.step, compass_forall]
      using congrArg (fun n => n*v) (near_response_ceiling ain d ⟨3, by decide⟩ hr).symm
  have hf : ∀ e : Compass, x ≠ -e.step := by
    intro e; cases e <;> assumption
  rw [relaxedReward_far x ain d hf, far_response_ceiling ain d hr]
  simp [deadSite, List.range_succ, direction, hf, h₀, h₁, h₂, h₃]

private theorem phase_univ : (Finset.univ : Finset Phase) = {.A,.B,.C,.D} := rfl

theorem phase_sum (k : StepKind) (r : ℚ) (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (phaseTransition k r φ ψ) * v ψ) =
      diagonal φ k * v φ +
      if (φ = .A ∧ k = .turn) ∨ (φ = .B ∧ k = .straight) then
        coefficientCeiling (passageFactor (decide (k=.straight)) * r / 3) *
          v (if k=.turn then .C else .D) else 0 := by
  cases φ <;> cases k <;>
    simp [phase_univ, phaseTransition, diagonal_ceiling, zero_ceiling]

theorem known_phase_sum (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (if φ = ψ then (1 : ℚ)/5 else 0) * v ψ) =
      q5 * v φ := by
  have hf : coefficientCeiling (5⁻¹ : ℚ) = q5 := by
    simpa only [one_div] using fifth_ceiling
  cases φ <;> simp [phase_univ, hf, zero_ceiling]

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.compass_forall
#print axioms AKLT.W.H3C026.response_sum
#print axioms AKLT.W.H3C026.phase_sum
#print axioms AKLT.W.H3C026.known_phase_sum
