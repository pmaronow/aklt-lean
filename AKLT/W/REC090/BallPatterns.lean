import AKLT.W.REC090.Slots

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC090

/-- The frozen pattern functional with ball fields in place of unit fields. -/
def patternBallFunctional (π : PatternData) (next : Bool) (b : Fin 20 → Vec3)
    (f : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : π.active → SpinLetter,
    (∏ x : π.active,
      spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (n x)) *
    f (π.spins n) *
    (∏ e ∈ π.bonds,
      if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
      else 1 + dot (π.spins n e.1) (π.spins n e.2)) *
    ∏ j : Fin 20,
      if π.statusAt (externalSlot j).1 = .X then 1
      else 1 + dot (b j) (π.spins n (externalSlot j).1)

theorem patternBallFunctional_unit (π : PatternData) (next : Bool)
    (m : Fin 20 → UnitVector) (f : (Plane → Vec3) → ℝ) :
    patternBallFunctional π next (fun j => (m j).val) f = patternFunctional π next m f := rfl

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The same unit-field mixture represents every observable and both current
and next functionals. In particular all removed slots are harmless. -/
theorem patternBallFunctional_mixture (π : PatternData) (b : Fin 20 → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) :
    ∃ m : (Fin 20 → Bool) → Fin 20 → UnitVector,
    ∃ weight : (Fin 20 → Bool) → ℝ,
      (∀ σ, 0 ≤ weight σ) ∧ (∑ σ, weight σ) = 1 ∧
      ∀ next f, patternBallFunctional π next b f =
        ∑ σ, weight σ * patternFunctional π next (m σ) f := by
  classical
  obtain ⟨m, weight, hw, hwsum, hslots⟩ := ball_slots_mixture b hb
  refine ⟨m, weight, hw, hwsum, ?_⟩
  have hprod (n : π.active → SpinLetter) :
      (∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1
        else 1 + dot (b j) (π.spins n (externalSlot j).1)) =
      ∑ σ, weight σ * ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1
        else 1 + dot (m σ j).val (π.spins n (externalSlot j).1) := by
    let ns : Fin 20 → Vec3 := fun j =>
      if π.statusAt (externalSlot j).1 = .X then 0 else π.spins n (externalSlot j).1
    have heq (a : Fin 20 → Vec3) :
        (∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1
          else 1 + dot (a j) (π.spins n (externalSlot j).1)) =
        ∏ j : Fin 20, (1 + dot (ns j) (a j)) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hx : π.statusAt (externalSlot j).1 = .X
      · simp [ns, hx, dot]
      · simp only [hx, ite_false, ns]
        rw [dot_comm]
    rw [heq b, hslots ns]
    apply Finset.sum_congr rfl
    intro σ _
    rw [heq (fun j => (m σ j).val)]
  intro next f
  unfold patternBallFunctional patternFunctional
  simp_rw [hprod, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- H1 is stable under arbitrary missing factors and ball-valued slots. -/
theorem h1_ball_pattern_bound (hH1 : AKLT.Blueprint.Top.H1Statement)
    (π : PatternData) (hπ : π.Covered) (b : Fin 20 → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) :
    (if π.outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) *
      patternBallFunctional π true b (fun _ => 1) ≤
      patternBallFunctional π false b (fun _ => 1) := by
  obtain ⟨m, w, hw, _, hrep⟩ := patternBallFunctional_mixture π b hb
  rw [hrep true, hrep false, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hi := mul_le_mul_of_nonneg_left (hH1.2.2.2.2 π hπ (m σ)) (hw σ)
  simpa only [patternNext, patternCurrent, mul_left_comm] using hi

end AKLT.W.REC090
