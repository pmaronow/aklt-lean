import AKLT.W.REC089.Basic

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

/-- The same twenty-slot polynomial, allowing ball fields and zero fields. -/
def ballPatternFunctional (π : PatternData) (next : Bool) (b : Fin 20 → Vec3) : ℝ :=
  ∑ n : (x : π.active) → SpinLetter,
    (∏ x : π.active,
      spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (n x)) *
    (∏ e ∈ π.bonds,
      if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
      else 1 + dot (π.spins n e.1) (π.spins n e.2)) *
    ∏ j : Fin 20,
      if π.statusAt (externalSlot j).1 = .X then 1
      else 1 + dot (b j) (π.spins n (externalSlot j).1)

def binaryCoefficient (t : ℝ) (q : Bool) : ℝ := if q then t else 1 - t
def binaryUnit (e : UnitVector) (q : Bool) : UnitVector := if q then e else negateUnit e

theorem binaryCoefficient_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (q : Bool) :
    0 ≤ binaryCoefficient t q := by
  cases q <;> simp [binaryCoefficient] <;> linarith

theorem binaryCoefficient_sum (t : ℝ) : ∑ q : Bool, binaryCoefficient t q = 1 := by
  simp [binaryCoefficient, Fintype.sum_bool]

/-- Finite distributivity with the coefficients separated from the factors. -/
theorem product_binary_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ι → ℝ) (f : ι → Bool → ℝ) :
    (∏ j, ∑ q : Bool, binaryCoefficient (t j) q * f j q) =
      ∑ η : ι → Bool, (∏ j, binaryCoefficient (t j) (η j)) * ∏ j, f j (η j) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro η _
  exact Finset.prod_mul_distrib

/-- Resolve every slot independently; the coefficients work for both passage laws. -/
theorem pattern_slots_mixture (π : PatternData) (b : Fin 20 → Vec3)
    (hb : ∀ j, normSq (b j) ≤ 1) :
    ∃ m : (Fin 20 → Bool) → Fin 20 → UnitVector,
      ∃ w : (Fin 20 → Bool) → ℝ,
      (∀ η, 0 ≤ w η) ∧ (∑ η, w η) = 1 ∧
      ∀ next : Bool, ballPatternFunctional π next b =
        ∑ η, w η * patternFunctional π next (m η) (fun _ => 1) := by
  classical
  choose e t ht0 ht1 he using fun j => ball_slot_split (b j) (hb j)
  let m : (Fin 20 → Bool) → Fin 20 → UnitVector := fun η j => binaryUnit (e j) (η j)
  let w : (Fin 20 → Bool) → ℝ := fun η => ∏ j, binaryCoefficient (t j) (η j)
  refine ⟨m, w, ?_, ?_, ?_⟩
  · intro η
    exact Finset.prod_nonneg fun j _ => binaryCoefficient_nonneg (ht0 j) (ht1 j) _
  · dsimp [w]
    rw [← Fintype.prod_sum]
    simp_rw [binaryCoefficient_sum]
    simp
  · intro next
    let K := fun n : (x : π.active) → SpinLetter =>
      (∏ x : π.active,
        spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (n x)) *
      (∏ edge ∈ π.bonds,
        if next ∧ ({edge.1, edge.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
        else 1 + dot (π.spins n edge.1) (π.spins n edge.2))
    let slot := fun (n : (x : π.active) → SpinLetter) (j : Fin 20) (q : Bool) =>
      if π.statusAt (externalSlot j).1 = .X then (1 : ℝ)
      else 1 + dot (binaryUnit (e j) q).val (π.spins n (externalSlot j).1)
    have hslot (n : (x : π.active) → SpinLetter) (j : Fin 20) :
        (if π.statusAt (externalSlot j).1 = .X then 1
          else 1 + dot (b j) (π.spins n (externalSlot j).1)) =
        ∑ q : Bool, binaryCoefficient (t j) q * slot n j q := by
      by_cases hx : π.statusAt (externalSlot j).1 = .X
      · simp [slot, hx, binaryCoefficient, Fintype.sum_bool]
      · simp only [slot, hx, ite_false, Fintype.sum_bool, binaryCoefficient, binaryUnit,
          Bool.false_eq_true, ite_false, ite_true, negateUnit]
        rw [dot_comm (b j), dot_comm (e j).val, dot_comm (-(e j).val)]
        exact he j (π.spins n (externalSlot j).1)
    change (∑ n, K n * ∏ j, _) = _
    simp_rw [hslot, product_binary_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    unfold patternFunctional
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    change K n * (w η * ∏ j, slot n j (η j)) =
      w η * ((∏ x : π.active,
        spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (n x)) * 1 *
        (∏ edge ∈ π.bonds,
          if next ∧ ({edge.1, edge.2} : Finset Plane) = {(0, 0), π.outgoing.step}
            then 1 else 1 + dot (π.spins n edge.1) (π.spins n edge.2)) *
        ∏ j, slot n j (η j))
    dsimp [K]
    ring

#print axioms product_binary_sum
#print axioms pattern_slots_mixture

end AKLT.W.REC089
