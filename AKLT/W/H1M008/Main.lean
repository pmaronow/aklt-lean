import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M008

private theorem dot_lower_bound {a b : Vec3}
    (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) : -1 ≤ dot a b := by
  have hterm (i : Fin 3) : -(a i * a i + b i * b i) ≤ 2 * (a i * b i) := by
    have h := sq_nonneg (a i + b i)
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  have hsum' : -(normSq a + normSq b) ≤ 2 * dot a b := by
    simpa [normSq, dot, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      ← Finset.mul_sum] using hsum
  nlinarith

private theorem ico_spin_norm_le_one
    (hUnit : ∀ j : IcoLetter, normSq (icoVector j) = 1) (j : SpinLetter) :
    normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (hUnit j)

private theorem support_spin_norm_le_one
    (hUnit : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (V : Finset Plane) (n : V → SpinLetter) (x : Plane) :
    normSq (supportSpins V n x) ≤ 1 := by
  by_cases hx : x ∈ V
  · simp [supportSpins, hx, ico_spin_norm_le_one hUnit]
  · simp [supportSpins, hx, normSq, dot]

private theorem spin_weight_nonneg (s : Status) (j : SpinLetter) :
    0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

private theorem without_passage_weight_nonneg (π : PatternData)
    (V : Finset Plane) (n : V → SpinLetter) :
    0 ≤ ∏ x : V, spinWeight (π.statusAt x.val) (n x) := by
  exact Finset.prod_nonneg (fun x _ => spin_weight_nonneg _ _)

private theorem without_passage_bonds_nonneg
    (hUnit : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (π : PatternData) (V : Finset Plane) (n : V → SpinLetter) :
    0 ≤ ∏ e ∈ π.bonds,
      if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1
      else 1 + dot (supportSpins V n e.1) (supportSpins V n e.2) := by
  apply Finset.prod_nonneg
  intro e he
  by_cases h0 : e.1 = (0, 0) ∨ e.2 = (0, 0)
  · simp [h0]
  · have hd := dot_lower_bound
      (support_spin_norm_le_one hUnit V n e.1)
      (support_spin_norm_le_one hUnit V n e.2)
    simp only [h0, ite_false]
    linarith

private theorem without_passage_pins_nonneg
    (hUnit : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (π : PatternData) (m : Fin 20 → UnitVector)
    (V : Finset Plane) (n : V → SpinLetter) :
    0 ≤ ∏ j : Fin 20,
      if π.statusAt (externalSlot j).1 = .X then 1 else
        1 + dot (m j).val (supportSpins V n (externalSlot j).1) := by
  apply Finset.prod_nonneg
  intro j hj
  by_cases hX : π.statusAt (externalSlot j).1 = .X
  · simp [hX]
  · have hd := dot_lower_bound (le_of_eq (m j).property)
      (support_spin_norm_le_one hUnit V n (externalSlot j).1)
    simp only [hX, ite_false]
    linarith

theorem main : AKLT.Blueprint.H1.PassageNextLowerBoundStatement := by
  intro hUnit π hCovered m f g
  classical
  unfold AKLT.Defs.withoutPassageFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  let V := π.active.erase (0, 0)
  let w := ∏ x : V, spinWeight (π.statusAt x.val) (n x)
  let B := ∏ e ∈ π.bonds,
    if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1
    else 1 + dot (supportSpins V n e.1) (supportSpins V n e.2)
  let P := ∏ j : Fin 20,
    if π.statusAt (externalSlot j).1 = .X then 1 else
      1 + dot (m j).val (supportSpins V n (externalSlot j).1)
  have hw : 0 ≤ w := by
    exact without_passage_weight_nonneg π V n
  have hB : 0 ≤ B := by
    exact without_passage_bonds_nonneg hUnit π V n
  have hP : 0 ≤ P := by
    exact without_passage_pins_nonneg hUnit π m V n
  have hJ : (4 / 5 : ℝ) ≤ AKLT.Blueprint.H1.passageJ f g (supportSpins V n) := by
    dsimp [AKLT.Blueprint.H1.passageJ]
    have hd := dot_lower_bound
      (support_spin_norm_le_one hUnit V n f)
      (support_spin_norm_le_one hUnit V n g)
    linarith
  have hbase : 0 ≤ w * (B * P) := mul_nonneg hw (mul_nonneg hB hP)
  have hterm : (4 / 5 : ℝ) * (w * B * P) ≤ w * AKLT.Blueprint.H1.passageJ f g (supportSpins V n) * B * P := by
    calc
      (4 / 5 : ℝ) * (w * B * P) = (4 / 5 : ℝ) * (w * (B * P)) := by ring
      _ ≤ AKLT.Blueprint.H1.passageJ f g (supportSpins V n) * (w * (B * P)) :=
        mul_le_mul_of_nonneg_right hJ hbase
      _ = w * AKLT.Blueprint.H1.passageJ f g (supportSpins V n) * B * P := by ring
  simpa only [V, w, B, P, Function.const_apply, one_mul, mul_one] using hterm

end AKLT.W.H1M008

#print axioms AKLT.W.H1M008.main
