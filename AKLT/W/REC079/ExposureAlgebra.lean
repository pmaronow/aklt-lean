import AKLT.W.REC079.KernelAlgebra
import AKLT.W.REC046.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC079

theorem passageFactor_one_le (straight : Bool) : (1 : ℝ) ≤ (passageFactor straight : ℝ) := by
  cases straight <;> norm_num [passageFactor, localThreshold]

theorem list_product_unit_bounds {ι : Type*} (c : ι → ℝ)
    (hc : ∀ i, 0 < c i ∧ c i ≤ 1) (l : List ι) :
    0 < (l.map c).prod ∧ (l.map c).prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact ⟨mul_pos (hc i).1 ih.1,
      (mul_le_mul_of_nonneg_left ih.2 (le_of_lt (hc i).1)).trans (by simpa using (hc i).2)⟩

/-- A list version of ordered exposure. Repetition is harmless here; the
application uses one permutation of all departure indices. -/
theorem products_le_realExposure {n : ℕ} (w : DirectionWord n)
    (b c r : Fin n → ℝ)
    (h : ∀ i, 0 < b i ∧ 0 < c i ∧ c i ≤ 1 ∧
      b i ≤ (passageFactor (wordStraight kernelIncoming w i) : ℝ) ∧
      |Real.log (c i) - Real.log (b i)| ≤ r i)
    (hr : ∀ i, 0 ≤ r i) (l : List (Fin n)) :
    |(l.map b).prod - (l.map c).prod| ≤ realExposure w r l := by
  induction l with
  | nil => simp [realExposure]
  | cons i l ih =>
    let x : ℝ := passageFactor (wordStraight kernelIncoming w i)
    have hx : 1 ≤ x := passageFactor_one_le _
    have hscalar := AKLT.W.REC046.main 1 (fun _ => b i) (fun _ => c i) (fun _ => x)
      (fun _ => ⟨(h i).1, (h i).2.1, (h i).2.2.1, (h i).2.2.2.1, hx⟩)
    have hs : |b i - c i| ≤ x * |Real.log (c i) - Real.log (b i)| := by
      simpa [Fin.sum_univ_one, Fin.prod_univ_one, mul_comm] using hscalar
    have hs' : |b i - c i| ≤ x * r i :=
      hs.trans (mul_le_mul_of_nonneg_left (h i).2.2.2.2 (by linarith))
    have hc := list_product_unit_bounds c (fun j => ⟨(h j).2.1, (h j).2.2.1⟩) l
    have he := realExposure_nonneg w r hr l
    have hd : b i * (l.map b).prod - c i * (l.map c).prod =
        (b i - c i) * (l.map c).prod + b i * ((l.map b).prod - (l.map c).prod) := by ring
    simp only [List.map_cons, List.prod_cons, realExposure]
    calc
      |b i * (l.map b).prod - c i * (l.map c).prod| ≤
          |b i - c i| * (l.map c).prod + b i * |(l.map b).prod - (l.map c).prod| := by
        rw [hd]
        simpa only [abs_mul, abs_of_pos hc.1, abs_of_pos (h i).1] using
          abs_add_le ((b i - c i) * (l.map c).prod)
            (b i * ((l.map b).prod - (l.map c).prod))
      _ ≤ x * r i + x * realExposure w r l := add_le_add
        ((mul_le_of_le_one_right (abs_nonneg _) hc.2).trans hs')
        (mul_le_mul (h i).2.2.2.1 ih (abs_nonneg _) (by linarith))
      _ = _ := by dsimp only [x]; ring

/-- Append the remaining revisit indices after the prescribed kernel order.
This leaves every retained prefix in that order unchanged. -/
def fullOrdering {n : ℕ} (w : DirectionWord n) : List (Fin n) :=
  kernelOrdering w ++ (List.finRange n).filter (wordRevisit kernelStart w)

theorem fullOrdering_perm {n : ℕ} (w : DirectionWord n)
    (hk : (kernelOrdering w).Perm (firstVisitList w)) :
    (fullOrdering w).Perm (List.finRange n) := by
  unfold fullOrdering
  apply (hk.append_right _).trans
  simpa only [firstVisitList, Bool.not_not] using
    List.filter_append_perm (fun i => !wordRevisit kernelStart w i) (List.finRange n)

theorem realExposure_append {n : ℕ} (w : DirectionWord n) (r : Fin n → ℝ)
    (l t : List (Fin n)) (ht : realExposure w r t = 0) :
    realExposure w r (l ++ t) = realExposure w r l := by
  induction l with
  | nil => simpa only [List.nil_append, realExposure] using ht
  | cons i l ih => simp only [List.cons_append, realExposure, ih]

theorem realExposure_zero {n : ℕ} (w : DirectionWord n) (r : Fin n → ℝ)
    (l : List (Fin n)) (hl : ∀ i ∈ l, r i = 0) : realExposure w r l = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [realExposure, hl i (by simp), ih (fun j hj => hl j (by simp [hj])),
      add_zero, mul_zero]

end AKLT.W.REC079
