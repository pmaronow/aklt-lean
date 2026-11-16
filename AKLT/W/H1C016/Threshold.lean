import AKLT.W.H1C016.Ring

namespace AKLT.W.H1C016

open AKLT.Cert.H1 AKLT.Cert.H1.Production
open scoped BigOperators

theorem gaussianL1_sum_map_le {α : Type} (xs : List α) (f : α → Gaussian) (B : Nat)
    (h : ∀ x ∈ xs, gaussianL1 (f x) ≤ B) :
    gaussianL1 (sumGaussian (xs.map f)) ≤ xs.length * B := by
  induction xs with
  | nil => simp only [List.map_nil, sumGaussian, gaussianL1_zero, List.length_nil, Nat.zero_mul, le_refl]
  | cons x xs ih =>
      simp only [List.map_cons, sumGaussian, List.length_cons]
      calc
        _ ≤ gaussianL1 (f x) + gaussianL1 (sumGaussian (xs.map f)) := gaussianL1_add_le _ _
        _ ≤ B + xs.length * B := Nat.add_le_add (h x List.mem_cons_self)
          (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))
        _ = (xs.length + 1) * B := by ring

theorem gaussianL1_sum_skip_le {α : Type} (xs : List α) (skip : α → Bool)
    (f : α → Gaussian) (B : Nat) (h : ∀ x ∈ xs, gaussianL1 (f x) ≤ B) :
    gaussianL1 (sumGaussian (xs.filterMap (fun x => if skip x then none else some (f x)))) ≤
      (xs.filter (fun x => !skip x)).length * B := by
  have he : xs.filterMap (fun x => if skip x then none else some (f x)) =
      (xs.filter (fun x => !skip x)).map f := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have iht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      cases hx : skip x <;> simp [hx, iht]
  rw [he]
  apply gaussianL1_sum_map_le
  intro x hx
  exact h x (List.mem_of_mem_filter hx)

theorem current_next_bound (ss : List SectorSite) (out row col B : Nat)
    (h : ∀ codes, gaussianL1 (directSectorRingValue ss row col codes) ≤ B) (next : Bool) :
    gaussianL1 (directSectorCurrentNext ss out row col next) ≤
      (if next then 5 else 3) * B +
      ((centerPairs (ss.map SectorSite.base)).filter (fun xy =>
        !(next && (xy.1 == out || xy.2 == out)))).length * (3*B) := by
  have hterms (xy : Nat × Nat) :
      gaussianL1 (sumGaussian ((List.range 3).map fun k =>
        directSectorRingValue ss row col (centerCodes ss.length xy.1 xy.2 (k+1)))) ≤ 3*B := by
    simpa only [List.length_range] using gaussianL1_sum_map_le (List.range 3)
      (fun k => directSectorRingValue ss row col (centerCodes ss.length xy.1 xy.2 (k+1)))
      B (fun _ _ => h _)
  have hscale : (if next then (5 : Int) else 3).natAbs = if next then 5 else 3 := by
    cases next <;> rfl
  unfold directSectorCurrentNext
  apply (gaussianL1_add_le _ _).trans
  apply Nat.add_le_add
  · rw [gaussianL1_scale, hscale]
    exact Nat.mul_le_mul_left _ (h [])
  · exact gaussianL1_sum_skip_le _ _ _ _ (fun xy _ => hterms xy)

theorem threshold_bound (ss : List SectorSite) (out p q row col B : Nat)
    (h : ∀ codes, gaussianL1 (directSectorRingValue ss row col codes) ≤ B)
    (hc : (centerPairs (ss.map SectorSite.base)).length ≤ 3)
    (hn : ((centerPairs (ss.map SectorSite.base)).filter
      (fun xy => xy.1 != out && xy.2 != out)).length ≤ 1) :
    gaussianL1 (directSectorThreshold ss out p q row col) ≤ B * (5*q*12+3*p*8) := by
  have hcur := current_next_bound ss out row col B h false
  have hnxt := current_next_bound ss out row col B h true
  simp only [Bool.false_and, Bool.not_false, List.filter_true, Bool.false_eq_true, ite_false] at hcur
  simp only [Bool.true_and, ite_true] at hnxt
  have hkeep : (fun xy : Nat × Nat => !(xy.1 == out || xy.2 == out)) =
      (fun xy : Nat × Nat => xy.1 != out && xy.2 != out) := by
    funext xy
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hkeep] at hnxt
  have hcur' : gaussianL1 (directSectorCurrentNext ss out row col false) ≤ 12*B := by
    have hm := Nat.mul_le_mul_right (3*B) hc
    omega
  have hnxt' : gaussianL1 (directSectorCurrentNext ss out row col true) ≤ 8*B := by
    have hm := Nat.mul_le_mul_right (3*B) hn
    omega
  unfold directSectorThreshold
  calc
    _ ≤ gaussianL1 ((directSectorCurrentNext ss out row col false).scale (5*q)) +
        gaussianL1 ((directSectorCurrentNext ss out row col true).scale (-(3*(p : Int)))) :=
      gaussianL1_add_le _ _
    _ = (5*q) * gaussianL1 (directSectorCurrentNext ss out row col false) +
        (3*p) * gaussianL1 (directSectorCurrentNext ss out row col true) := by
      simp only [gaussianL1_scale, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_mul]
      rfl
    _ ≤ (5*q)*(12*B)+(3*p)*(8*B) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hcur') (Nat.mul_le_mul_left _ hnxt')
    _ = B * (5*q*12+3*p*8) := by ring

#print axioms gaussianL1_sum_map_le
#print axioms gaussianL1_sum_skip_le
#print axioms current_next_bound
#print axioms threshold_bound

end AKLT.W.H1C016
