import AKLT.W.H1C015.Expansion

namespace AKLT.W.H1C015

open AKLT.Cert.H1 AKLT.Cert.H1.Production
open scoped BigOperators

/-- Evaluation of a Gaussian-valued column polynomial. -/
def Expands (width n : Nat) (packed : Gaussian) (direct : Nat → Gaussian) : Prop :=
  value packed = ∑ col ∈ Finset.range n, value (direct col) * weight width col

theorem expands_zero (width n : Nat) :
    Expands width n Gaussian.zero (fun _ => Gaussian.zero) := by
  simp [Expands]

theorem expands_add (width n : Nat) (a b : Gaussian) (f g : Nat → Gaussian)
    (ha : Expands width n a f) (hb : Expands width n b g) :
    Expands width n (a.add b) (fun col => (f col).add (g col)) := by
  unfold Expands at *
  simp only [value_add, add_mul, Finset.sum_add_distrib]
  rw [ha, hb]

theorem expands_scale (width n : Nat) (a : Gaussian) (f : Nat → Gaussian) (z : Int)
    (ha : Expands width n a f) :
    Expands width n (a.scale z) (fun col => (f col).scale z) := by
  unfold Expands at *
  simp only [value_scale, ha, Finset.mul_sum, mul_assoc]

theorem expands_sum {S : Type*} (width n : Nat) (xs : List S)
    (a : S → Gaussian) (f : S → Nat → Gaussian)
    (h : ∀ x ∈ xs, Expands width n (a x) (f x)) :
    Expands width n (sumGaussian (xs.map a))
      (fun col => sumGaussian (xs.map fun x => f x col)) := by
  induction xs with
  | nil => exact expands_zero width n
  | cons x xs ih =>
      exact expands_add width n _ _ _ _ (h x (by simp))
        (ih (fun y hy => h y (by simp [hy])))

theorem expands_filterMap {S : Type*} (width n : Nat) (xs : List S)
    (skip : S → Bool) (a : S → Gaussian) (f : S → Nat → Gaussian)
    (h : ∀ x ∈ xs, Expands width n (a x) (f x)) :
    Expands width n
      (sumGaussian (xs.filterMap fun x => if skip x then none else some (a x)))
      (fun col => sumGaussian (xs.filterMap fun x =>
        if skip x then none else some (f x col))) := by
  induction xs with
  | nil => exact expands_zero width n
  | cons x xs ih =>
      have ht := ih (fun y hy => h y (by simp [hy]))
      cases hx : skip x
      · simpa only [List.filterMap_cons, hx, Bool.false_eq_true, ite_false,
          List.cons_append, List.nil_append, sumGaussian] using
          expands_add width n _ _ _ _ (h x (by simp)) ht
      · simpa only [List.filterMap_cons, hx, ite_true, List.nil_append] using ht

/-- A uniform version of the two centre expressions in the packed constructor. -/
def packedCurrentNext (ss : List SectorSite) (out row width : Nat) (next : Bool) : Gaussian :=
  ((sectorRingValue ss row width []).scale (if next then 5 else 3)).add
    (sumGaussian ((centerPairs (ss.map fun s => s.base)).filterMap fun (x,y) =>
      if next && (x == out || y == out) then none else
        some (sumGaussian ((List.range 3).map fun k =>
          sectorRingValue ss row width (centerCodes ss.length x y (k+1))))))

theorem current_expansion (ss : List SectorSite) (h : Strides ss)
    (out row width : Nat) (next : Bool) :
    Expands width (lanes ss) (packedCurrentNext ss out row width next)
      (fun col => directSectorCurrentNext ss out row col next) := by
  unfold packedCurrentNext directSectorCurrentNext
  apply expands_add
  · apply expands_scale
    exact ring_expansion ss h row width []
  · apply expands_filterMap
    intro xy hxy
    apply expands_sum
    intro k hk
    exact ring_expansion ss h row width (centerCodes ss.length xy.1 xy.2 (k+1))

theorem filter_center_terms (xs : List (Nat × Nat)) (f : Nat → Nat → Gaussian) (out : Nat) :
    ((xs.map fun (x,y) => (x,y,f x y)).filterMap fun (x,y,c) =>
      if x != out && y != out then some c else none) =
    xs.filterMap (fun (x,y) => if x == out || y == out then none else some (f x y)) := by
  rw [List.filterMap_map]
  apply congrArg (fun g => xs.filterMap g)
  funext ⟨x,y⟩
  by_cases hx : x = out <;> by_cases hy : y = out <;> simp [hx, hy]

theorem packed_threshold_eq (ss : List SectorSite) (out row width p q : Nat) :
    packedSectorThresholdRow ss out row width p q =
      ((packedCurrentNext ss out row width false).scale (5*q)).add
        ((packedCurrentNext ss out row width true).scale (-(3*(p : Int)))) := by
  have hf := filter_center_terms (centerPairs (ss.map fun s => s.base))
    (fun x y => sumGaussian ((List.range 3).map fun k =>
      sectorRingValue ss row width (centerCodes ss.length x y (k+1)))) out
  dsimp only at hf
  unfold packedSectorThresholdRow packedCurrentNext
  dsimp only
  rw [hf]
  simp [List.map_map, Function.comp_def]

theorem threshold_expansion (ss : List SectorSite) (h : Strides ss)
    (out row width p q : Nat) :
    packedSectorThresholdRow ss out row width p q =
      sumGaussian ((List.range (lanes ss)).map fun col =>
        (directSectorThreshold ss out p q row col).scale
          ((2 : Nat)^(width*col) : Int)) := by
  apply value_injective
  rw [value_sum_range]
  have he : Expands width (lanes ss) (packedSectorThresholdRow ss out row width p q)
      (fun col => directSectorThreshold ss out p q row col) := by
    rw [packed_threshold_eq]
    unfold directSectorThreshold
    apply expands_add
    · exact expands_scale width (lanes ss) _ _ _
        (current_expansion ss h out row width false)
    · exact expands_scale width (lanes ss) _ _ _
        (current_expansion ss h out row width true)
  rw [he]
  apply Finset.sum_congr rfl
  intro col hcol
  rw [value_scale]
  have hw : (((2 : Nat)^(width*col) : Int) : R) = weight width col := by
    simp [weight]
  rw [hw]
  exact mul_comm _ _

end AKLT.W.H1C015
