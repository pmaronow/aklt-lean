import AKLT.W.H1C017.Main

namespace AKLT.W.H1C014

open AKLT.Cert.H1 AKLT.Cert.H1.Production
open scoped BigOperators

private def sparseCoeff : List Nat → List Int → Nat → Int
  | i :: is, a :: as, j => (if j = i then a else 0) + sparseCoeff is as j
  | _, _, _ => 0

private theorem sparseCoeff_zero (is : List Nat) (as : List Int) (j : Nat)
    (hj : j ∉ is) : sparseCoeff is as j = 0 := by
  induction is generalizing as with
  | nil => simp [sparseCoeff]
  | cons i is ih =>
      cases as with
      | nil => simp [sparseCoeff]
      | cons a as =>
          simp only [List.mem_cons, not_or] at hj
          simp only [sparseCoeff, ite_eq_right hj.1, ih as hj.2, zero_add]

private theorem sparseCoeff_bound (is : List Nat) (as : List Int) (h : Int)
    (hpos : 0 < h) (hnd : is.Nodup)
    (ha : ∀ a ∈ as, -h ≤ a ∧ a < h) (j : Nat) :
    -h ≤ sparseCoeff is as j ∧ sparseCoeff is as j < h := by
  induction is generalizing as with
  | nil => simp only [sparseCoeff]; omega
  | cons i is ih =>
      cases as with
      | nil => simp only [sparseCoeff]; omega
      | cons a as =>
          obtain ⟨hni, hnd⟩ := List.nodup_cons.mp hnd
          by_cases hji : j = i
          · subst j
            simp only [sparseCoeff, ↓reduceIte, sparseCoeff_zero is as i hni, add_zero]
            exact ha a (by simp)
          · simp only [sparseCoeff, ite_eq_right hji, zero_add]
            exact ih as hnd (fun a hm => ha a (by simp [hm]))

private theorem sum_sparseCoeff (width lanes : Nat) (is : List Nat) (as : List Int)
    (hlen : is.length = as.length) (hrange : ∀ i ∈ is, i < lanes) :
    (∑ j : Fin lanes, sparseCoeff is as j * ((2 : Nat)^(width*j.val) : Int)) =
      sparsePack width is as := by
  induction is generalizing as with
  | nil =>
      cases as with
      | nil => simp [sparseCoeff, sparsePack]
      | cons a as => simp at hlen
  | cons i is ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have hi : i < lanes := hrange i (by simp)
          have ht := ih as (by simpa using hlen) (fun j hj => hrange j (by simp [hj]))
          simp only [sparseCoeff, add_mul, Finset.sum_add_distrib]
          rw [ht]
          have hs : (∑ j : Fin lanes,
              (if j.val = i then a else 0) * ((2 : Nat)^(width*j.val) : Int)) =
                a * ((2 : Nat)^(width*i) : Int) := by
            rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin lanes)]
            · simp only [↓reduceIte]
            · intro j _ hj
              have hji : j.val ≠ i := fun h => hj (Fin.ext h)
              simp only [ite_eq_right hji, zero_mul]
            · simp
          rw [hs]
          rfl

private theorem sparseCoeff_map (is : List Nat) (as : List Int)
    (hlen : is.length = as.length) (hnd : is.Nodup) :
    is.map (sparseCoeff is as) = as := by
  induction is generalizing as with
  | nil =>
      cases as with
      | nil => rfl
      | cons a as => simp at hlen
  | cons i is ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          obtain ⟨hni, hnd⟩ := List.nodup_cons.mp hnd
          simp only [List.map_cons]
          have hhead : sparseCoeff (i :: is) (a :: as) i = a := by
            simp [sparseCoeff, sparseCoeff_zero is as i hni]
          rw [hhead]
          congr 1
          calc
            is.map (sparseCoeff (i :: is) (a :: as)) = is.map (sparseCoeff is as) := by
              apply List.map_congr_left
              intro j hj
              have hji : j ≠ i := fun h => hni (h ▸ hj)
              simp only [sparseCoeff, ite_eq_right hji, zero_add]
            _ = as := ih as (by simpa using hlen) hnd

/-- Sparse rows can use the proved dense signed-digit decoder once their
positions are distinct and lie in the biased range. -/
theorem signedSparseDecode (width lanes : Nat) (hw : 0 < width)
    (positions : List Nat) (values : List Int)
    (hlen : positions.length = values.length) (hnd : positions.Nodup)
    (hrange : ∀ j ∈ positions, j < lanes)
    (hbound : ∀ a ∈ values,
      -((2 : Nat)^(width-1) : Int) ≤ a ∧ a < ((2 : Nat)^(width-1) : Int)) :
    positions.map (fun j =>
      signedDigit (sparsePack width positions values + signedBias width lanes) width j) =
      values := by
  have hsum := sum_sparseCoeff width lanes positions values hlen hrange
  have hdense : ∀ j : Fin lanes,
      -((2 : Nat)^(width-1) : Int) ≤ sparseCoeff positions values j ∧
        sparseCoeff positions values j < ((2 : Nat)^(width-1) : Int) := by
    intro j
    apply sparseCoeff_bound positions values _ (by positivity) hnd hbound
  calc
    _ = positions.map (sparseCoeff positions values) := by
      apply List.map_congr_left
      intro j hj
      have h := AKLT.W.H1C017.main width lanes hw
        (fun k => sparseCoeff positions values k.val) hdense ⟨j, hrange j hj⟩
      rw [hsum] at h
      exact h
    _ = values := sparseCoeff_map positions values hlen hnd

#print axioms signedSparseDecode

end AKLT.W.H1C014
