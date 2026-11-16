import AKLT.W.H1C020.Site

/-!
Integration of the passage spin.  With at most three passage bonds, the
passage spin's odd moments vanish and its second moment is `δ_{kl} m₂`, with
`m₂ = 1/3` for `U` and `1/5` for `D`.
-/

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- Second moment of one coordinate. -/
def m2 (s : Status) : ℚ := if s = .D then 1/5 else 1/3

/-- Passage scalar product with a ring spin. -/
def cDot (y : Plane) : LPoly := formalDot (fun k => .inl ((0,0), k)) (fun k => .inl (y, k))

lemma cDot_eq (y : Plane) : cDot y = ∑ k : Fin 3, sv (0,0) k * sv y k := rfl

lemma sv_eq_spinB (x : Plane) (k : Fin 3) : sv x k = spinB x (k.val + 1) := by
  fin_cases k <;> simp [spinB]

lemma spinM_of_list (x : Plane) (cs : List Nat) :
    spinM x cs = MvPolynomial.C 1 * spinM x cs * liftV 1 := by
  simp

lemma contract_center_monomial (st : Plane → Status) (cs : List Nat) :
    contractSpins {(0,0)} st (spinM (0,0) cs) = MvPolynomial.C (rationalStatusMoment (st (0,0))
      (colorExponent (countColor 1 cs) (countColor 2 cs) (countColor 3 cs))) := by
  rw [spinM_of_list, contract_spin_vec]
  simp

lemma rationalStatusMoment_odd (s : Status) (m : Fin 3 → ℕ)
    (h : (∑ i, m i) = 1 ∨ (∑ i, m i) = 3) : rationalStatusMoment s m = 0 := by
  have hr : rationalMoment m = 0 := by
    unfold rationalMoment
    rcases h with h | h <;> simp [h]
  unfold rationalStatusMoment
  split <;> simp [hr]

lemma contract_c1 (st : Plane → Status) (k : Fin 3) :
    contractSpins {(0,0)} st (sv (0,0) k) = 0 := by
  rw [sv_eq_spinB, ← spinM_single, contract_center_monomial, rationalStatusMoment_odd]
  · simp
  · left
    fin_cases k <;> simp [colorExponent, countColor, Fin.sum_univ_three]

lemma contract_c2 (st : Plane → Status) (k l : Fin 3) :
    contractSpins {(0,0)} st (sv (0,0) k * sv (0,0) l) =
      MvPolynomial.C (if k = l then m2 (st (0,0)) else 0) := by
  have hm : sv (0,0) k * sv (0,0) l = spinM (0,0) [k.val+1, l.val+1] := by
    simp [spinM, sv_eq_spinB]
  rw [hm, contract_center_monomial]
  congr 1
  by_cases hs : st (0,0) = .D <;>
    fin_cases k <;> fin_cases l <;>
      simp [hs, m2, rationalStatusMoment, rationalMoment, colorExponent, countColor,
        Fin.sum_univ_three, Fin.exists_fin_succ] <;> norm_num

lemma contract_c3 (st : Plane → Status) (k l n : Fin 3) :
    contractSpins {(0,0)} st (sv (0,0) k * sv (0,0) l * sv (0,0) n) = 0 := by
  have hm : sv (0,0) k * sv (0,0) l * sv (0,0) n = spinM (0,0) [k.val+1, l.val+1, n.val+1] := by
    simp [spinM, sv_eq_spinB, mul_assoc]
  rw [hm, contract_center_monomial, rationalStatusMoment_odd]
  · simp
  · right
    fin_cases k <;> fin_cases l <;> fin_cases n <;>
      simp [colorExponent, countColor, Fin.sum_univ_three]

lemma center_split (V' : Finset Plane) (h0 : ((0,0) : Plane) ∉ V') (st : Plane → Status)
    (P Q : LPoly) (hP : VarsIn {(0,0)} P) (hQ : VarsIn V' Q) :
    contractSpins (insert (0,0) V') st (P * Q) =
      contractSpins {(0,0)} st P * contractSpins V' st Q := by
  rw [Finset.insert_eq]
  exact contractSpins_disjoint_mul _ _ st (Finset.disjoint_singleton_left.mpr h0) P Q
    hP.supported hQ.supported

lemma varsIn_origin_sv (k : Fin 3) : VarsIn {(0,0)} (sv (0,0) k) :=
  varsIn_sv (Finset.mem_singleton_self _) k

/-- Pair sum of the ring polynomial with the two inserted coordinates. -/
def pairSum (V' : Finset Plane) (st : Plane → Status) (R : LPoly) (y y' : Plane) : VectorPolynomial :=
  ∑ k : Fin 3, contractSpins V' st (R * sv y k * sv y' k)

lemma center_term1 (V' : Finset Plane) (h0 : ((0,0) : Plane) ∉ V') (st : Plane → Status)
    (R : LPoly) (hR : VarsIn V' R) (y : Plane) (t : ℚ) (hy : t ≠ 0 → y ∈ V') :
    contractSpins (insert (0,0) V') st (R * (MvPolynomial.C t * cDot y)) = 0 := by
  by_cases ht : t = 0
  · simp [ht, contractSpins_zero']
  have hyV := hy ht
  have he : R * (MvPolynomial.C t * cDot y) =
      MvPolynomial.C t * ∑ k : Fin 3, sv (0,0) k * (R * sv y k) := by
    rw [cDot_eq, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he, contractSpins_C_mul, contractSpins_sum]
  have : ∀ k : Fin 3, contractSpins (insert (0,0) V') st (sv (0,0) k * (R * sv y k)) = 0 := by
    intro k
    rw [center_split V' h0 st _ _ (varsIn_origin_sv k) (hR.mul (varsIn_sv hyV k)), contract_c1,
      zero_mul]
  simp [this]

lemma center_term2 (V' : Finset Plane) (h0 : ((0,0) : Plane) ∉ V') (st : Plane → Status)
    (R : LPoly) (hR : VarsIn V' R) (y y' : Plane) (t t' : ℚ) (hy : t ≠ 0 → y ∈ V')
    (hy' : t' ≠ 0 → y' ∈ V') :
    contractSpins (insert (0,0) V') st (R * (MvPolynomial.C t * cDot y) * (MvPolynomial.C t' * cDot y')) =
      MvPolynomial.C (t * t') * (MvPolynomial.C (m2 (st (0,0))) * pairSum V' st R y y') := by
  by_cases ht : t = 0
  · simp [ht, contractSpins_zero']
  by_cases ht' : t' = 0
  · simp [ht', contractSpins_zero']
  have hyV := hy ht
  have hyV' := hy' ht'
  have he : R * (MvPolynomial.C t * cDot y) * (MvPolynomial.C t' * cDot y') =
      MvPolynomial.C (t * t') * ∑ k : Fin 3, ∑ l : Fin 3,
        (sv (0,0) k * sv (0,0) l) * (R * sv y k * sv y' l) := by
    simp only [cDot_eq, Fin.sum_univ_three, MvPolynomial.C_mul]
    ring
  rw [he, contractSpins_C_mul]
  have hkl : ∀ k l : Fin 3, contractSpins (insert (0,0) V') st
      ((sv (0,0) k * sv (0,0) l) * (R * sv y k * sv y' l)) =
        MvPolynomial.C (if k = l then m2 (st (0,0)) else 0) *
          contractSpins V' st (R * sv y k * sv y' l) := by
    intro k l
    rw [center_split V' h0 st _ _ ((varsIn_origin_sv k).mul (varsIn_origin_sv l))
      ((hR.mul (varsIn_sv hyV k)).mul (varsIn_sv hyV' l)), contract_c2]
  simp only [Fin.sum_univ_three, contractSpins_add, hkl, pairSum]
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, MvPolynomial.C_0, zero_mul, add_zero, zero_add]
  ring

lemma center_term3 (V' : Finset Plane) (h0 : ((0,0) : Plane) ∉ V') (st : Plane → Status)
    (R : LPoly) (hR : VarsIn V' R) (y y' y'' : Plane) (t t' t'' : ℚ) (hy : t ≠ 0 → y ∈ V')
    (hy' : t' ≠ 0 → y' ∈ V') (hy'' : t'' ≠ 0 → y'' ∈ V') :
    contractSpins (insert (0,0) V') st (R * (MvPolynomial.C t * cDot y) *
      (MvPolynomial.C t' * cDot y') * (MvPolynomial.C t'' * cDot y'')) = 0 := by
  by_cases ht : t = 0
  · simp [ht, contractSpins_zero']
  by_cases ht' : t' = 0
  · simp [ht', contractSpins_zero']
  by_cases ht'' : t'' = 0
  · simp [ht'', contractSpins_zero']
  have hyV := hy ht
  have hyV' := hy' ht'
  have hyV'' := hy'' ht''
  have he : R * (MvPolynomial.C t * cDot y) * (MvPolynomial.C t' * cDot y') *
      (MvPolynomial.C t'' * cDot y'') =
      MvPolynomial.C (t * t' * t'') * ∑ k : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3,
        (sv (0,0) k * sv (0,0) l * sv (0,0) n) * (R * sv y k * sv y' l * sv y'' n) := by
    simp only [cDot_eq, Fin.sum_univ_three, MvPolynomial.C_mul]
    ring
  rw [he, contractSpins_C_mul]
  have hz : ∀ k l n : Fin 3, contractSpins (insert (0,0) V') st
      ((sv (0,0) k * sv (0,0) l * sv (0,0) n) * (R * sv y k * sv y' l * sv y'' n)) = 0 := by
    intro k l n
    rw [center_split V' h0 st _ _
      (((varsIn_origin_sv k).mul (varsIn_origin_sv l)).mul (varsIn_origin_sv n))
      (((hR.mul (varsIn_sv hyV k)).mul (varsIn_sv hyV' l)).mul (varsIn_sv hyV'' n)),
      contract_c3, zero_mul]
  simp only [Fin.sum_univ_three, contractSpins_add, hz, add_zero, mul_zero]

/-- Integration of the passage spin against at most three passage bonds. -/
theorem center_expand (V' : Finset Plane) (h0 : ((0,0) : Plane) ∉ V') (st : Plane → Status)
    (R : LPoly) (hR : VarsIn V' R) (y0 y1 y2 : Plane) (t0 t1 t2 : ℚ)
    (hy0 : t0 ≠ 0 → y0 ∈ V') (hy1 : t1 ≠ 0 → y1 ∈ V') (hy2 : t2 ≠ 0 → y2 ∈ V') :
    contractSpins (insert (0,0) V') st (R * ((1 + MvPolynomial.C t0 * cDot y0) *
      (1 + MvPolynomial.C t1 * cDot y1) * (1 + MvPolynomial.C t2 * cDot y2))) =
      contractSpins V' st R + MvPolynomial.C (m2 (st (0,0))) *
        (MvPolynomial.C (t0*t1) * pairSum V' st R y0 y1 +
          MvPolynomial.C (t0*t2) * pairSum V' st R y0 y2 +
          MvPolynomial.C (t1*t2) * pairSum V' st R y1 y2) := by
  set A := MvPolynomial.C t0 * cDot y0
  set B := MvPolynomial.C t1 * cDot y1
  set E := MvPolynomial.C t2 * cDot y2
  have hexp : R * ((1 + A) * (1 + B) * (1 + E)) =
      R + R * A + R * B + R * E + R * A * B + R * A * E + R * B * E + R * A * B * E := by ring
  rw [hexp]
  simp only [contractSpins_add]
  rw [contractSpins_superset (Finset.subset_insert _ _) st R hR.supported,
    center_term1 V' h0 st R hR y0 t0 hy0, center_term1 V' h0 st R hR y1 t1 hy1,
    center_term1 V' h0 st R hR y2 t2 hy2,
    center_term2 V' h0 st R hR y0 y1 t0 t1 hy0 hy1,
    center_term2 V' h0 st R hR y0 y2 t0 t2 hy0 hy2,
    center_term2 V' h0 st R hR y1 y2 t1 t2 hy1 hy2,
    center_term3 V' h0 st R hR y0 y1 y2 t0 t1 t2 hy0 hy1 hy2]
  ring

end AKLT.W.H1C020
