import AKLT.Uniq.Transvectant

/-! Coordinate identities for the concrete single-site spin matrices. -/

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

variable {L N : Size}

theorem atSite_apply (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Site L N)
    (v : Hilbert L N) (σ : Configuration L N) :
    atSite A x v σ = ∑ k : Fin 5, A (σ x) k * v (Function.update σ x k) := by
  classical
  change (∑ τ : Configuration L N,
    (if ∀ y, y ≠ x → σ y = τ y then A (σ x) (τ x) else 0) * v τ) = _
  symm
  apply Fintype.sum_of_injective (Function.update σ x) (Function.update_injective σ x)
  · intro τ hτ
    have hoff : ¬ ∀ y, y ≠ x → σ y = τ y := by
      intro h
      apply hτ
      refine ⟨τ x, ?_⟩
      funext y
      by_cases hy : y = x
      · subst y
        simp
      · simp [Function.update_of_ne hy, h y hy]
    rw [ite_eq_right hoff, zero_mul]
  · intro k
    have hoff : ∀ y, y ≠ x → σ y = Function.update σ x k y := by
      intro y hy
      simp [Function.update_of_ne hy]
    rw [ite_eq_left hoff, Function.update_self]

def singleScale (k : Fin 5) : ℂ := (Real.sqrt (Nat.choose 4 k.val : ℝ) : ℂ)

theorem plus_normalization (i j : Fin 5) :
    singleScale i * spinPlus i j =
      if i.val + 1 = j.val then (j.val : ℂ) * singleScale j else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [singleScale, spinPlus, Nat.choose, ← Complex.ofReal_mul, Real.mul_self_sqrt]

theorem minus_normalization (i j : Fin 5) :
    singleScale i * spinMinus i j =
      if j.val + 1 = i.val then (4 - j.val : ℂ) * singleScale j else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [singleScale, spinMinus, spinPlus, Matrix.conjTranspose_apply,
      Nat.choose, ← Complex.ofReal_mul, Real.mul_self_sqrt]

def spectatorScale (σ : Configuration L N) (x : Site L N) : ℂ :=
  ∏ y ∈ (Finset.univ : Finset (Site L N)).erase x, singleScale (σ y)

theorem basisScale_factor (σ : Configuration L N) (x : Site L N) :
    basisScale σ = singleScale (σ x) * spectatorScale σ x := by
  classical
  exact (Finset.mul_prod_erase Finset.univ (fun y => singleScale (σ y))
    (Finset.mem_univ x)).symm

theorem basisScale_update (σ : Configuration L N) (x : Site L N) (k : Fin 5) :
    basisScale (Function.update σ x k) = singleScale k * spectatorScale σ x := by
  classical
  rw [basisScale_factor _ x, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro y hy
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]

theorem scaled_spinPlus (σ : Configuration L N) (x : Site L N) (k : Fin 5) :
    basisScale σ * spinPlus (σ x) k =
      if (σ x).val + 1 = k.val then (k.val : ℂ) * basisScale (Function.update σ x k)
      else 0 := by
  rw [basisScale_factor σ x, mul_right_comm, plus_normalization]
  split_ifs <;> simp [basisScale_update, mul_assoc]

theorem scaled_spinMinus (σ : Configuration L N) (x : Site L N) (k : Fin 5) :
    basisScale σ * spinMinus (σ x) k =
      if k.val + 1 = (σ x).val then (4 - k.val : ℂ) * basisScale (Function.update σ x k)
      else 0 := by
  rw [basisScale_factor σ x, mul_right_comm, minus_normalization]
  split_ifs <;> simp [basisScale_update, mul_assoc]

theorem physical_ext {p q : SpinorPolynomial L N} (hp : IsPhysical p) (hq : IsPhysical q)
    (h : ∀ σ : Configuration L N, p.coeff (monomialDegree σ) = q.coeff (monomialDegree σ)) :
    p = q := by
  have hd : decode p = decode q := by
    ext σ
    change p.coeff (monomialDegree σ) / basisScale σ = q.coeff (monomialDegree σ) / basisScale σ
    rw [h σ]
  rw [← encode_decode hp, ← encode_decode hq, hd]

theorem X_pderiv_physical {p : SpinorPolynomial L N} (hp : IsPhysical p)
    (x : Site L N) (a b : Fin 2) :
    IsPhysical (MvPolynomial.X (x, a) * MvPolynomial.pderiv (x, b) p) := by
  intro y
  by_cases h : x = y
  · have hd : (MvPolynomial.pderiv (x, b) p).IsWeightedHomogeneous (siteWeight y) 3 :=
      (hp y).pderiv (by simp [siteWeight, h])
    simpa [siteWeight, h] using (MvPolynomial.isWeightedHomogeneous_X ℂ (siteWeight y) (x, a)).mul hd
  · have hd : (MvPolynomial.pderiv (x, b) p).IsWeightedHomogeneous (siteWeight y) 4 :=
      (hp y).pderiv (by simp [siteWeight, h])
    simpa [siteWeight, h] using (MvPolynomial.isWeightedHomogeneous_X ℂ (siteWeight y) (x, a)).mul hd

theorem coeff_X_pderiv_self (p : SpinorPolynomial L N)
    (d : (Site L N × Fin 2) →₀ ℕ) (i : Site L N × Fin 2) :
    (MvPolynomial.X i * MvPolynomial.pderiv i p).coeff d = (d i : ℂ) * p.coeff d := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  by_cases hi : i ∈ d.support
  · rw [ite_eq_left hi, MvPolynomial.coeff_pderiv]
    have hpos : 0 < d i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have heq : (d - Finsupp.single i 1) + Finsupp.single i 1 = d := by
      ext j
      by_cases hj : j = i
      · subst j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · simp [hj]
    have hval : ((d - Finsupp.single i 1 : (Site L N × Fin 2) →₀ ℕ) i) + 1 = d i := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    have hvalC : (((d - Finsupp.single i 1 : (Site L N × Fin 2) →₀ ℕ) i : ℕ) : ℂ) + 1 =
        (d i : ℂ) := by exact_mod_cast hval
    rw [heq, hvalC]
    ring
  · rw [ite_eq_right hi]
    have hzero : d i = 0 := by simpa using hi
    simp [hzero]

theorem monomialDegree_step_up (σ : Configuration L N) (x : Site L N)
    (hk : (σ x).val < 4) :
    (monomialDegree σ - Finsupp.single (x, 0) 1) + Finsupp.single (x, 1) 1 =
      monomialDegree (Function.update σ x ⟨(σ x).val + 1, by omega⟩) := by
  classical
  ext ⟨y, k⟩
  by_cases hy : y = x
  · subst y
    fin_cases k
    · simp [monomialDegree_apply]
      omega
    · simp [monomialDegree_apply]
  · fin_cases k <;>
      simp [monomialDegree_apply, hy]

theorem monomialDegree_step_down (σ : Configuration L N) (x : Site L N)
    (hk : 0 < (σ x).val) :
    (monomialDegree σ - Finsupp.single (x, 1) 1) + Finsupp.single (x, 0) 1 =
      monomialDegree (Function.update σ x ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩) := by
  classical
  ext ⟨y, k⟩
  by_cases hy : y = x
  · subst y
    fin_cases k
    · simp [monomialDegree_apply]
      have := (σ x).isLt
      omega
    · simp [monomialDegree_apply]
  · fin_cases k <;>
      simp [monomialDegree_apply, hy]

theorem coeff_encode_spinPlus (x : Site L N) (v : Hilbert L N) (σ : Configuration L N) :
    (encode (atSite spinPlus x v)).coeff (monomialDegree σ) =
      ∑ k : Fin 5, if (σ x).val + 1 = k.val then
        (k.val : ℂ) * (encode v).coeff (monomialDegree (Function.update σ x k)) else 0 := by
  classical
  rw [coeff_encode, atSite_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, scaled_spinPlus]
  split_ifs <;> simp [coeff_encode, mul_assoc]

theorem coeff_encode_spinMinus (x : Site L N) (v : Hilbert L N) (σ : Configuration L N) :
    (encode (atSite spinMinus x v)).coeff (monomialDegree σ) =
      ∑ k : Fin 5, if k.val + 1 = (σ x).val then
        (4 - k.val : ℂ) * (encode v).coeff (monomialDegree (Function.update σ x k)) else 0 := by
  classical
  rw [coeff_encode, atSite_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc, scaled_spinMinus]
  split_ifs <;> simp [coeff_encode, mul_assoc]

theorem encode_spinZ (x : Site L N) (v : Hilbert L N) :
    encode (atSite spinZ x v) = (2 : ℂ) • encode v -
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) (encode v) := by
  classical
  have hphys : IsPhysical ((2 : ℂ) • encode v -
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) (encode v)) := by
    intro y
    exact ((MvPolynomial.weightedHomogeneousSubmodule ℂ (siteWeight y) 4).smul_mem
      (2 : ℂ) (encode_physical v y)).sub (X_pderiv_physical (encode_physical v) x 1 1 y)
  apply physical_ext (encode_physical _) hphys
  intro σ
  rw [coeff_encode, atSite_apply]
  simp only [spinZ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Function.update_eq_self, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul,
    coeff_X_pderiv_self, coeff_encode, monomialDegree_apply]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false]
  ring

theorem encode_spinPlus (x : Site L N) (v : Hilbert L N) :
    encode (atSite spinPlus x v) =
      MvPolynomial.X (x, 0) * MvPolynomial.pderiv (x, 1) (encode v) := by
  classical
  apply physical_ext (encode_physical _) (X_pderiv_physical (encode_physical v) x 0 1)
  intro σ
  rw [coeff_encode_spinPlus, MvPolynomial.coeff_X_mul']
  by_cases hk : (σ x).val < 4
  · let j : Fin 5 := ⟨(σ x).val + 1, by omega⟩
    have hmem : (x, (0 : Fin 2)) ∈ (monomialDegree σ).support := by
      apply Finsupp.mem_support_iff.mpr
      simp only [monomialDegree_apply, ite_true]
      omega
    rw [ite_eq_left hmem, MvPolynomial.coeff_pderiv, monomialDegree_step_up σ x hk]
    have hval : ((monomialDegree σ - Finsupp.single (x, 0) 1 : (Site L N × Fin 2) →₀ ℕ) (x, 1)) + 1 = (σ x).val + 1 := by
      simp [Finsupp.tsub_apply, monomialDegree_apply]
    have hvalC : (((monomialDegree σ - Finsupp.single (x, 0) 1 :
        (Site L N × Fin 2) →₀ ℕ) (x, 1) : ℕ) : ℂ) + 1 = ((σ x).val + 1 : ℕ) := by
      exact_mod_cast hval
    rw [hvalC, Finset.sum_eq_single j]
    · simp only [j, ite_true]
      ring
    · intro k _ hkj
      have hne : (σ x).val + 1 ≠ k.val := by
        intro h
        apply hkj
        exact Fin.ext h.symm
      exact ite_eq_right hne
    · simp
  · have hval : (σ x).val = 4 := by have := (σ x).isLt; omega
    have hmem : (x, (0 : Fin 2)) ∉ (monomialDegree σ).support := by
      simp [Finsupp.mem_support_iff, monomialDegree_apply, hval]
    rw [ite_eq_right hmem]
    apply Finset.sum_eq_zero
    intro k _
    apply ite_eq_right
    have := k.isLt
    omega

theorem encode_spinMinus (x : Site L N) (v : Hilbert L N) :
    encode (atSite spinMinus x v) =
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 0) (encode v) := by
  classical
  apply physical_ext (encode_physical _) (X_pderiv_physical (encode_physical v) x 1 0)
  intro σ
  rw [coeff_encode_spinMinus, MvPolynomial.coeff_X_mul']
  by_cases hk : 0 < (σ x).val
  · let j : Fin 5 := ⟨(σ x).val - 1, by have := (σ x).isLt; omega⟩
    have hmem : (x, (1 : Fin 2)) ∈ (monomialDegree σ).support := by
      apply Finsupp.mem_support_iff.mpr
      simpa only [monomialDegree_apply, show (1 : Fin 2) ≠ 0 by decide, ite_false] using
        (Nat.ne_zero_of_lt hk)
    rw [ite_eq_left hmem, MvPolynomial.coeff_pderiv, monomialDegree_step_down σ x hk]
    have hval : (((monomialDegree σ - Finsupp.single (x, 1) 1 :
        (Site L N × Fin 2) →₀ ℕ) (x, 0) : ℕ) : ℂ) + 1 =
        (4 - j.val : ℂ) := by
      have he : (monomialDegree σ - Finsupp.single (x, 1) 1 :
          (Site L N × Fin 2) →₀ ℕ) (x, 0) = 4 - (σ x).val := by
        simp [Finsupp.tsub_apply, monomialDegree_apply]
      rw [he, Nat.cast_sub (by have := (σ x).isLt; omega)]
      dsimp [j]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [hval, Finset.sum_eq_single j]
    · have hj : j.val + 1 = (σ x).val := by dsimp [j]; omega
      rw [ite_eq_left hj]
      ring
    · intro k _ hkj
      have hne : k.val + 1 ≠ (σ x).val := by
        intro h
        apply hkj
        apply Fin.ext
        dsimp [j]
        omega
      exact ite_eq_right hne
    · simp
  · have hzero : (σ x).val = 0 := by omega
    have hmem : (x, (1 : Fin 2)) ∉ (monomialDegree σ).support := by
      simp [Finsupp.mem_support_iff, monomialDegree_apply, hzero]
    rw [ite_eq_right hmem]
    apply Finset.sum_eq_zero
    intro k _
    apply ite_eq_right
    omega

/-- Node S1: the frozen normalized single-site matrices act as binary differential operators. -/
def SingleSiteActionStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N, ∀ v : Hilbert L N,
    encode (atSite spinZ x v) = (2 : ℂ) • encode v -
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 1) (encode v) ∧
    encode (atSite spinPlus x v) =
      MvPolynomial.X (x, 0) * MvPolynomial.pderiv (x, 1) (encode v) ∧
    encode (atSite spinMinus x v) =
      MvPolynomial.X (x, 1) * MvPolynomial.pderiv (x, 0) (encode v)

theorem singleSiteAction : SingleSiteActionStatement :=
  fun _ _ x v => ⟨encode_spinZ x v, encode_spinPlus x v, encode_spinMinus x v⟩

#print axioms atSite_apply
#print axioms plus_normalization
#print axioms minus_normalization
#print axioms basisScale_factor
#print axioms basisScale_update
#print axioms scaled_spinPlus
#print axioms scaled_spinMinus
#print axioms physical_ext
#print axioms X_pderiv_physical
#print axioms coeff_X_pderiv_self
#print axioms monomialDegree_step_up
#print axioms monomialDegree_step_down
#print axioms coeff_encode_spinPlus
#print axioms coeff_encode_spinMinus
#print axioms encode_spinZ
#print axioms encode_spinPlus
#print axioms encode_spinMinus
#print axioms singleSiteAction

end AKLT.Uniq
