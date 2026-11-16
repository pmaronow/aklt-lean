import AKLT.Blueprint.H1.NodesStructure

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1M048

open AKLT.Defs
open AKLT.Blueprint.H1

private def cayleyRaw (j : Fin 3) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 + (t : ℂ) • (-Complex.I • pauli ⟨j.val + 1, by omega⟩)

private def cayleyNorm (j : Fin 3) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (1 + t ^ 2) : ℂ)⁻¹) • cayleyRaw j t

private lemma cayleyRaw_det (j : Fin 3) (t : ℝ) :
    (cayleyRaw j t).det = ((1 + t ^ 2 : ℝ) : ℂ) := by
  fin_cases j <;> norm_num [cayleyRaw, pauli, Matrix.det_fin_two] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

private lemma cayleyRaw_unitary_scale (j : Fin 3) (t : ℝ) :
    (cayleyRaw j t).conjTranspose * cayleyRaw j t =
      ((1 + t ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases j <;> ext a b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cayleyRaw, pauli, Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.add_apply, Fin.sum_univ_succ] <;>
    ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

private lemma tensorPower_smul (J : Finset (Fin 20)) (c : ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorPowerMatrix J (c • A) = c ^ J.card • tensorPowerMatrix J A := by
  ext σ τ
  simp [tensorPowerMatrix, Matrix.smul_apply, Finset.prod_mul_distrib,
    Finset.prod_const]

private lemma cayleyNorm_det (j : Fin 3) (t : ℝ) : (cayleyNorm j t).det = 1 := by
  let q : ℂ := (Real.sqrt (1 + t ^ 2) : ℝ)
  have hq2 : q ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) := by
    dsimp [q]
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
  have hqpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast hqpos.ne'
  rw [cayleyNorm, Matrix.det_smul, cayleyRaw_det]
  simp only [Fintype.card_fin]
  dsimp [q] at hq2 hq
  rw [← hq2]
  field_simp

private lemma cayleyNorm_unitary (j : Fin 3) (t : ℝ) :
    (cayleyNorm j t).conjTranspose * cayleyNorm j t = 1 := by
  let q : ℂ := (Real.sqrt (1 + t ^ 2) : ℝ)
  have hq2 : q ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) := by
    dsimp [q]
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
  have hqpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast hqpos.ne'
  have hstar : star q = q := by dsimp [q]; simp
  have hscalar : q⁻¹ * q⁻¹ * ((1 + t ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← pow_two, ← hq2]
    field_simp
  have hqinvstar : star (q⁻¹) = q⁻¹ := by simp [hstar]
  calc
    (cayleyNorm j t).conjTranspose * cayleyNorm j t =
        (star (q⁻¹) * q⁻¹) • ((cayleyRaw j t).conjTranspose * cayleyRaw j t) := by
      simp [cayleyNorm, q, Matrix.conjTranspose_smul, smul_smul]
    _ = 1 := by
      rw [cayleyRaw_unitary_scale]
      rw [smul_smul]
      rw [hqinvstar, hscalar]
      simp

theorem main : AKLT.Blueprint.H1.CayleyTensorCommutationStatement := by
  intro J M h j t
  have hunit : (cayleyNorm j t).conjTranspose * cayleyNorm j t = 1 :=
    cayleyNorm_unitary j t
  have hdet : (cayleyNorm j t).det = 1 := cayleyNorm_det j t
  have hcomm := h (cayleyNorm j t) hunit hdet
  let q : ℂ := (Real.sqrt (1 + t ^ 2) : ℝ)
  let k : ℂ := (q⁻¹) ^ J.card
  change Commute M (tensorPowerMatrix J (cayleyNorm j t)) at hcomm
  rw [cayleyNorm, tensorPower_smul] at hcomm
  change Commute M (k • tensorPowerMatrix J (cayleyRaw j t)) at hcomm
  have hqpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast hqpos.ne'
  have hk : k ≠ 0 := by
    dsimp [k]
    exact pow_ne_zero _ (inv_ne_zero hq)
  have hfactor : k • (M * tensorPowerMatrix J (cayleyRaw j t)) =
      k • (tensorPowerMatrix J (cayleyRaw j t) * M) := by
    calc
      k • (M * tensorPowerMatrix J (cayleyRaw j t)) =
          M * (k • tensorPowerMatrix J (cayleyRaw j t)) := by rw [Matrix.mul_smul]
      _ = (k • tensorPowerMatrix J (cayleyRaw j t)) * M := hcomm
      _ = k • (tensorPowerMatrix J (cayleyRaw j t) * M) := by rw [Matrix.smul_mul]
  exact (smul_right_injective (Matrix (J → Fin 2) (J → Fin 2) ℂ) hk) hfactor

end AKLT.W.H1M048

