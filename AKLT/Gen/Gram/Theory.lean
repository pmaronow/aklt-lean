module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Division-free Gram/residual positivity. No triangularity or invertibility of the
factor is needed: the result applies to arbitrary (also rectangular) Gram factors. -/

namespace AKLT.Gen.Gram

open Matrix
open scoped ComplexOrder

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]
variable {K : Type*} [RCLike K]

/-- Strict row diagonal dominance, measured against the real diagonal, implies
positive definiteness of a Hermitian real or complex matrix. -/
theorem posDef_of_strictDiagDominant {A : Matrix n n K} (hA : A.IsHermitian)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i, ‖A i j‖ < RCLike.re (A i i)) :
    A.PosDef := by
  rw [hA.posDef_iff_eigenvalues_pos]
  intro i
  have he : Module.End.HasEigenvalue A.toLin' (hA.eigenvalues i : K) := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [Matrix.spectrum_toLin']
    exact spectrum.algebraMap_mem K (hA.eigenvalues_mem_spectrum_real i)
  obtain ⟨j, hj⟩ := eigenvalue_mem_ball he
  rw [mem_closedBall_iff_norm'] at hj
  have hr := RCLike.re_le_norm (A j j - (hA.eigenvalues i : K))
  simp only [map_sub, RCLike.ofReal_re] at hr
  linarith [hdd j]

/-- A symmetric real matrix with positive, strictly dominant diagonal is positive definite.
The strict inequality already implies positivity of the diagonal. -/
theorem real_posDef_of_strictDiagDominant {A : Matrix n n ℝ} (hA : A.IsSymm)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < A i i) : A.PosDef := by
  exact posDef_of_strictDiagDominant (Matrix.isHermitian_iff_isSymm.mpr hA)
    (by simpa only [Real.norm_eq_abs, RCLike.re_to_real] using hdd)

/-- Add a nonnegative Gram term and remove a positive scalar. -/
theorem posDef_of_gram_residual {M : Matrix n n K} {L : Matrix n k K}
    {c g : ℝ} (hc : 0 < c) (hg : 0 ≤ g)
    (hE : (c • M - g • (L * Lᴴ)).PosDef) : M.PosDef := by
  have h := hE.add_posSemidef ((Matrix.posSemidef_self_mul_conjTranspose L).smul hg)
  rw [sub_add_cancel] at h
  have hi := h.smul (inv_pos.mpr hc)
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] using hi

/-- The analytic Gram/residual criterion over both real and complex scalars. -/
theorem gram_residual_posDef {M : Matrix n n K} {L : Matrix n k K}
    {g d S : ℝ} (hg : 0 ≤ g) (hd : 0 < d) (hS : 0 < S)
    (hE : ((d * S ^ 2) • M - g • (L * Lᴴ)).IsHermitian)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i,
      ‖((d * S ^ 2) • M - g • (L * Lᴴ)) i j‖ <
      RCLike.re (((d * S ^ 2) • M - g • (L * Lᴴ)) i i)) :
    ((d * S ^ 2) • M - g • (L * Lᴴ)).PosDef ∧ M.PosDef := by
  have hp := posDef_of_strictDiagDominant hE hdd
  exact ⟨hp, posDef_of_gram_residual (mul_pos hd (sq_pos_of_pos hS)) hg hp⟩

/-- Entrywise embedding of an integer matrix. -/
def castMatrix {R : Type*} [AddGroupWithOne R] (A : Matrix n k ℤ) : Matrix n k R :=
  fun i j => (A i j : R)

/-- Integer strict diagonal dominance suffices over either real or complex scalars. -/
theorem int_posDef_of_strictDiagDominant {A : Matrix n n ℤ} (hA : A.IsSymm)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| < A i i) :
    (castMatrix A : Matrix n n K).PosDef := by
  apply posDef_of_strictDiagDominant
  · ext i j
    simp only [conjTranspose_apply, castMatrix, star_intCast]
    exact congrArg (fun z : ℤ => (z : K)) (congrFun (congrFun hA i) j)
  · intro i
    have hn (z : ℤ) : ‖(z : K)‖ = (|z| : ℝ) := by
      rw [← RCLike.ofReal_intCast (K := K), RCLike.norm_ofReal]
    have hi : (∑ j ∈ Finset.univ.erase i, |A i j| : ℝ) < (A i i : ℝ) := by
      exact_mod_cast hdd i
    simpa only [castMatrix, hn, RCLike.intCast_re] using hi

/-- The integer witness criterion. Lower triangularity of `L` is unnecessary for soundness. -/
theorem int_gram_residual_posDef {M : Matrix n n ℤ} {L : Matrix n k ℤ}
    {g d S : ℤ} (hM : M.IsSymm) (hg : 0 < g) (hd : 0 < d) (hS : 0 < S)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i,
      |((d * S ^ 2) • M - g • (L * Lᵀ)) i j| <
      ((d * S ^ 2) • M - g • (L * Lᵀ)) i i) :
    (castMatrix ((d * S ^ 2) • M - g • (L * Lᵀ)) : Matrix n n K).PosDef ∧
      (castMatrix M : Matrix n n K).PosDef := by
  have hs : ((d * S ^ 2) • M - g • (L * Lᵀ)).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hM.eq]
  have hp : (castMatrix ((d * S ^ 2) • M - g • (L * Lᵀ)) : Matrix n n K).PosDef :=
    int_posDef_of_strictDiagDominant hs hdd
  refine ⟨hp, ?_⟩
  have he : (castMatrix ((d * S ^ 2) • M - g • (L * Lᵀ)) : Matrix n n K) =
      ((d : ℝ) * (S : ℝ) ^ 2) • castMatrix M - (g : ℝ) •
        ((castMatrix L : Matrix n k K) * (castMatrix L)ᴴ) := by
    ext i j
    simp only [castMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.conjTranspose_apply]
    simp only [zsmul_eq_mul, RCLike.real_smul_eq_coe_mul, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_sum, star_intCast, RCLike.ofReal_mul,
      RCLike.ofReal_pow, RCLike.ofReal_intCast]
    norm_cast
  rw [he] at hp
  exact posDef_of_gram_residual (mul_pos (by exact_mod_cast hd)
    (sq_pos_of_pos (by exact_mod_cast hS))) (by exact_mod_cast hg.le) hp

/-- Pull real positive definiteness back to a rational symmetric matrix. -/
theorem rat_posDef_of_real {A : Matrix n n ℚ} (hA : A.IsSymm)
    (h : Matrix.PosDef (fun i j => (A i j : ℝ))) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hA)
  intro x hx
  have hxR : (fun i => (x i : ℝ)) ≠ 0 := by
    intro hz
    apply hx
    funext i
    have hi := congrFun hz i
    change (x i : ℝ) = 0 at hi
    change x i = 0
    exact_mod_cast hi
  have hp := h.dotProduct_mulVec_pos hxR
  simp only [dotProduct, Matrix.mulVec, star_trivial] at hp ⊢
  exact_mod_cast hp

/-- Rational version of the integer witness criterion. -/
theorem int_gram_residual_posDef_rat {M : Matrix n n ℤ} {L : Matrix n k ℤ}
    {g d S : ℤ} (hM : M.IsSymm) (hg : 0 < g) (hd : 0 < d) (hS : 0 < S)
    (hdd : ∀ i, ∑ j ∈ Finset.univ.erase i,
      |((d * S ^ 2) • M - g • (L * Lᵀ)) i j| <
      ((d * S ^ 2) • M - g • (L * Lᵀ)) i i) :
    (castMatrix ((d * S ^ 2) • M - g • (L * Lᵀ)) : Matrix n n ℚ).PosDef ∧
      (castMatrix M : Matrix n n ℚ).PosDef := by
  have hs : ((d * S ^ 2) • M - g • (L * Lᵀ)).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hM.eq]
  have hcast (A : Matrix n n ℤ) (ha : A.IsSymm) :
      (castMatrix A : Matrix n n ℚ).IsSymm := by
    ext i j
    exact congrArg (fun z : ℤ => (z : ℚ)) (ha.apply i j)
  have hp := int_gram_residual_posDef (K := ℝ) hM hg hd hS hdd
  constructor
  · apply rat_posDef_of_real (hcast _ hs)
    simpa only [castMatrix, Rat.cast_intCast] using! hp.1
  · apply rat_posDef_of_real (hcast _ hM)
    simpa only [castMatrix, Rat.cast_intCast] using! hp.2

end AKLT.Gen.Gram
