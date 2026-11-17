module
public import AKLT.Blueprint.Q.NodesStar
public import AKLT.Vendor.QICLean.Analysis.KernelSpectralGap

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.Q019

theorem main : AKLT.Blueprint.Q.SpectralKernelCoercivityStatement := by
  unfold AKLT.Blueprint.Q.SpectralKernelCoercivityStatement
  intro ι _ T hT hpositive g hg hgap
  classical
  let n : ℕ := Fintype.card ι
  have hn : Module.finrank ℂ (EuclideanSpace ℂ ι) = n := by simp [n]
  let b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ ι) := hT.eigenvectorBasis hn
  let a : Fin n → ℝ := hT.eigenvalues hn
  have hdiag (i : Fin n) : T (b i) = (a i : ℂ) • b i := by
    dsimp [b, a]
    exact hT.apply_eigenvectorBasis hn i
  have hcoerciveOnOrthogonal (x : EuclideanSpace ℂ ι)
      (horth : ∀ z : EuclideanSpace ℂ ι, T z = 0 → inner ℂ z x = 0) :
      g * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re := by
    have hnorm : ‖x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 := by
      simpa only [LinearIsometryEquiv.norm_map] using
        EuclideanSpace.norm_sq_eq (b.repr x)
    rw [hnorm, Finset.mul_sum,
      AKLT.Vendor.QICLean.OrthonormalBasis.re_inner_apply_eq_sum_of_eigen b a T hdiag x]
    refine Finset.sum_le_sum fun i _ => ?_
    have hnonneg : 0 ≤ a i := by
      have h := hpositive (b i)
      rw [hdiag i] at h
      simpa [inner_smul_right, inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i] using h
    rcases eq_or_lt_of_le hnonneg with hzero | hpos
    · have heigenZero : T (b i) = 0 := by rw [hdiag i]; simp [hzero]
      have hcoeff : b.repr x i = 0 :=
        (b.repr_apply_apply x i).trans (horth (b i) heigenZero)
      simp [hzero.symm, hcoeff]
    · have heigenvalue : T.HasEigenvalue (a i : ℂ) :=
        Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr (hdiag i), b.orthonormal.ne_zero i⟩
      exact mul_le_mul_of_nonneg_right (hgap (a i) hpos heigenvalue) (sq_nonneg _)
  intro ψ
  let p : EuclideanSpace ℂ ι := (LinearMap.ker T).starProjection ψ
  let x : EuclideanSpace ℂ ι := ψ - p
  change g * ‖x‖ ^ 2 ≤ (inner ℂ ψ (T ψ)).re
  have hp : p ∈ LinearMap.ker T := by
    dsimp [p]
    exact Submodule.starProjection_apply_mem _ _
  have hTp : T p = 0 := LinearMap.mem_ker.mp hp
  have hTx : T x = T ψ := by
    dsimp [x]
    rw [map_sub, hTp, sub_zero]
  have horth : ∀ z : EuclideanSpace ℂ ι, T z = 0 → inner ℂ z x = 0 := by
    intro z hz
    have hzx : inner ℂ x z = 0 := by
      dsimp [x, p]
      exact Submodule.starProjection_inner_eq_zero ψ z (LinearMap.mem_ker.mpr hz)
    simpa [hzx] using (inner_conj_symm (𝕜 := ℂ) z x).symm
  have hform : inner ℂ ψ (T ψ) = inner ℂ x (T x) := by
    rw [← hTx]
    have hdecomp : ψ = x + p := by dsimp [x]; simp
    rw [hdecomp, inner_add_left, ← hT p x, hTp]
    simp
  calc
    g * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re := hcoerciveOnOrthogonal x horth
    _ = (inner ℂ ψ (T ψ)).re := congrArg Complex.re hform.symm

end AKLT.W.Q019

#print axioms AKLT.W.Q019.main
