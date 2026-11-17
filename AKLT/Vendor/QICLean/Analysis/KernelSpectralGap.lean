module
/-
Vendored from https://github.com/LionSR/QICLean
Commit: 603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac
Original path: QICLean/Analysis/KernelSpectralGap.lean
Modified for the AKLT campaign: namespace/import relocation and explicit implicit-variable options.
See AKLT/Vendor/manifest.json for hashes and additional changes.
License: Apache-2.0; original authorship and notices follow unchanged.
-/
/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
public import AKLT.Vendor.QICLean.Analysis.EuclideanEigenvectorBasis
public import AKLT.Vendor.QICLean.Analysis.LowEnergyPerturbation

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace AKLT.Vendor.QICLean


/-!
# The quadratic-form gap above a Hermitian kernel

A lower bound for every nonzero real eigenvalue bounds the quadratic form
on the orthogonal complement of the whole kernel. No dimension-one
assumption is required. This is the spectral step used with detectability
in ALVV, arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519
and 1562–1568.
-/

open scoped BigOperators InnerProductSpace

namespace Matrix.IsHermitian
open _root_.Matrix.IsHermitian

/-- The actual spectral gap controls every vector orthogonal to the kernel.
The real bound may have either sign. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:dl` and `thm:FF-tH`, lines 1508–1519 and 1562–1568. -/
theorem mul_norm_sq_le_re_inner_of_spectral_gap
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {γ : ℝ} (hγgap : ∀ e ∈ spectrum ℝ A, e = 0 ∨ γ ≤ e)
    (x : EuclideanSpace ℂ n)
    (horth : ∀ z : EuclideanSpace ℂ n,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A z = 0 → ⟪z, x⟫_ℂ = 0) :
    γ * ‖x‖ ^ 2 ≤ (⟪x, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A x⟫_ℂ).re := by
  have hnorm : ‖x‖ ^ 2 = ∑ j, ‖hA.eigenvectorBasis.repr x j‖ ^ 2 := by
    simpa only [LinearIsometryEquiv.norm_map] using
      EuclideanSpace.norm_sq_eq (hA.eigenvectorBasis.repr x)
  change γ * ‖x‖ ^ 2 ≤
    (⟪x, (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).toLinearMap x⟫_ℂ).re
  rw [hnorm, Finset.mul_sum,
    AKLT.Vendor.QICLean.OrthonormalBasis.re_inner_apply_eq_sum_of_eigen hA.eigenvectorBasis hA.eigenvalues
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).toLinearMap
      (AKLT.Vendor.QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis hA) x]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rcases hγgap (hA.eigenvalues j) (hA.eigenvalues_mem_spectrum_real j) with hz | hj
  · have hzero : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A
        (hA.eigenvectorBasis j) = 0 := by
      simpa only [hz, map_zero, zero_smul] using
        AKLT.Vendor.QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis hA j
    have hcoeff : hA.eigenvectorBasis.repr x j = 0 :=
      (hA.eigenvectorBasis.repr_apply_apply x j).trans (horth _ hzero)
    simpa only [hcoeff, norm_zero, zero_pow two_ne_zero, mul_zero] using (le_refl (0 : ℝ))
  · exact mul_le_mul_of_nonneg_right hj (sq_nonneg _)

end Matrix.IsHermitian


end AKLT.Vendor.QICLean
