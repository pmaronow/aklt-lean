import AKLT.Blueprint.H1.NodesSector
import AKLT.Vendor.QICLean.Analysis.LowEnergyPerturbation
import Mathlib.Analysis.Normed.Group.Submodule

noncomputable section

open scoped InnerProductSpace
open AKLT.Defs

namespace AKLT.W.H1M040

theorem main : AKLT.Blueprint.H1.PositiveSpectrumStatement := by
  intro J S O hInv hSym
  letI : NormedAddCommGroup S := Submodule.normedAddCommGroup S
  letI : InnerProductSpace ℂ S := S.innerProductSpace
  let T : S →ₗ[ℂ] S := O.restrict hInv
  have hT : T.IsSymmetric := by
    intro x y
    simpa [T] using hSym (x : EuclideanSpace ℂ (J → Fin 2)) x.property
      (y : EuclideanSpace ℂ (J → Fin 2)) y.property
  let d : ℕ := Module.finrank ℂ S
  let b := hT.eigenvectorBasis (n := d) (by rfl)
  change PositiveOn S O ↔ ∀ μ ∈ eigenvaluesOn S O, 0 < μ.re
  constructor
  · intro hpos μ hμ
    change ∃ ψ ∈ S, ψ ≠ 0 ∧ O ψ = μ • ψ at hμ
    obtain ⟨ψ, hψS, hψne, hO⟩ := hμ
    have hquad : (inner ℂ ψ (O ψ)).re = μ.re * ‖ψ‖ ^ 2 := by
      rw [hO, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
      exact RCLike.re_mul_ofReal μ (‖ψ‖ ^ 2)
    have hnorm : 0 < ‖ψ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hψne)
    have := hpos ψ hψS hψne
    rw [hquad] at this
    nlinarith
  · intro hvals ψ hψS hψne
    let x : S := ⟨ψ, hψS⟩
    have hxne : x ≠ 0 := by
      intro hx
      apply hψne
      exact congrArg Subtype.val hx
    have hlam (i : Fin d) : 0 < hT.eigenvalues (by rfl) i := by
      let lam : ℝ := hT.eigenvalues (by rfl) i
      have hEigen : O (b i : EuclideanSpace ℂ (J → Fin 2)) =
          (lam : ℂ) • (b i : EuclideanSpace ℂ (J → Fin 2)) := by
        have he := hT.apply_eigenvectorBasis (by rfl) i
        have hEq := congrArg (fun z : S => (z : EuclideanSpace ℂ (J → Fin 2))) he
        change O (b i : EuclideanSpace ℂ (J → Fin 2)) =
          ((hT.eigenvalues (by rfl) i : ℝ) : ℂ) • (b i : EuclideanSpace ℂ (J → Fin 2)) at hEq
        simpa [lam] using hEq
      have hBasisNe : (b i : EuclideanSpace ℂ (J → Fin 2)) ≠ 0 := by
        intro hz
        apply (b.orthonormal.ne_zero i)
        exact Subtype.ext hz
      have hEigMem : (lam : ℂ) ∈ eigenvaluesOn S O := by
        change ∃ v ∈ S, v ≠ 0 ∧ O v = (lam : ℂ) • v
        exact ⟨(b i : S), (b i).property, hBasisNe, hEigen⟩
      have h := hvals (lam : ℂ) hEigMem
      simpa [lam] using h
    have hreprne : b.repr x ≠ 0 := by
      intro hz
      apply hxne
      exact b.repr.injective (by simpa using hz)
    obtain ⟨i, hi⟩ : ∃ i : Fin d, b.repr x i ≠ 0 := by
      by_contra h
      have hz : b.repr x = 0 := by
        apply WithLp.ofLp_injective 2
        funext i
        exact not_ne_iff.mp (fun hne => h ⟨i, hne⟩)
      exact hreprne hz
    have hsumpos : 0 < ∑ i : Fin d, hT.eigenvalues (by rfl) i * ‖b.repr x i‖ ^ 2 := by
      apply Finset.sum_pos' (s := Finset.univ)
      · intro j hj
        exact mul_nonneg (le_of_lt (hlam j)) (sq_nonneg _)
      · refine ⟨i, Finset.mem_univ i, ?_⟩
        exact mul_pos (hlam i) (sq_pos_of_pos (norm_pos_iff.mpr hi))
    have hform := AKLT.Vendor.QICLean.OrthonormalBasis.re_inner_apply_eq_sum_of_eigen
      b (hT.eigenvalues (by rfl)) T (fun i => hT.apply_eigenvectorBasis (by rfl) i) x
    have hquad : (inner ℂ ψ (O ψ)).re =
        ∑ i : Fin d, hT.eigenvalues (by rfl) i * ‖b.repr x i‖ ^ 2 := by
      simpa [x, T] using hform
    rw [hquad]
    exact hsumpos

end AKLT.W.H1M040
