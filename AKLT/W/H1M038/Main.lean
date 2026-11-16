import AKLT.Blueprint.H1.NodesSector

noncomputable section

open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M038

theorem main : AKLT.Blueprint.H1.CommonWeightEigenvectorStatement := by
  classical
  intro J S O hOinv hOself hZinv hZself hcomm μ hμ
  change ∃ ψ ∈ S, ψ ≠ 0 ∧ O ψ = μ • ψ at hμ
  rcases hμ with ⟨ψ, hψS, hψ0, hOψ⟩
  let E : Submodule ℂ (AKLT.Blueprint.H1.TensorSpace J) :=
    S ⊓ Module.End.eigenspace O μ
  have hψE : ψ ∈ E := by
    change ψ ∈ S ∧ ψ ∈ Module.End.eigenspace O μ
    exact ⟨hψS, Module.End.mem_eigenspace_iff.mpr hOψ⟩
  have hEinv : ∀ x ∈ E, totalSpinZ J x ∈ E := by
    intro x hx
    change totalSpinZ J x ∈ S ∧ totalSpinZ J x ∈ Module.End.eigenspace O μ
    refine ⟨hZinv x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
    calc
      O (totalSpinZ J x) = totalSpinZ J (O x) := hcomm x hx.1
      _ = totalSpinZ J (μ • x) := congrArg (totalSpinZ J) (Module.End.mem_eigenspace_iff.mp hx.2)
      _ = μ • totalSpinZ J x := map_smul (totalSpinZ J) μ x
  let Z_E : Module.End ℂ E := (totalSpinZ J).restrict hEinv
  have hZ_E_symm : @LinearMap.IsSymmetric ℂ E _ _ _ Z_E := by
    intro x y
    change inner ℂ (totalSpinZ J (x : AKLT.Blueprint.H1.TensorSpace J))
        (y : AKLT.Blueprint.H1.TensorSpace J) =
      inner ℂ (x : AKLT.Blueprint.H1.TensorSpace J)
        (totalSpinZ J (y : AKLT.Blueprint.H1.TensorSpace J))
    exact hZself x.1 x.2.1 y.1 y.2.1
  have hEpos : 0 < Module.finrank ℂ E := by
    by_contra h
    have hz : Module.finrank ℂ E = 0 := Nat.eq_zero_of_not_pos h
    have hall : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hz
    exact hψ0 (by
      have : (⟨ψ, hψE⟩ : E) = 0 := hall ⟨ψ, hψE⟩
      exact congrArg Subtype.val this)
  let n : ℕ := Module.finrank ℂ E
  have hn : Module.finrank ℂ E = n := rfl
  let i : Fin n := ⟨0, by simpa [n] using hEpos⟩
  let v : E := hZ_E_symm.eigenvectorBasis hn i
  have hv_ne : v ≠ 0 := (hZ_E_symm.eigenvectorBasis hn).orthonormal.ne_zero i
  have hvZ_E : Z_E v =
      ((hZ_E_symm.eigenvalues hn i : ℝ) : ℂ) • v :=
    hZ_E_symm.apply_eigenvectorBasis hn i
  refine ⟨v.1, v.2.1, ?_, ?_, ?_⟩
  · intro hv
    apply hv_ne
    exact Subtype.ext hv
  · exact Module.End.mem_eigenspace_iff.mp v.2.2
  · refine ⟨hZ_E_symm.eigenvalues hn i, ?_⟩
    have hvZ := congrArg (fun x : E => (x : AKLT.Blueprint.H1.TensorSpace J)) hvZ_E
    simpa [Z_E, LinearMap.restrict_apply] using hvZ

end AKLT.W.H1M038
