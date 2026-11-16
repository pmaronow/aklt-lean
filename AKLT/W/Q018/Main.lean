import AKLT.Blueprint.Q.NodesStar
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace AKLT.W.Q018

open AKLT.Blueprint.Q

/-- The positive eigenvalues of a finite-dimensional symmetric operator form a
finite nonempty set, so its infimum is a positive eigenvalue and its minimum. -/
theorem main : AKLT.Blueprint.Q.PositiveSpectralMinimumStatement := by
  classical
  intro ι _ T hT hpos hwitness
  let n : ℕ := Fintype.card ι
  have hn : Module.finrank ℂ (EuclideanSpace ℂ ι) = n := by
    simp [n]
  let eval : Fin n → ℝ := hT.eigenvalues hn
  let S : Set ℝ := {μ | 0 < μ ∧ T.HasEigenvalue (μ : ℂ)}
  have hfinite : S.Finite := by
    apply (Set.finite_range eval).subset
    intro μ hμ
    obtain ⟨i, hi⟩ := hT.exists_eigenvalues_eq hn hμ.2
    refine ⟨i, ?_⟩
    have := congrArg Complex.re hi
    simpa [eval] using this
  have hnonempty : S.Nonempty := by
    rcases hwitness with ⟨μ, hμpos, hμeig⟩
    exact ⟨μ, hμpos, hμeig⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro μ hμ
    exact le_of_lt hμ.1
  obtain ⟨g, hgmem, hgminimal⟩ := hfinite.exists_minimal hnonempty
  have hleast : ∀ μ ∈ S, g ≤ μ := by
    intro μ hμ
    by_contra hnot
    have hlt : μ < g := lt_of_not_ge hnot
    exact (not_le_of_gt hlt) (hgminimal hμ hlt.le)
  have hinf : sInf S = g := by
    apply le_antisymm
    · exact csInf_le hbdd hgmem
    · exact le_csInf hnonempty hleast
  rw [show (sInf S : ℝ) = g from hinf]
  have hgmem' : 0 < g ∧ T.HasEigenvalue (g : ℂ) := by
    simpa [S] using hgmem
  refine ⟨hgmem'.1, hgmem'.2, ?_⟩
  intro μ hμpos hμeig
  exact hleast μ ⟨hμpos, hμeig⟩

end AKLT.W.Q018
