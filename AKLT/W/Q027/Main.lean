module
public import AKLT.Blueprint.Q.NodesPolynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q027

theorem main : AKLT.Blueprint.Q.IncidentKernelStatement := by
  classical
  intro L N x ψ hψ e he
  have hsum :
      (∑ f : Bond L N,
        (inner ℂ ((if x ∈ bondSites f then P f else 0) ψ) ψ).re) = 0 := by
    have hinner := congrArg (fun v : Hilbert L N => (inner ℂ v ψ).re) hψ
    simpa [siteHamiltonian] using hinner
  have hnonneg : ∀ f ∈ (Finset.univ : Finset (Bond L N)),
      0 ≤ (inner ℂ ((if x ∈ bondSites f then P f else 0) ψ) ψ).re := by
    intro f hf
    by_cases hi : x ∈ bondSites f
    · simpa [hi, P] using
        (Submodule.re_inner_starProjection_nonneg (spin4Space f) ψ)
    · simp [hi]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  have hquad : (inner ℂ (P e ψ) ψ).re = 0 := by
    simpa [he] using hzero e (Finset.mem_univ e)
  have hnormSq : ‖(spin4Space e).orthogonalProjectionOnto ψ‖ ^ 2 = 0 := by
    rw [← Submodule.re_inner_starProjection_eq_normSq (spin4Space e) ψ]
    simpa [P] using hquad
  have hproj : (spin4Space e).orthogonalProjectionOnto ψ = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormSq)
  simp [P, Submodule.starProjection_apply, hproj]

end AKLT.W.Q027
