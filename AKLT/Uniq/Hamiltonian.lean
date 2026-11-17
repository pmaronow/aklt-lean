module
public import AKLT.Challenge.Sanity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! The kernel of the sum of the frozen orthogonal bond projections. -/

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

theorem h_energy (L N : Size) (v : Hilbert L N) :
    (inner ℂ (H L N v) v).re = ∑ e : Bond L N, ‖P e v‖ ^ 2 := by
  classical
  simp only [H, LinearMap.sum_apply, sum_inner, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro e _
  simpa only [P, ContinuousLinearMap.coe_coe, Submodule.starProjection_apply,
    RCLike.re_eq_complex_re,
    Submodule.norm_coe] using (spin4Space e).re_inner_starProjection_eq_normSq v

/-- Node H1: no cancellation between positive bond energies. -/
def HamiltonianKernelStatement : Prop :=
  ∀ L N : Size, ∀ v : Hilbert L N, H L N v = 0 ↔ ∀ e : Bond L N, P e v = 0

theorem hamiltonianKernel : HamiltonianKernelStatement := by
  classical
  intro L N v
  constructor
  · intro hv e
    have hsum : ∑ f : Bond L N, ‖P f v‖ ^ 2 = 0 := by
      rw [← h_energy, hv, inner_zero_left]
      rfl
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun f (_ : f ∈ (Finset.univ : Finset (Bond L N))) => sq_nonneg ‖P f v‖)).mp
      hsum e (Finset.mem_univ e)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  · intro hv
    simp [H, LinearMap.sum_apply, hv]

#print axioms h_energy
#print axioms hamiltonianKernel

end AKLT.Uniq
