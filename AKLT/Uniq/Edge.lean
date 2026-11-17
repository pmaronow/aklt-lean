import AKLT.Uniq.CasimirAction

/-!
The concrete edge lemma of §3.  The normalized polynomial-action identity is
proved in `CasimirAction.lean`; surjectivity is proved by a four-term right
inverse in `Transvectant.lean`.  The range/orthogonality step is proved in
`Casimir.lean`.  There are no unproved leaves in this module.
-/

noncomputable section
open AKLT.Challenge

namespace AKLT.Uniq

/-- Node E: the concrete frozen Casimir projection has the determinant kernel. -/
def EdgeKernelStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    P e v = 0 ↔ singlet e ∣ encode v

/-- Proved assembly of the edge lemma from its two polynomial nodes. -/
theorem edgeKernel_of_nodes (action : CasimirActionStatement)
    (onto : TransvectantSurjectiveStatement) : EdgeKernelStatement := by
  intro L N e v
  rw [projection_eq_zero_iff_range]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨transvectant e (encode w), action L N e w⟩
  · rintro ⟨q, hq⟩
    obtain ⟨w, hw⟩ := onto L N e q (hq ▸ encode_physical v)
    refine ⟨w, encode_injective ?_⟩
    rw [action L N e w, hw]
    exact hq.symm

/-- Assembly using the proved transvectant surjectivity node. -/
theorem edgeKernel_of_action (action : CasimirActionStatement) : EdgeKernelStatement :=
  edgeKernel_of_nodes action transvectantSurjective

theorem edgeKernel : EdgeKernelStatement := edgeKernel_of_action casimirAction

/-- `l:edge`, including the endpoint degree (3,3) and spectator degree four. -/
def EdgeFactorizationStatement : Prop :=
  ∀ L N : Size, ∀ e : Bond L N, ∀ v : Hilbert L N,
    P e v = 0 ↔ ∃ q : SpinorPolynomial L N,
      encode v = singlet e * q ∧ HasSiteDegrees q (edgeResidual e 1)

theorem edgeFactorization : EdgeFactorizationStatement := by
  classical
  intro L N e v
  rw [edgeKernel L N e v]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, hq, ?_⟩
    have hdegree := quotientDegrees L N {e} q (by simpa using hq ▸ encode_physical v)
    intro x
    simpa [edgeResidual, residualDegree] using hdegree x
  · rintro ⟨q, hq, _⟩
    exact ⟨q, hq⟩

#print axioms edgeKernel_of_nodes
#print axioms edgeKernel_of_action
#print axioms edgeKernel
#print axioms edgeFactorization

end AKLT.Uniq
