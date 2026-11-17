module
public import AKLT.Uniq.Edge

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
Closed blueprint nodes for §3 (`d:poly`, `l:edge`, `l:divisibility`,
`p:toruskernel`).  All polynomial, torus and positivity nodes imported above
are proved, as are the concrete edge nodes.  The assembly theorems expose the
dependencies explicitly; `Main.lean` supplies their proved inhabitants.
-/

noncomputable section
open scoped BigOperators
open AKLT.Challenge

namespace AKLT.Uniq

/-- The exact first conjunct of `MainStatementV2`, using only frozen objects. -/
def UniquenessStatement : Prop :=
  ∀ L N : Size, B L N ≠ 0 ∧
    LinearMap.ker (H L N) = Submodule.span ℂ {B L N}

/-- Assembly from the edge node, with all polynomial and torus nodes discharged. -/
theorem uniqueness_of_edge (edge : EdgeKernelStatement) :
    ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
      LinearMap.ker (AKLT.Challenge.H L N) =
        Submodule.span ℂ {AKLT.Challenge.B L N} := by
  intro L N
  refine ⟨B_ne_zero L N, ?_⟩
  have hB : H L N (B L N) = 0 := by
    apply (hamiltonianKernel L N (B L N)).mpr
    intro e
    apply (edge L N e (B L N)).mpr
    rw [encode_B]
    exact Finset.dvd_prod_of_mem singlet (Finset.mem_univ e)
  apply le_antisymm
  · intro v hv
    have hvb : vbsPolynomial L N ∣ encode v := by
      apply vbsPolynomial_dvd
      intro e
      exact (edge L N e v).mp ((hamiltonianKernel L N v).mp hv e)
    obtain ⟨c, hc⟩ := scalarQuotient L N (encode v) (encode_physical v)
      (vbsDegree L N).2 (vbsDegree L N).1 hvb
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, encode_injective ?_⟩
    rw [map_smul, encode_B]
    exact hc.symm
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    exact hB

/-- `l:divisibility` with the physical operators, conditional only on the edge node. -/
def LocalDivisibilityStatement : Prop :=
  ∀ L N : Size, ∀ R : Finset (Site L N), ∀ v : Hilbert L N,
    (∀ e ∈ incidentBonds R, P e v = 0) →
    ∃ q : SpinorPolynomial L N,
      encode v = (∏ e ∈ incidentBonds R, singlet e) * q ∧ IndependentOn R q

theorem localDivisibility_of_edge (edge : EdgeKernelStatement) :
    LocalDivisibilityStatement := by
  intro L N R v hv
  exact polynomialLocalDivisibility L N R (encode v) (encode_physical v)
    (fun e he => (edge L N e v).mp (hv e he))

/-- Assembly directly from the two proved polynomial nodes. -/
theorem uniqueness_of_polynomial_nodes (action : CasimirActionStatement)
    (onto : TransvectantSurjectiveStatement) : UniquenessStatement :=
  uniqueness_of_edge (edgeKernel_of_nodes action onto)

/-- Assembly using the Casimir-action node and the proved transvectant node. -/
theorem uniqueness_of_nodes (action : CasimirActionStatement) :
    ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
      LinearMap.ker (AKLT.Challenge.H L N) =
        Submodule.span ℂ {AKLT.Challenge.B L N} :=
  uniqueness_of_edge (edgeKernel_of_action action)

theorem localDivisibility : LocalDivisibilityStatement := localDivisibility_of_edge edgeKernel

#print axioms uniqueness_of_nodes
#print axioms uniqueness_of_edge
#print axioms localDivisibility_of_edge
#print axioms uniqueness_of_polynomial_nodes
#print axioms localDivisibility

end AKLT.Uniq
