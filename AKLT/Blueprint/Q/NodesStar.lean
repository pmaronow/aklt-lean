module
public import AKLT.Blueprint.Q.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

/-- `l:star`, sec3 lines 235–236: every summand is an orthogonal projection.
Self-adjointness and positivity are separate from existence of positive spectrum. -/
def StarPositiveStatement : Prop :=
  starHamiltonian.IsSymmetric ∧ ∀ ψ : StarHilbert, 0 ≤ (inner ℂ ψ (starHamiltonian ψ)).re

/-- `l:star`, lines 236–240: the all-extremal-weight tensor is fixed by all
four projectors and has eigenvalue four. This prevents an empty positive spectrum. -/
def StarWitnessStatement : Prop := starHamiltonian.HasEigenvalue (4 : ℂ)

/-- `l:star`, lines 240–241: a finite-dimensional positive symmetric operator
with a positive eigenvalue has a positive attained minimum. Identify the
infimum definition, including its lower-boundedness premise. -/
def PositiveSpectralMinimumStatement : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ T : Module.End ℂ (EuclideanSpace ℂ ι),
    T.IsSymmetric → (∀ ψ, 0 ≤ (inner ℂ ψ (T ψ)).re) →
    (∃ μ : ℝ, 0 < μ ∧ T.HasEigenvalue (μ : ℂ)) →
    let g := sInf {μ : ℝ | 0 < μ ∧ T.HasEigenvalue (μ : ℂ)}
    0 < g ∧ T.HasEigenvalue (g : ℂ) ∧
      ∀ μ : ℝ, 0 < μ → T.HasEigenvalue (μ : ℂ) → g ≤ μ

/-- `l:star`, lines 242–243: expand in an orthonormal eigenbasis and remove
the zero eigenspace. This lemma is independent of the AKLT matrix size. -/
def SpectralKernelCoercivityStatement : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ T : Module.End ℂ (EuclideanSpace ℂ ι),
    T.IsSymmetric → (∀ ψ, 0 ≤ (inner ℂ ψ (T ψ)).re) →
    ∀ g : ℝ, 0 < g →
      (∀ μ : ℝ, 0 < μ → T.HasEigenvalue (μ : ℂ) → g ≤ μ) → kernelCoercivity T g

/-- `l:star`, lines 245–249: a coordinate permutation identifies an incident
torus star with independent copies of the fixed five-site star. Prove the
five sites distinct using periods >=3, also when either period equals three. -/
def StarRelabellingStatement : Prop :=
  ∀ L N : Size, ∀ x : Site L N,
    ∃ n : ℕ, ∃ U : Hilbert L N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5)),
      amplifiesStar (siteHamiltonian x) n U

/-- `l:star`, lines 249–250: tensor/amplification transports the kernel
coercivity inequality. Sum the fixed-star inequalities over spectator
configurations and conjugate the kernel projection by the isometry. -/
def StarAmplificationStatement : Prop :=
  ∀ (ι : Type) [Fintype ι], ∀ T : Module.End ℂ (EuclideanSpace ℂ ι),
    ∀ n : ℕ, ∀ U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5)),
      amplifiesStar T n U → ∀ g : ℝ, kernelCoercivity starHamiltonian g → kernelCoercivity T g

/-- `l:star`, lines 250–252: count an edge at its two distinct endpoints.
The sole geometric premise is explicit and supplied by `p:toruskernel`. -/
def IncidentDoubleCountStatement : Prop :=
  ∀ L N : Size, (∀ e : Bond L N, (bondSites e).card = 2) →
    (∑ x : Site L N, siteHamiltonian x) = 2 • H L N

theorem incidentDoubleCount : IncidentDoubleCountStatement := by
  classical
  intro L N hcard
  unfold siteHamiltonian
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter]
  have hf : ∀ e : Bond L N, Finset.univ.filter (fun x => x ∈ bondSites e) = bondSites e := by
    intro e
    ext x
    simp
  simp_rw [hf, Finset.sum_const, hcard]
  simp [H, Finset.smul_sum]

end AKLT.Blueprint.Q
