module
public import AKLT.W.GAP046.TraceHelpers

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP046


theorem main : AKLT.Blueprint.Gap.TraceMarginalsStatement := by
  intro P hP a y u l h p α η ξ R
  classical
  let Ω := PlaneConfig P (square a u)
  let μ : Weight Ω := P.law (square a u) η
  let ν : Weight Ω := P.law (square a u) ξ
  let initial : Weight (Ω × Ω) :=
    independentPairs (P.law (square a u) η) (P.law (square a u) ξ)
  let endpoint : Weight (Ω × Ω) :=
    traceEndpoint h
      (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel
  have hμpos : PositiveProbability μ := hP.1 (square a u) η
  have hνpos : PositiveProbability ν := hP.1 (square a u) ξ
  have hμprob : Probability μ := ⟨fun x => (hμpos.1 x).le, hμpos.2⟩
  have hνprob : Probability ν := ⟨fun x => (hνpos.1 x).le, hνpos.2⟩
  have hInitial : Probability initial := by
    exact independentPairProbability μ ν hμprob hνprob
  have hEndMarg := surgeryTrace_endpoint_marginals P a y u l h p α η ξ R hμpos hνpos
  have hTraceProbRaw : Probability (traceLaw h
      (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel) :=
    traceLaw_probability h
      (independentPairs (P.law (square a u) η) (P.law (square a u) ξ))
      R.kernel hInitial R.stochastic
  have hTraceProb : Probability (surgeryTrace P a y u l h p α η ξ R) := by
    exact hTraceProbRaw
  have hEndpointProb : Probability endpoint := by
    dsimp [endpoint]
    exact traceEndpoint_probability h
      (independentPairs (P.law (square a u) η) (P.law (square a u) ξ))
      R.kernel hTraceProbRaw
  have hEndpointEq : endpoint = marginal (surgeryTrace P a y u l h p α η ξ R)
      (fun t => t (Fin.last h)) := by
    dsimp [endpoint, traceEndpoint]
    rw [← surgeryTrace_eq_traceLaw P a y u l h p α η ξ R]
  let c : Coupling μ ν := {
    mass := fun σ τ => endpoint (σ, τ)
    nonnegative := fun σ τ => hEndpointProb.1 (σ, τ)
    first_marginal := hEndMarg.1
    second_marginal := hEndMarg.2 }
  refine ⟨hTraceProb, ?_⟩
  refine ⟨c, ?_⟩
  intro σ τ
  calc
    c.mass σ τ = endpoint (σ, τ) := rfl
    _ = marginal (surgeryTrace P a y u l h p α η ξ R)
        (fun t => t (Fin.last h)) (σ, τ) := by
      exact congrArg (fun w => w (σ, τ)) hEndpointEq

end AKLT.W.GAP046
