module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open scoped BigOperators
open AKLT.Blueprint.Gap AKLT.Defs

namespace AKLT.W.GAP026

private theorem configuration_hamming
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : ι → Type} {T : κ → Type} [∀ x, Fintype (S x)] [∀ y, Fintype (T y)]
    (e : ProductChange S T) (σ τ : Config S) :
    hamming (e.configurations σ) (e.configurations τ) = hamming σ τ := by
  classical
  unfold hamming
  symm
  apply Finset.card_bij (fun x _ => e.sites x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact fun hEq => hx ((e.coordinate_eq σ τ x).mpr hEq)
  · intro x hx y hy hxy
    exact e.sites.injective hxy
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨e.sites.symm y, ?_, e.sites.apply_symm_apply y⟩
    intro hEq
    apply hy
    have hEq' := (e.coordinate_eq σ τ (e.sites.symm y)).mp hEq
    rw [e.sites.apply_symm_apply] at hEq'
    exact hEq'

theorem main : AKLT.Blueprint.Gap.ProductCouplingTransportStatement := by
  classical
  intro ι κ _ _ _ _ S T _ _ e p p' q q' hp hp' c
  let d : Coupling p p' := {
    mass := fun σ τ => c.mass (e.configurations σ) (e.configurations τ)
    nonnegative := by
      intro σ τ
      exact c.nonnegative _ _
    first_marginal := by
      intro σ
      calc
        (∑ τ : Config S, c.mass (e.configurations σ) (e.configurations τ))
            = ∑ υ : Config T, c.mass (e.configurations σ) υ := by
                exact Equiv.sum_comp e.configurations _
        _ = q (e.configurations σ) := c.first_marginal _
        _ = p σ := hp σ
    second_marginal := by
      intro τ
      calc
        (∑ σ : Config S, c.mass (e.configurations σ) (e.configurations τ))
            = ∑ υ : Config T, c.mass υ (e.configurations τ) := by
                exact Equiv.sum_comp e.configurations (fun υ : Config T => c.mass υ (e.configurations τ))
        _ = q' (e.configurations τ) := c.second_marginal _
        _ = p' τ := hp' τ
  }
  refine ⟨d, ?_⟩
  unfold couplingCost
  change (∑ σ : Config S, ∑ τ : Config S,
      c.mass (e.configurations σ) (e.configurations τ) * (hamming σ τ : ℝ)) =
    ∑ ω : Config T, ∑ υ : Config T,
      c.mass ω υ * (hamming ω υ : ℝ)
  calc
    (∑ σ : Config S, ∑ τ : Config S,
        c.mass (e.configurations σ) (e.configurations τ) * (hamming σ τ : ℝ))
        = ∑ σ : Config S, ∑ υ : Config T,
            c.mass (e.configurations σ) υ * (hamming (e.configurations σ) υ : ℝ) := by
              apply Finset.sum_congr rfl
              intro σ _
              calc
                (∑ τ : Config S, c.mass (e.configurations σ) (e.configurations τ) *
                    (hamming σ τ : ℝ))
                    = ∑ τ : Config S, c.mass (e.configurations σ) (e.configurations τ) *
                        (hamming (e.configurations σ) (e.configurations τ) : ℝ) := by
                          apply Finset.sum_congr rfl
                          intro τ _
                          rw [configuration_hamming]
                _ = ∑ υ : Config T, c.mass (e.configurations σ) υ *
                    (hamming (e.configurations σ) υ : ℝ) := Equiv.sum_comp e.configurations (fun υ : Config T =>
                        c.mass (e.configurations σ) υ * (hamming (e.configurations σ) υ : ℝ))
    _ = ∑ ω : Config T, ∑ υ : Config T, c.mass ω υ * (hamming ω υ : ℝ) :=
      Equiv.sum_comp e.configurations (fun ω : Config T =>
        ∑ υ : Config T, c.mass ω υ * (hamming ω υ : ℝ))

#print axioms main

end AKLT.W.GAP026
