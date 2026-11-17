module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP025

private theorem agreeOutside_singleton_transport
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : ι → Type} {T : κ → Type} (e : ProductChange S T)
    (σ τ : Config S) (x : ι) :
    AgreeOutside ({x} : Finset ι) σ τ ↔
      AgreeOutside ({e.sites x} : Finset κ) (e.configurations σ) (e.configurations τ) := by
  constructor
  · intro h y hy
    let z : ι := e.sites.symm y
    have hz : z ≠ x := by
      intro hzx
      have hy' : y ≠ e.sites x := by simpa using hy
      apply hy'
      calc
        y = e.sites (e.sites.symm y) := (e.sites.apply_symm_apply y).symm
        _ = e.sites x := congrArg e.sites hzx
    have heq : σ z = τ z := h z (by simpa [z] using hz)
    have hyz : e.sites z = y := by
      dsimp [z]
      exact e.sites.apply_symm_apply y
    have hcoord := (e.coordinate_eq σ τ z).mp heq
    rw [hyz] at hcoord
    exact hcoord
  · intro h z hz
    have hy : e.sites z ≠ e.sites x := by
      simpa using hz
    have heq := h (e.sites z) (by simpa using hy)
    exact (e.coordinate_eq σ τ z).mpr heq

private theorem complexMean_transport
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : ι → Type} {T : κ → Type}
    [∀ x, Fintype (S x)] [∀ y, Fintype (T y)]
    (e : ProductChange S T) (p : Weight (Config S)) (q : Weight (Config T))
    (hcarry : Carries e p q) (f : Config S → ℂ) :
    complexMean q (fun τ => f (e.configurations.symm τ)) = complexMean p f := by
  classical
  unfold complexMean
  apply Fintype.sum_equiv e.configurations.symm
  intro τ
  have hq : q τ = p (e.configurations.symm τ) := by
    simpa using hcarry (e.configurations.symm τ)
  rw [hq]

private theorem conditionalExpectation_transport
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : ι → Type} {T : κ → Type}
    [∀ x, Fintype (S x)] [∀ y, Fintype (T y)]
    (e : ProductChange S T) (p : Weight (Config S)) (q : Weight (Config T))
    (hcarry : Carries e p q) (f : Config S → ℂ) (x : ι) (σ : Config S) :
    conditionalExpectation q ({e.sites x} : Finset κ)
        (fun τ => f (e.configurations.symm τ)) (e.configurations σ) =
      conditionalExpectation p ({x} : Finset ι) f σ := by
  classical
  unfold conditionalExpectation
  have hnum :
      (∑ τ, if AgreeOutside ({e.sites x} : Finset κ) (e.configurations σ) τ then
          (q τ : ℂ) * f (e.configurations.symm τ) else 0) =
        ∑ ρ, if AgreeOutside ({x} : Finset ι) σ ρ then
          (p ρ : ℂ) * f ρ else 0 := by
    apply Fintype.sum_equiv e.configurations.symm
    intro τ
    have hagree := agreeOutside_singleton_transport e σ (e.configurations.symm τ) x
    have hagree' :
        AgreeOutside ({e.sites x} : Finset κ) (e.configurations σ) τ ↔
          AgreeOutside ({x} : Finset ι) σ (e.configurations.symm τ) := by
      simpa using hagree.symm
    have hq : q τ = p (e.configurations.symm τ) := by
      simpa using hcarry (e.configurations.symm τ)
    simp only [hagree', hq]
  have hden :
      (∑ τ, if AgreeOutside ({e.sites x} : Finset κ) (e.configurations σ) τ then
          (q τ : ℂ) else 0) =
        ∑ ρ, if AgreeOutside ({x} : Finset ι) σ ρ then
          (p ρ : ℂ) else 0 := by
    apply Fintype.sum_equiv e.configurations.symm
    intro τ
    have hagree := agreeOutside_singleton_transport e σ (e.configurations.symm τ) x
    have hagree' :
        AgreeOutside ({e.sites x} : Finset κ) (e.configurations σ) τ ↔
          AgreeOutside ({x} : Finset ι) σ (e.configurations.symm τ) := by
      simpa using hagree.symm
    have hq : q τ = p (e.configurations.symm τ) := by
      simpa using hcarry (e.configurations.symm τ)
    simp only [hagree', hq]
  rw [hnum, hden]

private theorem variance_transport
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : ι → Type} {T : κ → Type}
    [∀ x, Fintype (S x)] [∀ y, Fintype (T y)]
    (e : ProductChange S T) (p : Weight (Config S)) (q : Weight (Config T))
    (hcarry : Carries e p q) (f : Config S → ℂ) :
    variance q (fun τ => f (e.configurations.symm τ)) = variance p f := by
  classical
  unfold variance
  rw [complexMean_transport e p q hcarry f]
  apply Fintype.sum_equiv e.configurations.symm
  intro τ
  have hq : q τ = p (e.configurations.symm τ) := by
    simpa using hcarry (e.configurations.symm τ)
  rw [hq]

private theorem blockDirichlet_transport
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : ι → Type} {T : κ → Type}
    [∀ x, Fintype (S x)] [∀ y, Fintype (T y)]
    (e : ProductChange S T) (p : Weight (Config S)) (q : Weight (Config T))
    (hcarry : Carries e p q) (f : Config S → ℂ) (x : ι) :
    blockDirichlet q ({e.sites x} : Finset κ) (fun τ => f (e.configurations.symm τ)) =
      blockDirichlet p ({x} : Finset ι) f := by
  classical
  unfold blockDirichlet
  apply Fintype.sum_equiv e.configurations.symm
  intro τ
  have hq : q τ = p (e.configurations.symm τ) := by
    simpa using hcarry (e.configurations.symm τ)
  have hce := conditionalExpectation_transport e p q hcarry f x (e.configurations.symm τ)
  have hce' :
      conditionalExpectation q ({e.sites x} : Finset κ)
          (fun τ => f (e.configurations.symm τ)) τ =
        conditionalExpectation p ({x} : Finset ι) f (e.configurations.symm τ) := by
    simpa using hce
  rw [hq, hce']

private theorem dirichlet_transport
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {S : ι → Type} {T : κ → Type}
    [∀ x, Fintype (S x)] [∀ y, Fintype (T y)]
    (e : ProductChange S T) (p : Weight (Config S)) (q : Weight (Config T))
    (hcarry : Carries e p q) (f : Config S → ℂ) :
    dirichlet q (fun τ => f (e.configurations.symm τ)) = dirichlet p f := by
  classical
  unfold dirichlet
  symm
  apply Fintype.sum_equiv e.sites
  intro x
  exact (blockDirichlet_transport e p q hcarry f x).symm

theorem main : ProductPoincareTransportStatement := by
  intro ι κ instι instEqι instκ instEqκ S T instS instT e p q hcarry g hg
  classical
  intro f
  let f' : Config T → ℂ := fun τ => f (e.configurations.symm τ)
  have hineq := hg f'
  have hvar := variance_transport e p q hcarry f
  have hdir := dirichlet_transport e p q hcarry f
  simpa [f', hvar, hdir] using hineq

end AKLT.W.GAP025
