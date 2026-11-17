module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators Pointwise
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP022

private lemma adjacent_eq_all
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (f : Config S → ℝ)
    (hstep : ∀ σ τ, hamming σ τ = 1 → f σ = f τ) :
    ∀ σ τ, f σ = f τ := by
  classical
  intro σ τ
  let aux : ∀ D : Finset ι, ∀ σ τ : Config S,
      (∀ x, x ∉ D → σ x = τ x) → f σ = f τ := by
    intro D
    induction D using Finset.induction with
    | empty =>
        intro σ τ hagree
        have hστ : σ = τ := funext fun x => hagree x (by simp)
        rw [hστ]
    | @insert x D hx ih =>
        intro σ τ hagree
        let ρ : Config S := Function.update σ x (τ x)
        have hleft : f σ = f ρ := by
          by_cases hval : σ x = τ x
          · have hρ : σ = ρ := by
              funext y
              by_cases hy : y = x
              · subst y
                simp [ρ, hval]
              · simp [ρ, hy]
            rw [hρ]
          · have hfilter : Finset.univ.filter (fun y => σ y ≠ ρ y) = {x} := by
              ext y
              simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_singleton]
              by_cases hy : y = x
              · subst y
                simp [ρ, hval]
              · simp [ρ, hy]
            have hdist : hamming σ ρ = 1 := by
              simp [hamming, hfilter]
            exact hstep σ ρ hdist
        have hρagree : ∀ y, y ∉ D → ρ y = τ y := by
          intro y hy
          by_cases hyx : y = x
          · subst y
            simp [ρ]
          · have hyInsert : y ∉ insert x D := by
              simp [Finset.mem_insert, hyx, hy]
            calc
              ρ y = σ y := by simp [ρ, hyx]
              _ = τ y := hagree y hyInsert
        exact hleft.trans (ih ρ τ hρagree)
  exact aux Finset.univ σ τ (fun x hx => by simp at hx)

private lemma edgeValues_bddAbove
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)]
    (f : Config S → ℝ) :
    BddAbove (insert 0 {r : ℝ | ∃ σ τ : Config S,
      hamming σ τ = 1 ∧ r = |f σ - f τ|}) := by
  classical
  let M : ℝ := 2 * ∑ σ : Config S, |f σ|
  have hsum_nonneg : 0 ≤ ∑ σ : Config S, |f σ| :=
    Finset.sum_nonneg fun σ _ => abs_nonneg (f σ)
  have hsingle (σ : Config S) : |f σ| ≤ ∑ τ : Config S, |f τ| :=
    Finset.single_le_sum (fun τ _ => abs_nonneg (f τ)) (Finset.mem_univ σ)
  refine ⟨M, ?_⟩
  intro r hr
  rcases Set.mem_insert_iff.mp hr with hzero | hedge
  · rw [hzero]
    dsimp [M]
    positivity
  · rcases hedge with ⟨σ, τ, _, rfl⟩
    have habs : |f σ - f τ| ≤ |f σ| + |f τ| := by
      simpa [abs_neg] using abs_sub_le (f σ) 0 (f τ)
    dsimp [M]
    calc
      |f σ - f τ| ≤ |f σ| + |f τ| := habs
      _ ≤ (∑ x : Config S, |f x|) + ∑ x : Config S, |f x| :=
        add_le_add (hsingle σ) (hsingle τ)
      _ = 2 * ∑ x : Config S, |f x| := by ring

private lemma lipschitz_smul
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)]
    (f : Config S → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    lipschitz (fun σ => a * f σ) = a * lipschitz f := by
  classical
  let E (g : Config S → ℝ) : Set ℝ :=
    insert 0 {r | ∃ σ τ : Config S, hamming σ τ = 1 ∧ r = |g σ - g τ|}
  have hmul (x y : ℝ) : |a * x - a * y| = a * |x - y| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg ha]
  have hE : E (fun σ => a * f σ) = a • E f := by
    ext r
    simp only [E, Set.mem_insert_iff, Set.mem_smul_set, Set.mem_ofPred_eq]
    constructor
    · rintro (hr | ⟨σ, τ, hdist, rfl⟩)
      · refine ⟨0, Or.inl rfl, ?_⟩
        simpa using hr.symm
      · refine ⟨|f σ - f τ|, Or.inr ⟨σ, τ, hdist, rfl⟩, ?_⟩
        simpa [smul_eq_mul] using (hmul (f σ) (f τ)).symm
    · rintro ⟨s, hs, hrs⟩
      · rcases hs with hs | ⟨σ, τ, hdist, rfl⟩
        · left
          simpa [hs] using hrs.symm
        · right
          refine ⟨σ, τ, hdist, ?_⟩
          calc
            _ = a * |f σ - f τ| := by simpa [smul_eq_mul] using hrs.symm
            _ = |a * f σ - a * f τ| := (hmul _ _).symm
  change sSup (E (fun σ => a * f σ)) = a * sSup (E f)
  rw [hE, Real.sSup_smul_of_nonneg ha]
  simp [smul_eq_mul]

end AKLT.W.GAP022

namespace AKLT.W.GAP022

theorem main : AKLT.Blueprint.Gap.LipschitzEigenvalueStatement := by
  classical
  unfold AKLT.Blueprint.Gap.LipschitzEigenvalueStatement
  intro ι _ _ S _ hS p K hp r hr hcontract f eigenvalue hmean hnonzero heigen
  have hnotConst : ¬ ∃ c, ∀ σ : Config S, f σ = c := by
    rintro ⟨c, hc⟩
    have hmeanC : expectation p f = c := by
      unfold expectation
      calc
        (∑ σ, p σ * f σ) = ∑ σ, p σ * c := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [hc σ]
        _ = (∑ σ, p σ) * c := by rw [Finset.sum_mul]
        _ = c := by rw [hp.2]; ring
    obtain ⟨σ, hσ⟩ := hnonzero
    have hc0 : c = 0 := by linarith [hmeanC]
    exact hσ (by rw [hc σ, hc0])
  have hedge : ∃ σ τ : Config S, hamming σ τ = 1 ∧ f σ ≠ f τ := by
    by_contra h
    have hstep : ∀ σ τ : Config S, hamming σ τ = 1 → f σ = f τ := by
      intro σ τ hd
      by_contra hne
      exact h ⟨σ, τ, hd, hne⟩
    have hall := adjacent_eq_all S f hstep
    let σ₀ : Config S := fun x => Classical.choice (hS x)
    exact hnotConst ⟨f σ₀, fun σ => (hall σ σ₀).trans rfl⟩
  obtain ⟨σ, τ, hdist, hdiff⟩ := hedge
  have hBdd := edgeValues_bddAbove f
  have hmem : |f σ - f τ| ∈
      insert 0 {v : ℝ | ∃ σ' τ' : Config S,
        hamming σ' τ' = 1 ∧ v = |f σ' - f τ'|} := by
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
    right
    exact ⟨σ, τ, hdist, rfl⟩
  have hedgeLe : |f σ - f τ| ≤ lipschitz f := by
    unfold lipschitz
    exact le_csSup hBdd hmem
  have hLipPos : 0 < lipschitz f :=
    lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hdiff)) hedgeLe
  by_cases hLam : eigenvalue ≤ 0
  · exact hLam.trans hr
  · have hLamPos : 0 < eigenvalue := lt_of_not_ge hLam
    have hscale := lipschitz_smul f eigenvalue (le_of_lt hLamPos)
    have heq : lipschitz (fun σ => eigenvalue * f σ) =
        lipschitz (kernelMean K f) := by
      congr 1
      funext σ
      exact (heigen σ).symm
    have hbound : eigenvalue * lipschitz f ≤ r * lipschitz f := by
      calc
        eigenvalue * lipschitz f = lipschitz (fun σ => eigenvalue * f σ) := hscale.symm
        _ = lipschitz (kernelMean K f) := heq
        _ ≤ r * lipschitz f := hcontract f
    exact le_of_mul_le_mul_right hbound hLipPos

#print axioms main

end AKLT.W.GAP022
