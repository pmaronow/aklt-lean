module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP021

local instance (α : Type) : DecidableEq α := Classical.decEq α

private def edgeOscillation {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : Config S → ℝ) : Set ℝ :=
  {r | ∃ σ τ : Config S, hamming σ τ = 1 ∧ r = |f σ - f τ|}

private lemma edgeOscillation_finite {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : Config S → ℝ) :
    (edgeOscillation f).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun p : Config S × Config S => |f p.1 - f p.2|))
  rintro r ⟨σ, τ, hστ, rfl⟩
  exact ⟨(σ, τ), rfl⟩

private lemma lipschitz_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : Config S → ℝ) : 0 ≤ lipschitz f := by
  unfold lipschitz
  have hbdd : BddAbove (insert 0 (edgeOscillation f)) :=
    (edgeOscillation_finite f).insert 0 |>.bddAbove
  apply le_csSup hbdd
  simp

private lemma edge_le_lipschitz {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : Config S → ℝ)
    {σ τ : Config S} (hστ : hamming σ τ = 1) :
    |f σ - f τ| ≤ lipschitz f := by
  unfold lipschitz
  have hbdd : BddAbove (insert 0 (edgeOscillation f)) :=
    (edgeOscillation_finite f).insert 0 |>.bddAbove
  apply le_csSup hbdd
  exact Or.inr ⟨σ, τ, hστ, rfl⟩

private def along {ι : Type} {S : ι → Type} (σ τ : Config S) (U : Finset ι) : Config S :=
  fun x => if x ∈ U then τ x else σ x

private lemma hamming_zero_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} (σ τ : Config S) (h : hamming σ τ = 0) : σ = τ := by
  classical
  apply funext
  intro x
  by_contra hx
  have hxmem : x ∈ Finset.univ.filter (fun y => σ y ≠ τ y) := by
    simp [hx]
  have hcard : (Finset.univ.filter (fun y => σ y ≠ τ y)).card = 0 := h
  have hempty := Finset.card_eq_zero.mp hcard
  rw [hempty] at hxmem
  simp at hxmem

private lemma hamming_le_one_of_eq_outside {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} (σ τ : Config S) (x : ι)
    (h : ∀ y, y ≠ x → σ y = τ y) : hamming σ τ ≤ 1 := by
  classical
  unfold hamming
  let D := Finset.univ.filter (fun y => σ y ≠ τ y)
  have hsub : D ⊆ {x} := by
    intro y hy
    have hy' : σ y ≠ τ y := (Finset.mem_filter.mp hy).2
    apply Finset.mem_singleton.mpr
    by_contra hne
    exact hy' (h y hne)
  exact le_trans (Finset.card_le_card hsub) (by simp [D])

private lemma edge_or_equal_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : Config S → ℝ)
    (L : ℝ) (hL : lipschitz f ≤ L) {σ τ : Config S}
    (hστ : hamming σ τ ≤ 1) : |f σ - f τ| ≤ L := by
  by_cases hz : hamming σ τ = 0
  · have heq := hamming_zero_eq σ τ hz
    have hnonneg : 0 ≤ L := (lipschitz_nonneg f).trans hL
    simpa [heq] using hnonneg
  · have hone : hamming σ τ = 1 := by omega
    exact (edge_le_lipschitz f hone).trans hL

private lemma along_path_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : Config S → ℝ)
    (σ τ : Config S) (U : Finset ι)
    (hU : ∀ x ∈ U, σ x ≠ τ x) :
    |f (along σ τ U) - f σ| ≤ lipschitz f * (U.card : ℝ) := by
  classical
  revert hU
  induction U using Finset.induction_on with
  | empty =>
      intro hU
      have heq : along σ τ ∅ = σ := by
        funext y
        simp [along]
      rw [heq]
      simp
  | @insert x U hx ih =>
      intro hU
      have hU' : ∀ y ∈ U, σ y ≠ τ y := by
        intro y hy
        exact hU y (Finset.mem_insert_of_mem hy)
      have hstep : ∀ y, y ≠ x → along σ τ U y = along σ τ (insert x U) y := by
        intro y hy
        by_cases hyU : y ∈ U <;> simp [along, hyU, hx, hy, hy.symm]
      have hham : hamming (along σ τ U) (along σ τ (insert x U)) ≤ 1 :=
        hamming_le_one_of_eq_outside _ _ x hstep
      have hstepBound :
          |f (along σ τ (insert x U)) - f (along σ τ U)| ≤ lipschitz f := by
        have htmp := edge_or_equal_bound f (lipschitz f) (le_refl _) hham
        simpa [abs_sub_comm] using htmp
      have hL : 0 ≤ lipschitz f := lipschitz_nonneg f
      calc
        |f (along σ τ (insert x U)) - f σ|
            ≤ |f (along σ τ (insert x U)) - f (along σ τ U)| +
                |f (along σ τ U) - f σ| := abs_sub_le _ _ _
        _ ≤ lipschitz f + lipschitz f * (U.card : ℝ) := add_le_add hstepBound (ih hU')
        _ = lipschitz f * ((insert x U).card : ℝ) := by simp [hx]; ring

private lemma global_lipschitz_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (f : Config S → ℝ)
    (σ τ : Config S) :
    |f σ - f τ| ≤ lipschitz f * (hamming σ τ : ℝ) := by
  classical
  let D : Finset ι := Finset.univ.filter (fun x => σ x ≠ τ x)
  have hD : ∀ x ∈ D, σ x ≠ τ x := by
    intro x hx
    simpa [D] using hx
  have hend : along σ τ D = τ := by
    funext x
    by_cases hx : x ∈ D
    · simp [along, hx]
    · have heq : σ x = τ x := by
        by_contra hne
        exact hx (by simp [D, hne])
      simp [along, hx, heq]
  have hpath := along_path_bound f σ τ D hD
  rw [hend] at hpath
  simpa [D, hamming, abs_sub_comm] using hpath

private lemma expectation_difference_coupling {Ω : Type} [Fintype Ω]
    (p q : Weight Ω) (c : Coupling p q) (f : Ω → ℝ) :
    expectation p f - expectation q f =
      ∑ x, ∑ y, c.mass x y * (f x - f y) := by
  classical
  have hp : expectation p f = ∑ x, ∑ y, c.mass x y * f x := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro x hx
    rw [← c.first_marginal x, Finset.sum_mul]
  have hq : expectation q f = ∑ x, ∑ y, c.mass x y * f y := by
    unfold expectation
    calc
      (∑ y, q y * f y) = ∑ y, ∑ x, c.mass x y * f y := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [← c.second_marginal y, Finset.sum_mul]
      _ = ∑ x, ∑ y, c.mass x y * f y := by rw [Finset.sum_comm]
  rw [hp, hq]
  calc
    (∑ x, ∑ y, c.mass x y * f x) - (∑ x, ∑ y, c.mass x y * f y)
        = ∑ x, ((∑ y, c.mass x y * f x) - (∑ y, c.mass x y * f y)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ x, ∑ y, c.mass x y * (f x - f y) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.sum_sub_distrib (s := Finset.univ)
            (f := fun y => c.mass x y * f x) (g := fun y => c.mass x y * f y)]
          apply Finset.sum_congr rfl
          intro y hy
          ring

private lemma expectation_difference_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)]
    {p q : Weight (Config S)} (c : Coupling p q) (f : Config S → ℝ)
    (L : ℝ) (hL : lipschitz f ≤ L)
    (hLip : ∀ σ τ, |f σ - f τ| ≤ L * (hamming σ τ : ℝ)) :
    |expectation p f - expectation q f| ≤ L * couplingCost c := by
  classical
  rw [expectation_difference_coupling p q c f]
  calc
    |∑ x, ∑ y, c.mass x y * (f x - f y)|
        ≤ ∑ x, ∑ y, |c.mass x y * (f x - f y)| := by
            calc
              |∑ x, ∑ y, c.mass x y * (f x - f y)|
                  ≤ ∑ x, |∑ y, c.mass x y * (f x - f y)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ x, ∑ y, |c.mass x y * (f x - f y)| := by
                  apply Finset.sum_le_sum
                  intro x hx
                  exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ∑ y, L * (c.mass x y * (hamming x y : ℝ)) := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          have hm := c.nonnegative x y
          calc
            |c.mass x y * (f x - f y)| = c.mass x y * |f x - f y| := by
              rw [abs_mul, abs_of_nonneg hm]
            _ ≤ c.mass x y * (L * (hamming x y : ℝ)) :=
              mul_le_mul_of_nonneg_left (hLip x y) hm
            _ = L * (c.mass x y * (hamming x y : ℝ)) := by ring
    _ = L * couplingCost c := by
          rw [couplingCost]
          simp_rw [← Finset.mul_sum]

private lemma lipschitz_kernelMean_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (K : Config S → Weight (Config S)) (f : Config S → ℝ)
    (hK : ∀ σ, Probability (K σ)) (r : ℝ) (hr : 0 ≤ r)
    (hcouple : ∀ σ τ, hamming σ τ = 1 →
      ∃ c : Coupling (K σ) (K τ), couplingCost c ≤ r) :
    lipschitz (kernelMean K f) ≤ r * lipschitz f := by
  classical
  apply csSup_le
  · exact ⟨0, by simp⟩
  · intro z hz
    rcases hz with rfl | hz
    · exact mul_nonneg hr (lipschitz_nonneg f)
    · rcases hz with ⟨σ, τ, hστ, rfl⟩
      obtain ⟨c, hc⟩ := hcouple σ τ hστ
      have hdiff := expectation_difference_bound c f (lipschitz f) (le_refl _)
        (global_lipschitz_bound f)
      have hcost :
          |kernelMean K f σ - kernelMean K f τ| ≤ lipschitz f * couplingCost c := by
        simpa [kernelMean] using hdiff
      have horder := mul_le_mul_of_nonneg_left hc (lipschitz_nonneg f)
      simpa [mul_comm] using hcost.trans horder

theorem main : AKLT.Blueprint.Gap.LipschitzCouplingStatement := by
  intro ι _ _ S _ _ K hK r hr hcouple f
  exact lipschitz_kernelMean_bound K f hK r hr hcouple

#print axioms main

end AKLT.W.GAP021
