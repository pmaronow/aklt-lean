import AKLT.W.GAP014.Product

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP014

local instance (α : Type) : DecidableEq α := Classical.decEq α

private theorem signed_edge_bounds
    {ι : Type} (b : ℝ) (κ : ι → Fin 3) (E : Finset (ι × ι))
    (positiveSign : ι × ι → Bool) (σ : ι → IcoLetter)
    (hcolor : ∀ e ∈ E, κ e.1 ≠ κ e.2)
    (hbnd : ∀ i j : Fin 3, i ≠ j → ∀ a c : IcoLetter,
      b ≤ 1 + dot (frameVector i a) (frameVector j c) ∧
      1 + dot (frameVector i a) (frameVector j c) ≤ 2-b ∧
      b ≤ 1 - dot (frameVector i a) (frameVector j c) ∧
      1 - dot (frameVector i a) (frameVector j c) ≤ 2-b) :
    ∀ e ∈ E, b ≤ (if positiveSign e then
      1 + dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
      else 1 - dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))) ∧
      (if positiveSign e then
        1 + dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
        else 1 - dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))) ≤ 2-b := by
  intro e he
  have hh := hbnd (κ e.1) (κ e.2) (hcolor e he) (σ e.1) (σ e.2)
  by_cases hs : positiveSign e <;> simp [hs] at * <;> tauto

/-- Signed frame interactions on any finite block have the one-ratio gap bound. -/
theorem main :
    AKLT.Blueprint.Gap.SignedFrameBlockStatement := by
  classical
  intro hb hb1 hbnds ι hι hdec κ E hcolor positiveSign h hpos
  let π : (x : ι) → Weight IcoLetter := fun x a => h x a / ∑ c, h x c
  let q : (ι → IcoLetter) → ℝ := fun σ => ∏ x, π x (σ x)
  let ψ : (ι → IcoLetter) → ℝ := fun σ =>
    ∏ e ∈ E, if positiveSign e then
      1 + dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
    else 1 - dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
  let w : (ι → IcoLetter) → ℝ := fun σ => (∏ x, h x (σ x)) * ψ σ
  let H : ι → ℝ := fun x => ∑ a, h x a
  let C : ℝ := ∏ x, H x
  let lo : ℝ := frameBound ^ E.card
  let hi : ℝ := (2-frameBound) ^ E.card
  let Z : ℝ := expectation q ψ
  have hHpos : ∀ x, 0 < H x := by
    intro x
    dsimp [H]
    apply Finset.sum_pos'
    · intro a ha
      exact (hpos x a).le
    · exact ⟨(0, 0, 0), Finset.mem_univ _, hpos x (0, 0, 0)⟩
  have hπ : ∀ x, PositiveProbability (π x) := by
    intro x
    constructor
    · intro a
      dsimp [π]
      exact div_pos (hpos x a) (hHpos x)
    · dsimp [π, H]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (hHpos x))
  have hq : PositiveProbability q := by
    exact productWeight_probability π hπ
  have hEdge : ∀ (σ : ι → IcoLetter) (e : ι × ι), e ∈ E →
      frameBound ≤ (if positiveSign e then
        1 + dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
        else 1 - dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))) ∧
      (if positiveSign e then
        1 + dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
        else 1 - dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))) ≤ 2-frameBound := by
    intro σ e he
    exact signed_edge_bounds frameBound κ E positiveSign σ hcolor hbnds e he
  have hψbounds : ∀ σ, lo ≤ ψ σ ∧ ψ σ ≤ hi := by
    intro σ
    constructor
    · dsimp [lo, ψ]
      calc
        frameBound ^ E.card = ∏ e ∈ E, frameBound := by simp
        _ ≤ ∏ e ∈ E, (if positiveSign e then
            1 + dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
            else 1 - dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))) :=
          Finset.prod_le_prod₀ (fun e he => le_of_lt hb)
            (fun e he => (hEdge σ e he).1)
    · dsimp [hi, ψ]
      calc
        ∏ e ∈ E, (if positiveSign e then
            1 + dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2))
            else 1 - dot (frameVector (κ e.1) (σ e.1)) (frameVector (κ e.2) (σ e.2)))
            ≤ ∏ e ∈ E, (2-frameBound) :=
          Finset.prod_le_prod₀
            (fun e he => le_trans (le_of_lt hb) (hEdge σ e he).1)
            (fun e he => (hEdge σ e he).2)
        _ = (2-frameBound) ^ E.card := by simp
  have hlo : 0 < lo := by
    dsimp [lo]
    exact pow_pos hb _
  have hhi : 0 < hi := by
    dsimp [hi]
    exact pow_pos (by linarith : 0 < 2-frameBound) _
  have hψpos : ∀ σ, 0 < ψ σ := by
    intro σ
    exact lt_of_lt_of_le hlo (hψbounds σ).1
  have hCpos : 0 < C := by
    dsimp [C]
    exact Finset.prod_pos fun x hx => hHpos x
  have hraw : ∀ σ, (∏ x, h x (σ x)) = C * q σ := by
    intro σ
    dsimp [C, q, π, H]
    rw [Finset.prod_div_distrib]
    have hden : (∏ x, ∑ a, h x a) ≠ 0 := by
      exact ne_of_gt (Finset.prod_pos fun x hx => hHpos x)
    field_simp [hden]
  have hZpos : 0 < Z := by
    dsimp [Z, expectation, q]
    apply Finset.sum_pos'
    · intro σ hσ
      exact mul_nonneg (le_of_lt (Finset.prod_pos fun x hx => (hπ x).1 (σ x)))
        (le_of_lt (hψpos σ))
    · exact ⟨fun _ => (0, 0, 0), Finset.mem_univ _,
        mul_pos (Finset.prod_pos fun x hx => (hπ x).1 ((fun _ => (0, 0, 0)) x))
          (hψpos (fun _ => (0, 0, 0)))⟩
  have hsum : (∑ σ, w σ) = C * Z := by
    dsimp [w, Z, expectation]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [hraw σ]
    ring
  have hμeq : ∀ σ, AKLT.Defs.normalize w σ = q σ * ψ σ / Z := by
    intro σ
    rw [AKLT.Defs.normalize, hsum]
    dsimp [w]
    rw [hraw σ]
    field_simp [hCpos.ne', hZpos.ne']
  have hμ : PositiveProbability (AKLT.Defs.normalize w) := by
    constructor
    · intro σ
      rw [hμeq σ]
      exact div_pos (mul_pos (hq.1 σ) (hψpos σ)) hZpos
    · calc
        (∑ σ, AKLT.Defs.normalize w σ) = ∑ σ, q σ * ψ σ / Z := by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hμeq σ
        _ = 1 := by
          rw [← Finset.sum_div]
          have hzsum : Z = ∑ σ, q σ * ψ σ := by rfl
          rw [← hzsum]
          exact div_self hZpos.ne'
  have hloD : 0 < lo / Z := div_pos hlo hZpos
  have hhiD : 0 < hi / Z := div_pos hhi hZpos
  have hpoint : ∀ σ, (lo / Z) * q σ ≤ AKLT.Defs.normalize w σ ∧
      AKLT.Defs.normalize w σ ≤ (hi / Z) * q σ := by
    intro σ
    rw [hμeq σ]
    constructor
    · calc
        (lo / Z) * q σ = (lo * q σ) / Z := by ring
        _ ≤ (q σ * ψ σ) / Z := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hZpos)
          calc
            lo * q σ = q σ * lo := by ring
            _ ≤ q σ * ψ σ := mul_le_mul_of_nonneg_left (hψbounds σ).1 (le_of_lt (hq.1 σ))
        _ = q σ * ψ σ / Z := by ring
    · calc
        q σ * ψ σ / Z ≤ (hi * q σ) / Z := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hZpos)
          calc
            q σ * ψ σ ≤ q σ * hi := mul_le_mul_of_nonneg_left (hψbounds σ).2 (le_of_lt (hq.1 σ))
            _ = hi * q σ := by ring
        _ = (hi / Z) * q σ := by ring
  have hprodGap : PoincareLower q 1 := product_gap π hπ
  have hboundGap := density_comparison q (AKLT.Defs.normalize w) hq hμ hprodGap
    (lo/Z) (hi/Z) hloD hhiD hpoint
  have hratio : lo / Z / (hi / Z) = frameRatio ^ E.card := by
    calc
      lo / Z / (hi / Z) = lo / hi := by
        field_simp [hZpos.ne', (ne_of_gt hhi)]
      _ = (frameBound / (2-frameBound)) ^ E.card := by
        dsimp [lo, hi]
        rw [← div_pow]
      _ = frameRatio ^ E.card := by rfl
  change PoincareLower (AKLT.Defs.normalize w) (frameRatio ^ E.card)
  intro f
  have hf := hboundGap f
  rw [hratio] at hf
  exact hf

end AKLT.W.GAP014

#print axioms AKLT.W.GAP014.main
