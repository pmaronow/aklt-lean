import AKLT.Blueprint.Gap.NodesFinite

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP009

private theorem fibre_stationary
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p)
    (U : Finset ι) (σ : Config S) :
    ∑ a, p a * fibre p U a σ = p σ := by
  classical
  let Z : ℝ := ∑ x, if AgreeOutside U σ x then p x else 0
  have hZlower : p σ ≤ Z := by
    dsimp [Z]
    calc
      p σ = if AgreeOutside U σ σ then p σ else 0 := by simp [AgreeOutside]
      _ ≤ ∑ x, if AgreeOutside U σ x then p x else 0 := by
        have hle := Finset.single_le_sum
          (s := Finset.univ)
          (f := fun x => if AgreeOutside U σ x then p x else 0)
          (fun x hx => by
            split_ifs
            · exact le_of_lt (hp.1 x)
            · exact le_rfl)
          (Finset.mem_univ σ)
        simpa [AgreeOutside] using hle
  have hZpos : 0 < Z := lt_of_lt_of_le (hp.1 σ) hZlower
  have hden (a : Config S) (ha : AgreeOutside U a σ) :
      (∑ x, if AgreeOutside U a x then p x else 0) = Z := by
    dsimp [Z]
    apply Finset.sum_congr rfl
    intro x hx
    have hiff : AgreeOutside U a x ↔ AgreeOutside U σ x := by
      constructor
      · intro h z hz
        calc
          σ z = a z := (ha z hz).symm
          _ = x z := h z hz
      · intro h z hz
        calc
          a z = σ z := ha z hz
          _ = x z := h z hz
    simp [hiff]
  have houter :
      (∑ a, if AgreeOutside U a σ then p a else 0) = Z := by
    dsimp [Z]
    apply Finset.sum_congr rfl
    intro a ha
    have hiff : AgreeOutside U a σ ↔ AgreeOutside U σ a := by
      constructor <;> intro h z hz
      · exact (h z hz).symm
      · exact (h z hz).symm
    simp [hiff]
  change ∑ a, p a *
    ((if AgreeOutside U a σ then p σ else 0) /
      ∑ x, if AgreeOutside U a x then p x else 0) = p σ
  calc
    ∑ a, p a *
        ((if AgreeOutside U a σ then p σ else 0) /
          ∑ x, if AgreeOutside U a x then p x else 0)
      = ∑ a, (p σ / Z) * (if AgreeOutside U a σ then p a else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases h : AgreeOutside U a σ
          · simp [h, hden a h, mul_comm]
          · simp [h]
    _ = (p σ / Z) * ∑ a, if AgreeOutside U a σ then p a else 0 := by
          rw [Finset.mul_sum]
    _ = (p σ / Z) * Z := by rw [houter]
    _ = p σ := by
          field_simp [ne_of_gt hZpos]

theorem main : AKLT.Blueprint.Gap.SurgeryPreservationStatement := by
  classical
  intro ι hι hdec S hS hSn p q hp hq U c R
  let d : Coupling p q := {
    mass := fun σ τ => ∑ a, ∑ b, c.mass a b * (R a b).mass σ τ
    nonnegative := by
      intro σ τ
      apply Finset.sum_nonneg
      intro a ha
      apply Finset.sum_nonneg
      intro b hb
      exact mul_nonneg (c.nonnegative a b) ((R a b).nonnegative σ τ)
    first_marginal := by
      intro σ
      calc
        ∑ τ, ∑ a, ∑ b, c.mass a b * (R a b).mass σ τ
          = ∑ a, ∑ τ, ∑ b, c.mass a b * (R a b).mass σ τ := Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ τ, c.mass a b * (R a b).mass σ τ := by
              apply Finset.sum_congr rfl
              intro a ha
              exact Finset.sum_comm
        _ = ∑ a, ∑ b, c.mass a b * ∑ τ, (R a b).mass σ τ := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              rw [← Finset.mul_sum]
        _ = ∑ a, ∑ b, c.mass a b * fibre p U a σ := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              rw [(R a b).first_marginal]
        _ = ∑ a, (∑ b, c.mass a b) * fibre p U a σ := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [← Finset.sum_mul]
        _ = ∑ a, p a * fibre p U a σ := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [c.first_marginal a]
        _ = p σ := fibre_stationary S p hp U σ
    second_marginal := by
      intro τ
      calc
        ∑ σ, ∑ a, ∑ b, c.mass a b * (R a b).mass σ τ
          = ∑ a, ∑ σ, ∑ b, c.mass a b * (R a b).mass σ τ := Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ σ, c.mass a b * (R a b).mass σ τ := by
              apply Finset.sum_congr rfl
              intro a ha
              exact Finset.sum_comm
        _ = ∑ b, ∑ a, ∑ σ, c.mass a b * (R a b).mass σ τ := Finset.sum_comm
        _ = ∑ b, ∑ a, c.mass a b * ∑ σ, (R a b).mass σ τ := by
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro a ha
              rw [← Finset.mul_sum]
        _ = ∑ b, ∑ a, c.mass a b * fibre q U b τ := by
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro a ha
              rw [(R a b).second_marginal]
        _ = ∑ b, (∑ a, c.mass a b) * fibre q U b τ := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [← Finset.sum_mul]
        _ = ∑ b, q b * fibre q U b τ := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [c.second_marginal b]
        _ = q τ := fibre_stationary S q hq U τ
  }
  exact ⟨d, by intro σ τ; rfl⟩

end AKLT.W.GAP009
