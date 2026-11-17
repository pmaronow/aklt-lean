import AKLT.Blueprint.Gap.NodesPeriodic

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP037

local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- Insert a block assignment into a product configuration with a fixed exterior. -/
def insertBlock {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι)
    (σ : Config S) (ω : (x : U) → S x) : Config S :=
  fun x => if hx : x ∈ U then ω ⟨x, hx⟩ else σ x

@[simp] theorem insertBlock_inside {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) (σ : Config S) (ω : (x : U) → S x) (x : U) :
    insertBlock U σ ω x = ω x := by simp [insertBlock]

@[simp] theorem restrict_insertBlock {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) (σ : Config S) (ω : (x : U) → S x) :
    restrict U (insertBlock U σ ω) = ω := by funext x; simp [restrict]

theorem insertBlock_agrees {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) (σ : Config S) (ω : (x : U) → S x) :
    AgreeOutside U σ (insertBlock U σ ω) := by
  intro x hx
  simp [insertBlock, hx]

theorem insertBlock_restrict {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) (σ τ : Config S) (h : AgreeOutside U σ τ) :
    insertBlock U σ (restrict U τ) = τ := by
  funext x
  by_cases hx : x ∈ U
  · simp [insertBlock, restrict, hx]
  · simp [insertBlock, hx, h x hx]

/-- Reindex the exterior fibre by its free coordinates. -/
theorem sum_insertBlock {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (U : Finset ι) (σ : Config S) (f : Config S → ℝ) :
    (∑ τ, if AgreeOutside U σ τ then f τ else 0) = ∑ ω, f (insertBlock U σ ω) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun τ _ => restrict U τ)
  · intro τ hτ; exact Finset.mem_univ _
  · intro τ hτ υ hυ heq
    have ht := insertBlock_restrict U σ τ (Finset.mem_filter.mp hτ).2
    have hu := insertBlock_restrict U σ υ (Finset.mem_filter.mp hυ).2
    rw [← ht, ← hu, heq]
  · intro ω hω
    exact ⟨insertBlock U σ ω, by simp [insertBlock_agrees], restrict_insertBlock U σ ω⟩
  · intro τ hτ
    rw [insertBlock_restrict U σ τ (Finset.mem_filter.mp hτ).2]

/-- The conditional block marginal is the normalized weight on its fibre. -/
theorem blockLaw_formula {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (σ : Config S) (ω : (x : U) → S x) :
    blockLaw p U σ ω = normalize (fun ρ => p (insertBlock U σ ρ)) ω := by
  classical
  change (∑ τ, if restrict U τ = ω then
    (if AgreeOutside U σ τ then p τ else 0) /
      (∑ υ, if AgreeOutside U σ υ then p υ else 0) else 0) = _
  have hd (P : Prop) [Decidable P] (a b : ℝ) : (if P then a / b else 0) = (if P then a else 0) / b := by
    split_ifs <;> simp
  simp_rw [hd]
  rw [← Finset.sum_div, sum_insertBlock]
  have hn : (∑ τ, if restrict U τ = ω then
      (if AgreeOutside U σ τ then p τ else 0) else 0) = p (insertBlock U σ ω) := by
    have heq : ∀ τ, (if restrict U τ = ω then
        (if AgreeOutside U σ τ then p τ else 0) else 0) =
        if AgreeOutside U σ τ then (if restrict U τ = ω then p τ else 0) else 0 := by
      intro τ
      split_ifs <;> rfl
    simp_rw [heq]
    rw [sum_insertBlock]
    simp
  rw [hn]
  rfl

private theorem paritySign_add_one (n : ℤ) :
    (if Even (n + 1) then (1 : ℝ) else -1) =
      -(if Even n then (1 : ℝ) else -1) := by
  by_cases h : Even n <;> simp [h]

/-- Adjacent lifted plane sites have opposite gauge signs. -/
theorem paritySign_adjacent (x y : Plane) (h : Adjacent x y) :
    paritySign x = - paritySign y := by
  have hd : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := h
  rcases Nat.add_eq_one_iff.mp hd with ⟨hx0, hy1⟩ | ⟨hx1, hy0⟩
  · have hxd : x.1 - y.1 = 0 := Int.natAbs_eq_zero.mp hx0
    rcases Int.natAbs_eq_iff.mp hy1 with hyd | hyd
    · have hs : x.1 + x.2 = y.1 + y.2 + 1 := by omega
      unfold paritySign
      rw [hs, paritySign_add_one]
      try ring
    · have hs : y.1 + y.2 = x.1 + x.2 + 1 := by omega
      unfold paritySign
      rw [hs, paritySign_add_one]
      try ring
  · have hyd0 : x.2 - y.2 = 0 := Int.natAbs_eq_zero.mp hy0
    rcases Int.natAbs_eq_iff.mp hx1 with hxd | hxd
    · have hs : x.1 + x.2 = y.1 + y.2 + 1 := by omega
      unfold paritySign
      rw [hs, paritySign_add_one]
      try ring
    · have hs : y.1 + y.2 = x.1 + x.2 + 1 := by omega
      unfold paritySign
      rw [hs, paritySign_add_one]
      try ring

/-- Rescaling all weights by one nonzero constant commutes with normalization,
including when the underlying weight has zero total mass. -/
theorem normalize_rescale_equiv {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (f : Ω → ℝ) (g : Ξ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (h : ∀ x, f x = c * g (e x)) (x : Ω) :
    normalize f x = normalize g (e x) := by
  have hs : (∑ y, f y) = c * ∑ z, g z := by
    calc
      (∑ y, f y) = ∑ y, c * g (e y) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact h y
      _ = c * ∑ y, g (e y) := by rw [Finset.mul_sum]
      _ = c * ∑ z, g z := by rw [Equiv.sum_comp e g]
  unfold AKLT.Defs.normalize
  rw [hs]
  rw [h x]
  field_simp [hc]

/-- Conditioning also removes the global normalizer, when it is nonzero. -/
theorem blockLaw_normalize_formula {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (w : Weight (Config S))
    (hw : (∑ τ, w τ) ≠ 0) (U : Finset ι) (σ : Config S) (ω : (x : U) → S x) :
    blockLaw (normalize w) U σ ω = normalize (fun ρ => w (insertBlock U σ ρ)) ω := by
  rw [blockLaw_formula]
  apply normalize_rescale_equiv (Equiv.refl _) _ _ (∑ τ, w τ)⁻¹ (inv_ne_zero hw)
  intro ρ
  simp [AKLT.Defs.normalize, div_eq_mul_inv, mul_comm]

theorem dot_comm (u v : Vec3) : dot u v = dot v u := by
  simp only [dot, mul_comm]

theorem dot_smul (r s : ℝ) (u v : Vec3) :
    dot (r • u) (s • v) = r*s*dot u v := by
  change (∑ i, (r*u i)*(s*v i)) = r*s*(∑ i, u i*v i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dot_gauge {x y : Plane} (h : Adjacent x y) (u v : Vec3) :
    dot (paritySign x • u) (paritySign y • v) = -dot u v := by
  have hy : paritySign y * paritySign y = 1 := by
    unfold paritySign
    split_ifs <;> norm_num
  rw [dot_smul, paritySign_adjacent x y h]
  calc
    -paritySign y * paritySign y * dot u v = -(paritySign y * paritySign y) * dot u v := by ring
    _ = -dot u v := by rw [hy]; ring

end AKLT.W.GAP037
