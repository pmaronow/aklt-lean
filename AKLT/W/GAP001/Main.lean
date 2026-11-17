module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP001

theorem main : AKLT.Blueprint.Gap.FiberNormalizationStatement := by
  classical
  intro ι hι hιdec S hS hSnonempty p hp U σ
  let E : Config S → Prop := fun τ => AgreeOutside U σ τ
  let w : Config S → ℝ := fun τ => if E τ then p τ else 0
  let Z : ℝ := ∑ τ, w τ
  have hσE : E σ := by
    intro x hx
    rfl
  have hZpos : 0 < Z := by
    have hterm : 0 < w σ := by
      simp [w, E, hσE, hp.1]
    have hle : w σ ≤ ∑ τ, w τ := by
      apply Finset.single_le_sum (fun τ hτ => by
        by_cases h : E τ
        · exact le_of_lt (by simpa [w, h] using hp.1 τ)
        · simp [w, h]) (Finset.mem_univ σ)
    dsimp [Z]
    exact lt_of_lt_of_le hterm hle
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hfiber : fiber p U σ = fun τ => w τ / Z := by
    funext τ
    simp [fiber, conditionOn, AKLT.Defs.normalize, w, Z, E]
  have hprob : Probability (fiber p U σ) := by
    rw [hfiber]
    constructor
    · intro τ
      apply div_nonneg
      · by_cases h : E τ
        · simp [w, h, le_of_lt (hp.1 τ)]
        · simp [w, h]
      · exact le_of_lt hZpos
    · calc
        (∑ τ, w τ / Z) = (∑ τ, w τ) / Z := by rw [Finset.sum_div]
        _ = 1 := by simp [Z, hZne]
  refine ⟨hprob, ?_, ?_⟩
  · change (∀ b, 0 < ∑ τ, if restrict U τ = b then fiber p U σ τ else 0) ∧
      (∑ b, ∑ τ, if restrict U τ = b then fiber p U σ τ else 0) = 1
    constructor
    · intro b
      let τ₀ : Config S := fun x => if hx : x ∈ U then b ⟨x, hx⟩ else σ x
      have hrestrict : restrict U τ₀ = b := by
        funext x
        simp [restrict, τ₀]
      have hτ₀E : E τ₀ := by
        intro x hx
        simp [τ₀, hx]
      have hterm : 0 < if restrict U τ₀ = b then fiber p U σ τ₀ else 0 := by
        simp only [hrestrict, eq_self, ite_true]
        rw [hfiber]
        change 0 < w τ₀ / Z
        have : w τ₀ = p τ₀ := by simp [w, hτ₀E]
        rw [this]
        exact div_pos (hp.1 τ₀) hZpos
      have hsum_nonneg : ∀ τ ∈ (Finset.univ : Finset (Config S)),
          0 ≤ if restrict U τ = b then fiber p U σ τ else 0 := by
        intro τ hτ
        by_cases h : restrict U τ = b
        · simpa [h] using (hprob.1 τ)
        · simp [h]
      have hle : (if restrict U τ₀ = b then fiber p U σ τ₀ else 0) ≤
          ∑ τ, if restrict U τ = b then fiber p U σ τ else 0 := by
        apply Finset.single_le_sum hsum_nonneg (Finset.mem_univ τ₀)
      change 0 < ∑ τ, if restrict U τ = b then fiber p U σ τ else 0
      exact lt_of_lt_of_le hterm hle
    · calc
        (∑ b, ∑ τ, if restrict U τ = b then fiber p U σ τ else 0) =
            ∑ τ, ∑ b, if restrict U τ = b then fiber p U σ τ else 0 := by
              rw [Finset.sum_comm]
        _ = ∑ τ, fiber p U σ τ := by
              apply Finset.sum_congr rfl
              intro τ hτ
              simp
        _ = 1 := hprob.2
  · intro f
    let N : ℂ := ∑ τ, if E τ then (p τ : ℂ) * f τ else 0
    let D : ℂ := ∑ τ, if E τ then (p τ : ℂ) else 0
    have hD : D = (Z : ℂ) := by
      dsimp [D, Z, w, E]
      calc
        (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) else 0) =
            ∑ τ, ((if AgreeOutside U σ τ then p τ else 0 : ℝ) : ℂ) := by
              apply Finset.sum_congr rfl
              intro τ hτ
              by_cases h : AgreeOutside U σ τ <;> simp [h]
        _ = (∑ τ, if AgreeOutside U σ τ then p τ else 0 : ℝ) := by
              norm_cast
    have hmean : complexMean (fiber p U σ) f = N / (Z : ℂ) := by
      rw [hfiber]
      dsimp [complexMean, N]
      calc
        (∑ τ, (((w τ / Z : ℝ) : ℂ) * f τ)) =
            ∑ τ, (if E τ then (p τ : ℂ) * f τ else 0) / (Z : ℂ) := by
              apply Finset.sum_congr rfl
              intro τ hτ
              by_cases h : E τ
              · have hzc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZne
                simp [w, h, Complex.ofReal_div]
                field_simp [hzc]
              · simp [w, h]
        _ = N / (Z : ℂ) := by rw [Finset.sum_div]
    change N / D = complexMean (fiber p U σ) f
    rw [hD, hmean]

end AKLT.W.GAP001
