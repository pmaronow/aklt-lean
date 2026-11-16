import AKLT.Blueprint.Win.NodesCut

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN071

theorem main : AKLT.Blueprint.Win.OverlapMinorizationStatement := by
  intro Ω hF p q ν hp hq hν p₀ hp₀ hpn hqn
  classical
  have hpoint : ∀ s : Ω, |p s - q s| ≤ p s + q s - 2 * (p₀ * ν s) := by
    intro s
    by_cases hpq : p s ≤ q s
    · rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
      linarith [hpn s]
    · have hqp : q s ≤ p s := le_of_not_ge hpq
      rw [abs_of_nonneg (sub_nonneg.mpr hqp)]
      linarith [hqn s]
  have hsum : (∑ s : Ω, |p s - q s|) ≤ 2 - 2 * p₀ := by
    calc
      (∑ s : Ω, |p s - q s|) ≤
          ∑ s : Ω, (p s + q s - 2 * (p₀ * ν s)) :=
        Finset.sum_le_sum fun s _ => hpoint s
      _ = (∑ s : Ω, p s) + (∑ s : Ω, q s) -
          2 * p₀ * (∑ s : Ω, ν s) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        ring
      _ = 2 - 2 * p₀ := by rw [hp.2, hq.2, hν.2]; ring
  change (1 / 2 : ℝ) * (∑ s : Ω, |p s - q s|) ≤ 1 - p₀
  nlinarith

end AKLT.W.WIN071

#print axioms AKLT.W.WIN071.main
