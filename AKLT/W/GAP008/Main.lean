module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP008

/-- A shared subprobability mass bounds the total variation distance. -/
theorem main : AKLT.Blueprint.Gap.CommonMinorizationStatement := by
  classical
  intro Ω hΩ p q ν hp hq hν t ht0 ht1 hminor
  have hpoint : ∀ x, |p x - q x| ≤ (p x - t * ν x) + (q x - t * ν x) := by
    intro x
    have hp' := hminor x |>.1
    have hq' := hminor x |>.2
    rw [abs_le]
    constructor <;> nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  have hpSum : ∑ x, p x = 1 := hp.2
  have hqSum : ∑ x, q x = 1 := hq.2
  have hνSum : ∑ x, ν x = 1 := hν.2
  have hscaled : (∑ x, t * ν x) = t := by
    rw [← Finset.mul_sum, hνSum]
    ring
  have hsum' : (∑ x, |p x - q x|) ≤ 2 * (1 - t) := by
    calc
      (∑ x, |p x - q x|) ≤ ∑ x, ((p x - t * ν x) + (q x - t * ν x)) := hsum
      _ = 2 * (1 - t) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hpSum, hqSum, hscaled]
        ring
  unfold totalVariation
  nlinarith

end AKLT.W.GAP008
