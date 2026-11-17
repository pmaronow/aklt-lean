module
public import AKLT.W.GAP045.Match

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
namespace AKLT.W.GAP045
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]

/-- Extend prescribed letters on a block to a full configuration. -/
def extendBlock (B : Finset ι) (a : Config S) (b : (x : B) → S x) : Config S :=
  fun x => if hx : x ∈ B then b ⟨x,hx⟩ else a x

lemma restrict_extendBlock (B : Finset ι) (a : Config S) (b : (x : B) → S x) :
    restrict B (extendBlock B a b) = b := by
  funext x
  simp [restrict, extendBlock, x.property]

lemma restrict_eq_agree (B : Finset ι) (a : Config S) (b : (x : B) → S x) (σ : Config S) :
    restrict B σ = b ↔ AgreeOn B σ (extendBlock B a b) := by
  constructor
  · intro h x hx
    have := congrFun h ⟨x,hx⟩
    simpa [restrict, extendBlock, hx] using this
  · intro h
    funext x
    simpa [restrict, extendBlock, x.property] using h x x.property

lemma assignment_mass {p : Weight (Config S)} (hp : PositiveProbability p)
    {α : ℝ} (he : AssignmentBound p α) (A B : Finset ι) (hd : Disjoint A B)
    (a : Config S) (b : (x : B) → S x) :
    α ^ A.card * marginal p (restrict B) b ≤
      eventMass p (fun σ => restrict B σ = b ∧ AgreeOn A σ a) := by
  let ab := extendBlock B a b
  have hpos : 0 < marginal p (restrict B) b := by
    rw [marginal_event]
    exact event_pos_of_atom (fun σ => (hp.1 σ).le) (fun σ => restrict B σ = b)
      ab (restrict_extendBlock B a b) (hp.1 ab)
  have h := he A B hd ab a
  have hn : (fun σ : Config S => AgreeOn B σ ab) = (fun σ => restrict B σ = b) := by
    funext σ
    exact propext (restrict_eq_agree B a b σ).symm
  change α ^ A.card ≤ conditionalProbability p (fun σ => AgreeOn B σ ab)
    (fun σ => AgreeOn A σ a) at h
  rw [hn, conditional_event, ← marginal_event] at h
  exact (le_div_iff₀ hpos).mp h

/-- Direct overlap matching gives a stronger bound with exponent |A|. -/
theorem patch_coupling {p q : Weight (Config S)}
    (hp : PositiveProbability p) (hq : PositiveProbability q)
    (A B : Finset ι) (hd : Disjoint A B) (α t : ℝ) (hα : 0 ≤ α)
    (hep : AssignmentBound p α) (heq : AssignmentBound q α)
    (htv : totalVariation (marginal p (restrict B)) (marginal q (restrict B)) ≤ 1-t) :
    ∃ c : Coupling p q,
      t * α ^ A.card ≤ eventMass (fun z : Config S × Config S => c.mass z.1 z.2)
        (fun z => AgreeOn (A ∪ B) z.1 z.2) := by
  classical
  let a : Config S := Classical.choice inferInstance
  let w : Weight ((x : B) → S x) := fun b =>
    α ^ A.card * min (marginal p (restrict B) b) (marginal q (restrict B) b)
  have hp' : Probability p := ⟨fun x => (hp.1 x).le, hp.2⟩
  have hq' : Probability q := ⟨fun x => (hq.1 x).le, hq.2⟩
  have hw : ∀ b, 0 ≤ w b := fun b => mul_nonneg (pow_nonneg hα _) (le_min
    (marginal_nonnegative hp'.1 _ _) (marginal_nonnegative hq'.1 _ _))
  obtain ⟨c, hc⟩ := match_events hp' hq' (restrict B) (restrict B)
    (fun σ => AgreeOn A σ a) (fun σ => AgreeOn A σ a) w hw
    (fun b => (mul_le_mul_of_nonneg_left (min_le_left _ _) (pow_nonneg hα _)).trans
      (assignment_mass hp hep A B hd a b))
    (fun b => (mul_le_mul_of_nonneg_left (min_le_right _ _) (pow_nonneg hα _)).trans
      (assignment_mass hq heq A B hd a b))
    (fun z => AgreeOn (A ∪ B) z.1 z.2) (by
      intro σ τ hσ hτ hB x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (hσ x hx).trans (hτ x hx).symm
      · exact congrFun hB ⟨x,hx⟩)
  refine ⟨c, le_trans ?_ hc⟩
  have ht : t ≤ ∑ b, min (marginal p (restrict B) b) (marginal q (restrict B) b) := by
    rw [tv_overlap (marginal_probability hp' _) (marginal_probability hq' _)] at htv
    linarith
  dsimp [w]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_right ht (pow_nonneg hα _)).trans_eq (mul_comm _ _)

end AKLT.W.GAP045
