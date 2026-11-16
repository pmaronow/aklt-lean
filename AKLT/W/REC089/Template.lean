import AKLT.W.REC089.Disintegration
import AKLT.W.REC089.Tips

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

def tipPoint : Fin 4 → Plane := ![(2, 0), (0, 2), (-2, 0), (0, -2)]
def tipNeighbour : Fin 4 → Plane := ![(1, 0), (0, 1), (-1, 0), (0, -1)]

theorem tipPoint_mem (t : Fin 4) : tipPoint t ∈ templateSites ∧ tipPoint t ∈ templateTips := by
  revert t
  decide +kernel

theorem tipNeighbour_mem (t : Fin 4) : tipNeighbour t ∈ templateSites \ templateTips := by
  revert t
  decide +kernel

def cornerIndex (j : Fin 8) : Fin 20 := ⟨j.val, by omega⟩
def tipIndex (t : Fin 4) (j : Fin 3) : Fin 20 := ⟨8 + 3 * t.val + j.val, by omega⟩

def packFields (corner : Fin 8 → Vec3) (tip : Fin 4 → Fin 3 → Vec3)
    (j : Fin 20) : Vec3 :=
  if h : j.val < 8 then corner ⟨j.val, h⟩ else
    tip ⟨(j.val - 8) / 3, by omega⟩ ⟨(j.val - 8) % 3, by omega⟩

theorem packFields_corner (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3) (j : Fin 8) :
    packFields c b (cornerIndex j) = c j := by simp [packFields, cornerIndex, j.isLt]

theorem packFields_tip (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3)
    (t : Fin 4) (j : Fin 3) : packFields c b (tipIndex t j) = b t j := by
  have hn : ¬8 + 3 * t.val + j.val < 8 := by omega
  have hdiv : (8 + 3 * t.val + j.val - 8) / 3 = t.val := by omega
  have hmod : (8 + 3 * t.val + j.val - 8) % 3 = j.val := by omega
  simp [packFields, tipIndex, hn, hdiv, hmod]

theorem packFields_ball (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3)
    (hc : ∀ j, normSq (c j) ≤ 1) (hb : ∀ t j, normSq (b t j) ≤ 1) :
    ∀ j, normSq (packFields c b j) ≤ 1 := by
  intro j
  unfold packFields
  split_ifs
  · exact hc _
  · exact hb _ _

def coreSites (π : PatternData) : Finset Plane := π.active \ templateTips

def coreBonds (π : PatternData) : Finset (Plane × Plane) :=
  π.bonds.filter fun e => e.1 ∉ templateTips ∧ e.2 ∉ templateTips

def coreKernel (π : PatternData) (next : Bool) (σ : coreSites π → SpinLetter) : ℝ :=
  (∏ x : coreSites π,
    spinWeight (if next ∧ x.val = (0, 0) then .D else π.statusAt x.val) (σ x)) *
  ∏ e ∈ coreBonds π,
    if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1 else
      1 + dot (supportSpins (coreSites π) σ e.1) (supportSpins (coreSites π) σ e.2)

def cornerKernel (π : PatternData) (c : Fin 8 → Vec3)
    (σ : coreSites π → SpinLetter) : ℝ :=
  ∏ j : Fin 8,
    if π.statusAt (externalSlot (cornerIndex j)).1 = .X then 1 else
      1 + dot (c j) (supportSpins (coreSites π) σ (externalSlot (cornerIndex j)).1)

def coverTipBond (π : PatternData) (t : Fin 4) : Bool := by
  classical
  exact decide (π.InternalPresent (tipNeighbour t) (tipPoint t))

def actualTipStatus (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) (t : Fin 4) : Status :=
  a.D.status (localChart a incoming (tipPoint t))

def actualTipBond (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) (t : Fin 4) : Bool :=
  decide (a.D.Present (localChart a incoming (tipNeighbour t))
    (localChart a incoming (tipPoint t)))

/-- The actual four tips have been summed, leaving the nine-site core. -/
def actualReduced (π : PatternData) (s : Fin 4 → Status) (bond : Fin 4 → Bool)
    (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3) (next : Bool) : ℝ :=
  ∑ σ : coreSites π → SpinLetter, coreKernel π next σ * cornerKernel π c σ *
    ∏ t : Fin 4,
      tipValue (s t) (bond t) (b t) (supportSpins (coreSites π) σ (tipNeighbour t))

/-- The covering four U tips, with ball external fields. -/
def coveredReduced (π : PatternData) (c : Fin 8 → Vec3)
    (b : Fin 4 → Fin 3 → Vec3) (next : Bool) : ℝ :=
  ∑ σ : coreSites π → SpinLetter, coreKernel π next σ * cornerKernel π c σ *
    ∏ t : Fin 4,
      coveredTipValue (coverTipBond π t) (b t)
        (supportSpins (coreSites π) σ (tipNeighbour t))

/-- Independent finite mixtures tensorize, keeping both passage laws. -/
theorem reduced_tip_mixture (π : PatternData) (s : Fin 4 → Status) (bond : Fin 4 → Bool)
    (hkeep : ∀ t, bond t = true → coverTipBond π t = true)
    (hlive : ∀ t, bond t = true → s t ≠ .X)
    (c : Fin 8 → Vec3) (b : Fin 4 → Fin 3 → Vec3)
    (hb : ∀ t j, normSq (b t j) ≤ 1) :
    ∃ fields : (Fin 4 → Bool) → Fin 4 → Fin 3 → Vec3,
      ∃ w : (Fin 4 → Bool) → ℝ,
      (∀ η, 0 ≤ w η) ∧ (∀ η t j, normSq (fields η t j) ≤ 1) ∧
      ∀ next : Bool, actualReduced π s bond c b next =
        ∑ η, w η * coveredReduced π c (fields η) next := by
  classical
  choose fields w hw hb' he using fun t =>
    tip_ball_mixture (s t) (bond t) (coverTipBond π t) (hkeep t) (hlive t) (b t) (hb t)
  refine ⟨(fun η t => fields t (η t)), (fun η => ∏ t, w t (η t)), ?_, ?_, ?_⟩
  · intro η
    exact Finset.prod_nonneg fun t _ => hw t _
  · intro η t j
    exact hb' t (η t) j
  · intro next
    unfold actualReduced
    simp_rw [he, Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    unfold coveredReduced
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring

/-- The concrete matcher used by the frozen statement, with its witness exposed. -/
def Matches (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) : Prop :=
  π.Covered ∧ normalizeRotation incoming π.outgoing.step = outgoing.step ∧
  (∀ z ∈ templateSites \ templateTips, π.statusAt z = a.D.status (localChart a incoming z)) ∧
  ∀ z ∈ templateSites \ templateTips, ∀ t ∈ templateSites,
    if t ∈ templateTips then
      a.D.Present (localChart a incoming z) (localChart a incoming t) → π.InternalPresent z t
    else (π.InternalPresent z t ↔ a.D.Present (localChart a incoming z) (localChart a incoming t))

theorem matches_exists (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (h : AKLT.Defs.CoveredDepartureV2 a.D a.y incoming outgoing) :
    ∃ π, Matches a incoming outgoing π := h

theorem matches_tip_kept (a : AKLT.Blueprint.Rec.Departure) (incoming outgoing : Compass)
    (π : PatternData) (h : Matches a incoming outgoing π) (t : Fin 4)
    (hb : actualTipBond a incoming t = true) : coverTipBond π t = true := by
  classical
  have htip := (tipPoint_mem t).2
  have hp := h.2.2.2 (tipNeighbour t) (tipNeighbour_mem t) (tipPoint t) (tipPoint_mem t).1
  simp only [htip, ite_true] at hp
  exact decide_eq_true (hp (of_decide_eq_true hb))

theorem actual_tip_live (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (t : Fin 4) (hb : actualTipBond a incoming t = true) : actualTipStatus a incoming t ≠ .X := by
  have hp := of_decide_eq_true hb
  exact (Finset.mem_filter.mp hp.2.1).2

theorem rotation_straight (incoming outgoing canonical : Compass)
    (h : normalizeRotation incoming canonical.step = outgoing.step) :
    canonical = .north ↔ outgoing = incoming := by
  cases incoming <;> cases outgoing <;> cases canonical <;>
    simp_all [normalizeRotation, Compass.step]

#print axioms reduced_tip_mixture
#print axioms matches_tip_kept
#print axioms actual_tip_live
#print axioms rotation_straight

end AKLT.W.REC089
