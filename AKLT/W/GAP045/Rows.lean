import AKLT.W.GAP045.Window

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
namespace AKLT.W.GAP045
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- An exceptional row is the point mass at its input. -/
theorem skipped_row
    (P : PlaneSpec) (a y : Plane) (u l h : ℕ) (p α : ℝ)
    (η ξ : Config P.Letter) (j : Fin h)
    (ω : PlaneConfig P (square a u) × PlaneConfig P (square a u))
    (hex : (j.val + 2 : ℤ) ∈ exceptionalIndices a y u) :
    ∃ r, RowConditions P a y u l h p α η ξ j ω r := by
  classical
  let r : Weight (PlaneConfig P (square a u) × PlaneConfig P (square a u)) :=
    fun v => if v = ω then 1 else 0
  have hp : Probability r := by
    constructor
    · intro v; dsimp [r]; split_ifs <;> norm_num
    · dsimp [r]; simp
  refine ⟨r, hp, ?_, ?_, ?_, ?_⟩
  · simp [r, hex]
  · intro v hv
    have hvo : v = ω := by by_contra hn; simp [r, hn] at hv
    subst v
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · intro hn; exact (hn hex).elim
  · intro _ hn; exact (hn hex).elim

/-- Lift a local coupling with the two required support and success certificates. -/
theorem row_of_local (P : PlaneSpec) (hP : RegularSpec P)
    (a y : Plane) (u l h : ℕ) (p α : ℝ) (η ξ : Config P.Letter)
    (j : Fin h) (ω : PlaneConfig P (square a u) × PlaneConfig P (square a u))
    (hex : (j.val+2 : ℤ) ∉ exceptionalIndices a y u)
    (hD : shell a y u (j.val+2) ⊆ farVolume a y u (j.val+2))
    (c : Coupling
      (P.law (farVolume a y u (j.val+2)) (fill P (square a u) η ω.1))
      (P.law (farVolume a y u (j.val+2)) (fill P (square a u) ξ ω.2)))
    (hi : AgreeOn (sitesInVolume (square a u) (shell a y u (j.val+1))) ω.1 ω.2 →
      ∀ x z, 0 < c.mass x z → x = z)
    (hc : j.val+2 ≤ h → p * α^(16*l) ≤ eventMass
      (fun z : PlaneConfig P (farVolume a y u (j.val+2)) ×
        PlaneConfig P (farVolume a y u (j.val+2)) => c.mass z.1 z.2)
      (fun z => AgreeOn (sitesInVolume (farVolume a y u (j.val+2))
        (shell a y u (j.val+2))) z.1 z.2)) :
    ∃ r, RowConditions P a y u l h p α η ξ j ω r := by
  let W := square a u
  let F := farVolume a y u (j.val+2)
  have hF : F ⊆ W := Finset.filter_subset _ _
  let d := liftLocalCoupling P hP W F hF η ξ ω.1 ω.2 c
  let r : Weight (PlaneConfig P W × PlaneConfig P W) := fun z => d.mass z.1 z.2
  have hr : Probability r := coupling_probability (fibre_probability P hP W F η ω.1) d
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · simp only [hex, ↓reduceIte]
    exact ⟨d.first_marginal, d.second_marginal⟩
  · intro v hv
    exact lifted_support P hP W F η ξ ω.1 ω.2 d v hv
  · intro _ hs v hv
    obtain ⟨x,z,hxz,hx,hz⟩ := mapCoupling_positive c
      (insertVolume P W F ω.1) (insertVolume P W F ω.2) v.1 v.2 hv
    have he := hi hs x z hxz
    rw [← hx, ← hz]
    exact insert_agreement P W F F (fun _ h => h) ω.1 ω.2 (x,z)
      (fun t _ => congrFun he t)
  · intro hj _
    have hmap := mapCoupling_event c (insertVolume P W F ω.1) (insertVolume P W F ω.2)
      (fun z => AgreeOn (sitesInVolume W (shell a y u (j.val+2))) z.1 z.2)
    dsimp only [r, d, liftLocalCoupling]
    rw [hmap]
    exact (hc hj).trans (event_mono (fun z => c.nonnegative z.1 z.2)
      (fun _ => le_rfl) (fun z hz => insert_agreement P W F _ hD ω.1 ω.2 z hz))

end AKLT.W.GAP045
