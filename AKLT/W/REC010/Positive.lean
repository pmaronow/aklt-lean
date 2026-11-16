import AKLT.W.REC010.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC010

/-- Fewer than six arbitrary unit pins cannot exclude all six chosen atoms. -/
theorem half_avoid {ι : Type*} [Fintype ι] (hi : Fintype.card ι < 6)
    (b : ι → UnitVector) : ∃ j : HalfLetter, ∀ i, 0 < 1 + dot (b i).val (halfVector j) := by
  classical
  by_contra h
  push Not at h
  choose bad hbad using h
  have hz (j : HalfLetter) : 1 + dot (halfVector j) (b (bad j)).val = 0 := by
    rw [dot_comm]
    exact le_antisymm (hbad j) (factor_nonneg (b (bad j)).property.le (half_unit j).le)
  have hinj : Function.Injective bad := by
    intro j k heq
    apply half_injective
    have hj := eq_neg_of_factor_zero (half_unit j) (b (bad j)).property.le (hz j)
    have hk := eq_neg_of_factor_zero (half_unit k) (b (bad k)).property.le (hz k)
    rw [heq] at hj
    exact hj.trans hk.symm
  have hc := Fintype.card_le_of_injective bad hinj
  have h6 : Fintype.card HalfLetter = 6 := by decide
  omega

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem spinWeight_some_pos (s : Status) (hs : s ≠ .X) (j : IcoLetter) :
    0 < spinWeight s (some j) := by
  cases s <;> simp_all [spinWeight]

theorem spinVector_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact (ico_unit j).le

theorem spins_ball {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split
  · exact spinVector_ball _
  · norm_num [normSq, dot]

/-- The unnormalized summand of the network partition with observable one. -/
def networkWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

theorem networkWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : D.active → SpinLetter) : 0 ≤ networkWeight D τ b n := by
  unfold networkWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg (fun x _ => spinWeight_nonneg _ _)
    · exact Finset.prod_nonneg (fun e _ => factor_nonneg (spins_ball D n _) (spins_ball D n _))
  · apply Finset.prod_nonneg
    intro e _
    split
    · exact factor_nonneg (τ e).property.le (spins_ball D n _)
    · norm_num

/-- Local pin avoidance independently at all active sites. -/
theorem positive_assignment {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (hlegs : ∀ x ∈ D.active, ((originalLegs G).filter fun e => e.1 = x).card ≤ 4) :
    ∃ n : D.active → HalfLetter,
      ∀ e : originalLegs G, ∀ h : e.val.1 ∈ D.active,
        0 < 1 + dot (τ e).val (halfVector (n ⟨e.val.1, h⟩)) := by
  classical
  have hx (x : D.active) : ∃ j : HalfLetter,
      ∀ e : (originalLegs G).filter (fun e => e.1 = x.val),
        0 < 1 + dot (τ ⟨e.val, (Finset.mem_filter.mp e.property).1⟩).val (halfVector j) := by
    apply half_avoid
    rw [Fintype.card_coe]
    have := hlegs x.val x.property
    omega
  choose n hn using hx
  refine ⟨n, ?_⟩
  intro e h
  exact hn ⟨e.val.1, h⟩ ⟨e.val, Finset.mem_filter.mpr ⟨e.property, rfl⟩⟩

/-- Strict partition positivity needs only the bound on surviving original legs. -/
theorem partition_pos_of_leg_bound {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (hlegs : ∀ x ∈ D.active, ((originalLegs G).filter fun e => e.1 = x).card ≤ 4)
    (b : Bool) : 0 < D.partition τ b (fun _ => 1) := by
  classical
  obtain ⟨n, hn⟩ := positive_assignment D τ hlegs
  let σ : D.active → SpinLetter := fun x => some (halfLetter (n x))
  have hspin (x : Plane) (hx : x ∈ D.active) : D.spins σ x = halfVector (n ⟨x, hx⟩) := by
    simp [Network.spins, hx, σ, spinVector, halfVector]
  have hpos : 0 < networkWeight D τ b σ := by
    unfold networkWeight
    apply mul_pos
    · apply mul_pos
      · apply Finset.prod_pos
        intro x _
        exact spinWeight_some_pos _ (Finset.mem_filter.mp x.property).2 _
      · apply Finset.prod_pos
        intro e he
        have hp := (Finset.mem_filter.mp he).2
        rw [hspin e.1 hp.1, hspin e.2 hp.2.1]
        exact half_pair_pos _ _
    · apply Finset.prod_pos
      intro e _
      split
      · rename_i h
        rw [hspin e.val.1 h.2]
        exact hn e h.2
      · norm_num
  have hsum : D.partition τ b (fun _ => 1) = ∑ n, networkWeight D τ b n := by
    simp [Network.partition, networkWeight]
  rw [hsum]
  exact Finset.sum_pos' (fun n _ => networkWeight_nonneg D τ b n)
    ⟨σ, Finset.mem_univ _, hpos⟩

/-- In particular, every auxiliary network has positive normalizers for both pin choices. -/
theorem partition_pos {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (hD : D.Auxiliary) (b : Bool) : 0 < D.partition τ b (fun _ => 1) := by
  apply partition_pos_of_leg_bound D τ _ b
  intro x hx
  have hdegree := hD.1.2.2.2 x hx
  omega

end AKLT.W.REC010
