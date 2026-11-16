import AKLT.W.REC013.SpinFacts

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC013

theorem candidate_avoids {ι : Type*} [Fintype ι] (hc : Fintype.card ι ≤ 4)
    (pin : ι → UnitVector) :
    ∃ a : Fin 3 × Fin 2, ∀ i, 0 < 1 + dot (icoVector (candidate a)) (pin i).val := by
  classical
  by_contra h
  push Not at h
  choose f hf using h
  have hz (a) : icoVector (candidate a) = -(pin (f a)).val := by
    apply factor_zero _ _ (ico_unit _) (pin (f a)).property
    exact le_antisymm (hf a) (factor_nonneg _ _ (ico_unit _).le (pin (f a)).property.le)
  have hinj : Function.Injective f := by
    intro a b hab
    apply candidate_injective
    change icoVector (candidate a) = icoVector (candidate b)
    rw [hz a, hz b, hab]
  have hh := Fintype.card_le_of_injective f hinj
  norm_num [Fintype.card_prod] at hh
  omega

theorem spinWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j := by
  cases s <;> cases j <;> norm_num [spinWeight]

theorem spinWeight_some_pos (s : Status) (hs : s ≠ .X) (j : IcoLetter) :
    0 < spinWeight s (some j) := by
  cases s <;> norm_num [spinWeight] at *

theorem network_spins_ball {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split
  · exact spin_ball _
  · norm_num [normSq, dot]

/-- A positive summand can be chosen using the six mutually compatible atoms. -/
theorem partition_positive {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (hD : D.Auxiliary) (b : Bool) : 0 < D.partition τ b (fun _ => 1) := by
  classical
  have hchoice (x : D.active) : ∃ a : Fin 3 × Fin 2,
      ∀ (e : Plane × Plane) (he : e ∈ originalLegs G), e.1 = x.val → 0 < 1 + dot (τ ⟨e, he⟩).val
        (icoVector (candidate a)) := by
    let L := (originalLegs G).filter fun e => e.1 = x.val
    have hc : Fintype.card L ≤ 4 := by
      simpa only [Fintype.card_coe] using
        (show L.card ≤ 4 by have hh := hD.1.2.2.2 x.val x.property; dsimp [L]; omega)
    obtain ⟨a, ha⟩ := candidate_avoids hc
      (fun e : L => τ ⟨e.val, (Finset.mem_filter.mp e.property).1⟩)
    refine ⟨a, ?_⟩
    intro e he hex
    rw [dot_comm]
    exact ha ⟨e, Finset.mem_filter.mpr ⟨he, hex⟩⟩
  choose a ha using hchoice
  let n : D.active → SpinLetter := fun x => some (candidate (a x))
  have hv (x : D.active) : D.spins n x.val = icoVector (candidate (a x)) := by
    simp [Network.spins, n, spinVector]
  have hbonds (e : Plane × Plane) (he : e ∈ D.bonds) :
      0 < 1 + dot (D.spins n e.1) (D.spins n e.2) := by
    have hp := (Finset.mem_filter.mp he).2
    rw [hv ⟨e.1, hp.1⟩, hv ⟨e.2, hp.2.1⟩]
    exact candidate_factor_pos _ _
  have hterm : 0 < (∏ x : D.active, spinWeight (D.status x.val) (n x)) * (1 : ℝ) *
      (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G, if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1 := by
    apply mul_pos
    · apply mul_pos
      · simpa only [mul_one] using Finset.prod_pos (fun x _ =>
          spinWeight_some_pos (D.status x.val)
            (show D.status x.val ≠ .X from
              (show x.val ∈ G ∧ D.status x.val ≠ .X by
                simpa only [Network.active, Finset.mem_filter] using x.property).2) _)
      · exact Finset.prod_pos hbonds
    · apply Finset.prod_pos
      intro e _
      split_ifs with he
      · rw [hv ⟨e.val.1, he.2⟩]
        exact ha ⟨e.val.1, he.2⟩ e.val e.property rfl
      · norm_num
  unfold Network.partition
  apply Finset.sum_pos'
  · intro m _
    apply mul_nonneg
    · apply mul_nonneg
      · simpa only [mul_one] using Finset.prod_nonneg (fun x _ => spinWeight_nonneg _ _)
      · exact Finset.prod_nonneg (fun e _ => factor_nonneg _ _
          (network_spins_ball D m _) (network_spins_ball D m _))
    · apply Finset.prod_nonneg
      intro e _
      split_ifs
      · exact factor_nonneg _ _ (τ e).property.le (network_spins_ball D m _)
      · norm_num
  · exact ⟨n, Finset.mem_univ _, hterm⟩

end AKLT.W.REC013
