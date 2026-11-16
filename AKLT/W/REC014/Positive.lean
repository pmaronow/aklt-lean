import AKLT.W.REC014.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC014

theorem spins_at {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter)
    (x : D.active) : D.spins n x.val = spinVector (n x) := by
  simp [Network.spins, x.property]

theorem spins_ball {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter)
    (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  by_cases hx : x ∈ D.active
  · simpa [Network.spins, hx] using spin_ball (n ⟨x,hx⟩)
  · simp [Network.spins, hx, normSq, dot]

theorem partition_positive {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) : 0 < D.partition τ pinned (fun _ => 1) := by
  classical
  have hchoose (x : D.active) : ∃ j : Fin 3 × Fin 2,
      ∀ e : {e : originalLegs G // e.val.1 = x.val},
        0 < 1 + dot (icoVector (label j)) (τ e.val).val := by
    apply label_avoids (fun e : {e : originalLegs G // e.val.1 = x.val} => τ e.val)
    let e : {e : originalLegs G // e.val.1 = x.val} ≃
        ↥((originalLegs G).filter fun e => e.1 = x.val) :=
      { toFun := fun e => ⟨e.val.val, Finset.mem_filter.mpr ⟨e.val.property,e.property⟩⟩
        invFun := fun e => ⟨⟨e.val,(Finset.mem_filter.mp e.property).1⟩,
          (Finset.mem_filter.mp e.property).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_coe]
    exact leg_count x.val
  choose σ hσ using hchoose
  let n : D.active → SpinLetter := fun x => some (label (σ x))
  have hsp (x : D.active) : D.spins n x = icoVector (label (σ x)) := by
    simp [spins_at, n, spinVector]
  have hw : 0 < (∏ x : D.active, spinWeight (D.status x.val) (n x)) * 1 *
      (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G,
        if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n e.val.1) else 1 := by
    apply mul_pos
    · apply mul_pos
      · apply mul_pos
        · apply Finset.prod_pos
          intro x _
          exact weight_pos _ (Finset.mem_filter.mp x.property).2 _
        · norm_num
      · apply Finset.prod_pos
        intro e he
        have hp := (Finset.mem_filter.mp he).2
        rw [hsp ⟨e.1,hp.1⟩, hsp ⟨e.2,hp.2.1⟩]
        exact factor_pos _ _ (le_of_eq (ico_unit _)) (le_of_eq (ico_unit _))
          (label_not_antipodal _ _)
    · apply Finset.prod_pos
      intro e _
      split_ifs with h
      · rw [hsp ⟨e.val.1,h.2⟩, dot_comm]
        exact hσ ⟨e.val.1,h.2⟩ ⟨e,rfl⟩
      · norm_num
  apply Finset.sum_pos'
  · intro a _
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (Finset.prod_nonneg fun x _ => weight_nonneg _ _) (by norm_num)
      · exact Finset.prod_nonneg fun e _ =>
          factor_nonneg _ _ (spins_ball D a _) (spins_ball D a _)
    · apply Finset.prod_nonneg
      intro e _
      split_ifs
      · exact factor_nonneg _ _ (le_of_eq (τ e).property) (spins_ball D a _)
      · norm_num
  · exact ⟨n, Finset.mem_univ _, hw⟩

end AKLT.W.REC014
