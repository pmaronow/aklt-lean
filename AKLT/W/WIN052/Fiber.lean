module
public import AKLT.W.WIN052.Polynomial

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win
namespace AKLT.W.WIN052

/-- The reindexing which separates one spin from all the remaining spins. -/
def removalConfigEquiv (G Y : Finset Plane) (x : Plane)
    (hx : x ∈ G \ Y) :
    PlaneConfiguration (G \ Y) ≃
      PlaneConfiguration (G \ insert x Y) × IcoLetter := by
  classical
  let D := G \ Y
  let E := G \ insert x Y
  refine
    { toFun := fun n =>
        (fun z : E => n ⟨z.1, by
          rcases Finset.mem_sdiff.mp z.2 with ⟨hzG, hznot⟩
          exact Finset.mem_sdiff.mpr ⟨hzG, fun hy => hznot (Finset.mem_insert_of_mem hy)⟩⟩,
         n ⟨x, hx⟩)
      invFun := fun q => fun z : D =>
        if heq : z.1 = x then q.2 else
          q.1 ⟨z.1, by
            rcases Finset.mem_sdiff.mp z.2 with ⟨hzG, hzY⟩
            refine Finset.mem_sdiff.mpr ⟨hzG, ?_⟩
            intro hi
            rcases Finset.mem_insert.mp hi with hxi | hy
            · exact heq hxi
            · exact hzY hy⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro n
    funext z
    by_cases heq : z.1 = x
    · have hz : (⟨x, hx⟩ : D) = z := Subtype.ext heq.symm
      rw [← hz]
      simp
    · simp [heq]
  · rintro ⟨r, a⟩
    apply Prod.ext
    · funext z
      have hz : z.1 ≠ x := by
        intro h
        exact (Finset.mem_sdiff.mp z.2).2 (by simp [h])
      simp [hz]
    · simp


theorem spins_removed (G Y : Finset Plane) (x : Plane) (hx : x ∈ G \ Y)
    (r : PlaneConfiguration (G \ insert x Y)) (a : IcoLetter) :
    extendIcoSpins ((removalConfigEquiv G Y x hx).symm (r, a)) x = icoVector a := by
  simp [extendIcoSpins, hx, removalConfigEquiv]

theorem spins_retained (G Y : Finset Plane) (x : Plane) (hx : x ∈ G \ Y)
    (r : PlaneConfiguration (G \ insert x Y)) (a : IcoLetter)
    (z : Plane) (hzx : z ≠ x) :
    extendIcoSpins ((removalConfigEquiv G Y x hx).symm (r, a)) z =
      extendIcoSpins r z := by
  classical
  have hmem : z ∈ G \ Y ↔ z ∈ G \ insert x Y := by
    simp [Finset.mem_sdiff, Finset.mem_insert, hzx]
  by_cases hz : z ∈ G \ Y
  · simp [extendIcoSpins, hz, hmem.mp hz, removalConfigEquiv, hzx]
  · have hzE : z ∉ G \ insert x Y := fun h => hz (hmem.mpr h)
    simp only [extendIcoSpins, dite_eq_right hz, dite_eq_right hzE]

/-- Removing the spin changes just its uniform mass and incident bonds. -/
theorem weight_factor (G Y : Finset Plane) (τ : PinAssignment G) (x : Plane)
    (hstep : RemovalStep G Y x) (pinned : Bool)
    (r : PlaneConfiguration (G \ insert x Y)) (a : IcoLetter) :
    partWeight pinned G Y τ ((removalConfigEquiv G Y x hstep.2.1).symm (r, a)) =
      partWeight pinned G (insert x Y) τ r *
        ((1 / 12 : ℝ) * ∏ z ∈ survivors G Y x,
          (1 + dot (icoVector a) (extendIcoSpins r z))) := by
  classical
  let E := G \ insert x Y
  let s := (removalConfigEquiv G Y x hstep.2.1).symm (r, a)
  have hxE : x ∉ E := by simp [E]
  have hD : G \ Y = insert x E := by
    ext z
    by_cases hz : z = x
    · subst z
      exact ⟨fun _ => by simp, fun _ => hstep.2.1⟩
    · simp [E, Finset.mem_sdiff, hz]
  have hc : (G \ Y).card = E.card + 1 := by
    rw [hD, Finset.card_insert_of_notMem hxE]
  have hne (z : Plane) (hz : z ∈ E) : z ≠ x := by
    intro h
    exact hxE (h ▸ hz)
  have hrest :
      (∏ e ∈ internalBonds E, (1 + dot (extendIcoSpins s e.1) (extendIcoSpins s e.2))) =
      ∏ e ∈ internalBonds E, (1 + dot (extendIcoSpins r e.1) (extendIcoSpins r e.2)) := by
    apply Finset.prod_congr rfl
    intro e he
    rcases e with ⟨u, v⟩
    have h := mem_bonds.mp he
    rw [spins_retained G Y x hstep.2.1 r a u (hne u h.1),
      spins_retained G Y x hstep.2.1 r a v (hne v h.2.1)]
  have hinc :
      (∏ z ∈ neighbours x ∩ E, (1 + dot (extendIcoSpins s x) (extendIcoSpins s z))) =
      ∏ z ∈ survivors G Y x, (1 + dot (icoVector a) (extendIcoSpins r z)) := by
    apply Finset.prod_congr rfl
    intro z hz
    rw [spins_removed G Y x hstep.2.1 r a,
      spins_retained G Y x hstep.2.1 r a z (hne z (Finset.mem_inter.mp hz).2)]
  have hbonds :
      (∏ e ∈ internalBonds (G \ Y),
        (1 + dot (extendIcoSpins s e.1) (extendIcoSpins s e.2))) =
      (∏ e ∈ internalBonds E,
        (1 + dot (extendIcoSpins r e.1) (extendIcoSpins r e.2))) *
      ∏ z ∈ survivors G Y x, (1 + dot (icoVector a) (extendIcoSpins r z)) := by
    rw [congrArg internalBonds hD, bondProduct_insert hxE, hrest, hinc]
  have hlegs :
      (∏ e : originalLegs G, if pinned ∧ e.val.1 ∈ G \ Y then
        1 + dot (τ e).val (extendIcoSpins s e.val.1) else 1) =
      ∏ e : originalLegs G, if pinned ∧ e.val.1 ∈ E then
        1 + dot (τ e).val (extendIcoSpins r e.val.1) else 1 := by
    apply Finset.prod_congr rfl
    intro e _
    have hx := leg_source_ne hstep.2.2 e
    have hmem : e.val.1 ∈ G \ Y ↔ e.val.1 ∈ E := by
      simp [E, Finset.mem_sdiff, Finset.mem_insert, hx]
    have hs : extendIcoSpins s e.val.1 = extendIcoSpins r e.val.1 :=
      spins_retained G Y x hstep.2.1 r a e.val.1 hx
    simp only [hmem, hs]
  change (1 / 12 : ℝ) ^ (G \ Y).card *
      (∏ e ∈ internalBonds (G \ Y),
        (1 + dot (extendIcoSpins s e.1) (extendIcoSpins s e.2))) *
      (∏ e : originalLegs G, if pinned ∧ e.val.1 ∈ G \ Y then
        1 + dot (τ e).val (extendIcoSpins s e.val.1) else 1) = _
  rw [hc, pow_succ, hbonds, hlegs]
  unfold partWeight
  ring

/-- The closed one-site identity that discharges the earlier residual. -/
theorem siteFiber (hM : AKLT.Blueprint.Top.MomentsStatement)
    (G Y : Finset Plane) (τ : PinAssignment G) (x : Plane)
    (hstep : RemovalStep G Y x) (pinned : Bool)
    (r : PlaneConfiguration (G \ insert x Y)) :
    (∑ a : IcoLetter,
      partWeight pinned G Y τ ((removalConfigEquiv G Y x hstep.2.1).symm (r, a))) =
      partWeight pinned G (insert x Y) τ r *
        removalPolynomial x (survivors G Y x) (extendIcoSpins r) := by
  simp_rw [weight_factor G Y τ x hstep pinned r]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact congrArg (partWeight pinned G (insert x Y) τ r * ·)
    (neighbour_moment hM x (survivors G Y x) Finset.inter_subset_left (extendIcoSpins r))

end AKLT.W.WIN052
