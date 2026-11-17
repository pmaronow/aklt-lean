module
public import AKLT.Blueprint.Win.NodesCut

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN066

private theorem sum_union_prod {α : Type*} [DecidableEq α]
    (s t : Finset α) (h : Disjoint s t)
    (f : (↥s → IcoLetter) → ℝ) (g : (↥t → IcoLetter) → ℝ) :
    (∑ n : (↥(s ∪ t) → IcoLetter), f (fun x => n ⟨x.1, Finset.mem_union_left t x.2⟩) *
      g (fun x => n ⟨x.1, Finset.mem_union_right s x.2⟩)) =
      (∑ a : (↥s → IcoLetter), f a) * (∑ b : (↥t → IcoLetter), g b) := by
  classical
  let e := Equiv.piFinsetUnion (fun _ : α => IcoLetter) h
  calc
    _ = ∑ p : (↥s → IcoLetter) × (↥t → IcoLetter), f p.1 * g p.2 := by
      apply Fintype.sum_equiv e.symm
      intro n
      apply congrArg₂ (fun a b => f a * g b)
      · funext x
        let z : ↥(s ∪ t) := ⟨x.1, Finset.mem_union_left t x.2⟩
        have hn := congrFun (e.apply_symm_apply n) z
        have hp := Equiv.piFinsetUnion_left (fun _ : α => IcoLetter) h
          (f := (e.symm n).1) (g := (e.symm n).2) x.2 (Finset.mem_union_left t x.2)
        exact hn.symm.trans hp
      · funext x
        let z : ↥(s ∪ t) := ⟨x.1, Finset.mem_union_right s x.2⟩
        have hn := congrFun (e.apply_symm_apply n) z
        have hp := Equiv.piFinsetUnion_right (fun _ : α => IcoLetter) h
          (f := (e.symm n).1) (g := (e.symm n).2) x.2 (Finset.mem_union_right s x.2)
        exact hn.symm.trans hp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      exact (Fintype.sum_mul_sum f g).symm


private theorem positive_adj {x y : Plane} (h : y ∈ AKLT.Defs.positiveNeighbours x) : Adjacent x y := by
  simp only [AKLT.Defs.positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · subst y
    simp [Adjacent, latticeDist]
  · subst y
    simp [Adjacent, latticeDist]

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have hx : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by
    rw [show y.1 - x.1 = -(x.1 - y.1) by omega, Int.natAbs_neg]
  have hy : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by
    rw [show y.2 - x.2 = -(x.2 - y.2) by omega, Int.natAbs_neg]
  simpa [Adjacent, latticeDist, hx, hy, Nat.add_comm] using h

private theorem internalBonds_union (s t : Finset Plane)
    (hbond : AKLT.Blueprint.Win.NoBond (↑s) (↑t)) :
    internalBonds (s ∪ t) = internalBonds s ∪ internalBonds t := by
  classical
  ext ⟨x, y⟩
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter,
    Finset.mem_union, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, hax, hby⟩
    subst a
    subst b
    rcases ha with hxs | hxt
    · rcases hb.2 with hys | hyt
      · exact Or.inl ⟨x, hxs, y, ⟨hb.1, hys⟩, rfl, rfl⟩
      · exact False.elim (hbond x hxs y hyt (positive_adj hb.1))
    · rcases hb.2 with hys | hyt
      · exact False.elim (hbond y hys x hxt (adjacent_symm (positive_adj hb.1)))
      · exact Or.inr ⟨x, hxt, y, ⟨hb.1, hyt⟩, rfl, rfl⟩
  · rintro (⟨a, ha, b, hb, hax, hby⟩ | ⟨a, ha, b, hb, hax, hby⟩)
    · subst a
      subst b
      exact ⟨x, Or.inl ha, y, ⟨hb.1, Or.inl hb.2⟩, rfl, rfl⟩
    · subst a
      subst b
      exact ⟨x, Or.inr ha, y, ⟨hb.1, Or.inr hb.2⟩, rfl, rfl⟩

private def freeWeight (H : Finset Plane) (n : PlaneConfiguration H) : ℝ :=
  (1 / 12 : ℝ) ^ H.card *
    ∏ e ∈ internalBonds H,
      (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))

private theorem internalBonds_fst_mem {H : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds H) : e.1 ∈ H := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter] at he
  rcases he with ⟨x, hx, y, hy, heq⟩
  have hfst : x = e.1 := congrArg Prod.fst heq
  simpa [hfst] using hx

private theorem internalBonds_snd_mem {H : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds H) : e.2 ∈ H := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter] at he
  rcases he with ⟨x, hx, y, hy, heq⟩
  have hsnd : y = e.2 := congrArg Prod.snd heq
  simpa [hsnd] using hy.2

private theorem internalBonds_disjoint (s t : Finset Plane) (hdisj : Disjoint s t) :
    Disjoint (internalBonds s) (internalBonds t) := by
  apply Finset.disjoint_left.mpr
  intro e hes het
  have hs := internalBonds_fst_mem hes
  have ht := internalBonds_fst_mem het
  exact (Finset.disjoint_left.mp hdisj) hs ht

private theorem freeWeight_union (s t : Finset Plane) (hdisj : Disjoint s t)
    (hbond : AKLT.Blueprint.Win.NoBond (↑s) (↑t))
    (n : PlaneConfiguration (s ∪ t)) :
    freeWeight (s ∪ t) n =
      freeWeight s (fun x => n ⟨x.1, Finset.mem_union_left t x.2⟩) *
      freeWeight t (fun x => n ⟨x.1, Finset.mem_union_right s x.2⟩) := by
  classical
  have hsplit := internalBonds_union s t hbond
  have hbd := internalBonds_disjoint s t hdisj
  have hleft (e : Plane × Plane) (he : e ∈ internalBonds s) :
      extendIcoSpins (fun x : s => n ⟨x.1, Finset.mem_union_left t x.2⟩) e.1 =
      extendIcoSpins n e.1 := by
    have hx := internalBonds_fst_mem he
    simp [extendIcoSpins, hx]
  have hright (e : Plane × Plane) (he : e ∈ internalBonds t) :
      extendIcoSpins (fun x : t => n ⟨x.1, Finset.mem_union_right s x.2⟩) e.1 =
      extendIcoSpins n e.1 := by
    have hx := internalBonds_fst_mem he
    simp [extendIcoSpins, hx]
  unfold freeWeight
  rw [hsplit, Finset.prod_union hbd]
  have hprod1 :
      ∏ e ∈ internalBonds s,
        (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2)) =
      ∏ e ∈ internalBonds s,
        (1 + dot (extendIcoSpins (fun x : s => n ⟨x.1, Finset.mem_union_left t x.2⟩) e.1)
          (extendIcoSpins (fun x : s => n ⟨x.1, Finset.mem_union_left t x.2⟩) e.2)) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [← hleft e he]
    have hy := internalBonds_snd_mem he
    have hsnd : extendIcoSpins (fun x : s => n ⟨x.1, Finset.mem_union_left t x.2⟩) e.2 =
      extendIcoSpins n e.2 := by simp [extendIcoSpins, hy]
    rw [← hsnd]
  have hprod2 :
      ∏ e ∈ internalBonds t,
        (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2)) =
      ∏ e ∈ internalBonds t,
        (1 + dot (extendIcoSpins (fun x : t => n ⟨x.1, Finset.mem_union_right s x.2⟩) e.1)
          (extendIcoSpins (fun x : t => n ⟨x.1, Finset.mem_union_right s x.2⟩) e.2)) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [← hright e he]
    have hy := internalBonds_snd_mem he
    have hsnd : extendIcoSpins (fun x : t => n ⟨x.1, Finset.mem_union_right s x.2⟩) e.2 =
      extendIcoSpins n e.2 := by simp [extendIcoSpins, hy]
    rw [← hsnd]
  rw [hprod1, hprod2]
  simp only [Finset.card_union_of_disjoint hdisj, pow_add]
  ring

private theorem diff_diff_eq_self {D H : Finset Plane} (h : H ⊆ D) :
    D \ (D \ H) = H := by
  ext x
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨hxD, hxnot⟩
    by_contra hxH
    exact hxnot ⟨hxD, hxH⟩
  · intro hxH
    exact ⟨h hxH, by simp [hxH]⟩

private theorem freeSum_split (D Y s t : Finset Plane)
    (hpart : s ∪ t = D \ Y) (hdisj : Disjoint s t)
    (hsD : s ⊆ D) (htD : t ⊆ D)
    (hbond : AKLT.Blueprint.Win.NoBond (↑s) (↑t)) :
    freeSum D Y (fun _ => 1) =
      freeSum D (D \ s) (fun _ => 1) * freeSum D (D \ t) (fun _ => 1) := by
  classical
  have hsactive : D \ (D \ s) = s := diff_diff_eq_self hsD
  have htactive : D \ (D \ t) = t := diff_diff_eq_self htD
  unfold freeSum
  rw [← hpart, hsactive, htactive]
  simp only [mul_one]
  change (∑ n : PlaneConfiguration (s ∪ t), freeWeight (s ∪ t) n) =
    (∑ a : PlaneConfiguration s, freeWeight s a) *
      (∑ b : PlaneConfiguration t, freeWeight t b)
  calc
    _ = ∑ n : PlaneConfiguration (s ∪ t),
        freeWeight s (fun x => n ⟨x.1, Finset.mem_union_left t x.2⟩) *
        freeWeight t (fun x => n ⟨x.1, Finset.mem_union_right s x.2⟩) := by
      apply Fintype.sum_congr
      intro n
      exact freeWeight_union s t hdisj hbond n
    _ = _ := sum_union_prod s t hdisj (freeWeight s) (freeWeight t)

private def pinProduct (D H : Finset Plane) (τ : PinAssignment D)
    (n : PlaneConfiguration H) : ℝ :=
  ∏ e : originalLegs D,
    if e.val.1 ∈ H then
      1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1

private def pinnedWeight (D H : Finset Plane) (τ : PinAssignment D)
    (n : PlaneConfiguration H) : ℝ := freeWeight H n * pinProduct D H τ n

private theorem pinProduct_union (D s t : Finset Plane) (τ : PinAssignment D)
    (hdisj : Disjoint s t) (n : PlaneConfiguration (s ∪ t)) :
    pinProduct D (s ∪ t) τ n =
      pinProduct D s τ (fun x => n ⟨x.1, Finset.mem_union_left t x.2⟩) *
      pinProduct D t τ (fun x => n ⟨x.1, Finset.mem_union_right s x.2⟩) := by
  classical
  unfold pinProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e he
  by_cases hs : e.val.1 ∈ s
  · have ht : e.val.1 ∉ t := by
      intro ht
      exact (Finset.disjoint_left.mp hdisj) hs ht
    simp [hs, ht, extendIcoSpins]
  · by_cases ht : e.val.1 ∈ t
    · simp [hs, ht, extendIcoSpins]
    · simp [hs, ht]

private theorem pinnedWeight_union (D s t : Finset Plane) (τ : PinAssignment D)
    (hdisj : Disjoint s t)
    (hbond : AKLT.Blueprint.Win.NoBond (↑s) (↑t))
    (n : PlaneConfiguration (s ∪ t)) :
    pinnedWeight D (s ∪ t) τ n =
      pinnedWeight D s τ (fun x => n ⟨x.1, Finset.mem_union_left t x.2⟩) *
      pinnedWeight D t τ (fun x => n ⟨x.1, Finset.mem_union_right s x.2⟩) := by
  rw [pinnedWeight, pinnedWeight, pinnedWeight,
    freeWeight_union s t hdisj hbond n, pinProduct_union D s t τ hdisj n]
  ring

private theorem pinnedSum_split (D Y s t : Finset Plane) (τ : PinAssignment D)
    (hpart : s ∪ t = D \ Y) (hdisj : Disjoint s t)
    (hsD : s ⊆ D) (htD : t ⊆ D)
    (hbond : AKLT.Blueprint.Win.NoBond (↑s) (↑t)) :
    pinnedSum D Y τ (fun _ => 1) =
      pinnedSum D (D \ s) τ (fun _ => 1) * pinnedSum D (D \ t) τ (fun _ => 1) := by
  classical
  have hsactive : D \ (D \ s) = s := diff_diff_eq_self hsD
  have htactive : D \ (D \ t) = t := diff_diff_eq_self htD
  unfold pinnedSum
  rw [← hpart, hsactive, htactive]
  simp only [mul_one]
  change (∑ n : PlaneConfiguration (s ∪ t), pinnedWeight D (s ∪ t) τ n) =
    (∑ a : PlaneConfiguration s, pinnedWeight D s τ a) *
      (∑ b : PlaneConfiguration t, pinnedWeight D t τ b)
  calc
    _ = ∑ n : PlaneConfiguration (s ∪ t),
        pinnedWeight D s τ (fun x => n ⟨x.1, Finset.mem_union_left t x.2⟩) *
        pinnedWeight D t τ (fun x => n ⟨x.1, Finset.mem_union_right s x.2⟩) := by
      apply Fintype.sum_congr
      intro n
      exact pinnedWeight_union D s t τ hdisj hbond n
    _ = _ := sum_union_prod s t hdisj (pinnedWeight D s τ) (pinnedWeight D t τ)

theorem main : AKLT.Blueprint.Win.OriginalFactorizationStatement := by
  intro F B X G₁ G₂ hcut τ
  rcases hcut with ⟨hBF, hBext, hX, hdisj, hpart, hbond, houter₁, houter₂⟩
  have hG₁active : G₁ ⊆ (F \ B) \ X := by
    rw [← hpart]
    exact Finset.subset_union_left
  have hG₂active : G₂ ⊆ (F \ B) \ X := by
    rw [← hpart]
    exact Finset.subset_union_right
  have hG₁ : G₁ ⊆ F \ B := hG₁active.trans Finset.sdiff_subset
  have hG₂ : G₂ ⊆ F \ B := hG₂active.trans Finset.sdiff_subset
  constructor
  · simpa [AKLT.Blueprint.Win.componentSum] using
      pinnedSum_split (F \ B) X G₁ G₂ τ hpart hdisj hG₁ hG₂ hbond
  · exact freeSum_split (F \ B) X G₁ G₂ hpart hdisj hG₁ hG₂ hbond

#print axioms main

end AKLT.W.WIN066
