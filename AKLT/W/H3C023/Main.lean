module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C023

open AKLT.Cert.H3 AKLT.Gen.Packed CertData.H3.Bridge
open AKLT.Defs

private theorem lane_oneMask (i s : Nat) :
    lane (oneMask i) 80 s = if s = i then 2 ^ 80 - 1 else 0 := by
  by_cases h : s = i
  · subst s
    rw [oneMask, lane_shiftLeft (2 ^ 80 - 1) 80 i i (by decide)]
    simp [lane]
  · by_cases hs : i ≤ s
    · have hpos : 0 < s - i := by omega
      rw [oneMask, lane_shiftLeft (2 ^ 80 - 1) 80 i s (by decide)]
      simp only [ite_eq_left hs]
      rw [show s - i = (s - i - 1) + 1 by omega, lane_succ]
      simp [lane, Nat.shiftRight_eq_div_pow]
      simp [h]
    · rw [oneMask, lane_shiftLeft (2 ^ 80 - 1) 80 i s (by decide)]
      simp [hs, h]

private theorem gridSite_index (s : Nat) :
    siteIndex (gridSite s) = s := by
  have hrow' : (((s / 141 : Nat) : Int) - 70 + 70).toNat = s / 141 := by
    have h : ((s / 141 : Nat) : Int) - 70 + 70 = (s / 141 : Nat) := by ring
    rw [h]
    exact Int.toNat_natCast _
  have hcol' : (((s % 141 : Nat) : Int) - 70 + 70).toNat = s % 141 := by
    have h : ((s % 141 : Nat) : Int) - 70 + 70 = (s % 141 : Nat) := by ring
    rw [h]
    exact Int.toNat_natCast _
  unfold siteIndex gridSite
  rw [hrow', hcol']
  calc
    s / 141 * 141 + s % 141 = 141 * (s / 141) + s % 141 := by ring
    _ = s := Nat.div_add_mod s 141

private theorem gridSite_index_neighbour (d : Compass) :
    gridSite (siteIndex (-d.step)) = -d.step := by
  cases d <;> norm_num [gridSite, siteIndex, Compass.step]

private theorem gridSite_eq_neighbour_iff (s : Nat) (d : Compass) :
    gridSite s = -d.step ↔ s = siteIndex (-d.step) := by
  constructor
  · intro h
    have := congrArg siteIndex h
    simpa [gridSite_index s] using this
  · intro h
    rw [h]
    exact gridSite_index_neighbour d

private theorem oneMask_fits (i : Nat) (hi : i < 19881) :
    Fits (oneMask i) 80 19881 := by
  unfold Fits oneMask
  rw [Nat.shiftLeft_eq]
  have hmul : (2 ^ 80 - 1) * 2 ^ (80 * i) < 2 ^ 80 * 2 ^ (80 * i) := by
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
  have hexp : 80 + 80 * i = 80 * (i + 1) := by omega
  calc
    (2 ^ 80 - 1) * 2 ^ (80 * i) < 2 ^ 80 * 2 ^ (80 * i) := hmul
    _ = 2 ^ (80 + 80 * i) := by rw [pow_add]
    _ = 2 ^ (80 * (i + 1)) := by rw [hexp]
    _ ≤ 2 ^ (80 * 19881) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem oneMask_packed (i : Nat) (hi : i < 19881) :
    oneMask i = packFn 80 19881 (fun s => if s = i then 2 ^ 80 - 1 else 0) := by
  apply lanes_ext (oneMask_fits i hi) (packFn_lt 80 19881 _ (by
    intro s hs
    split_ifs <;> omega))
  intro s hs
  rw [lane_oneMask, lane_packFn]
  · simp [hs]
  · intro t ht
    split_ifs <;> omega

private def neighbourIndex (s : Nat) : Prop :=
  s = 9799 ∨ s = 9939 ∨ s = 10081 ∨ s = 9941

private instance (s : Nat) : Decidable (neighbourIndex s) := by
  unfold neighbourIndex
  infer_instance

private theorem centreNeighbourMasks_sum :
    centreNeighbourMasks = oneMask 9799 + oneMask 9939 + oneMask 10081 + oneMask 9941 := by
  norm_num [centreNeighbourMasks, centreNeighbourMask, direction, siteIndex,
    Compass.step, List.range, List.range.loop]

private theorem centreNeighbourMasks_packed :
    centreNeighbourMasks = packFn 80 19881 (fun s => if neighbourIndex s then 2 ^ 80 - 1 else 0) := by
  have h0 := oneMask_packed 9799 (by norm_num)
  have h1 := oneMask_packed 9939 (by norm_num)
  have h2 := oneMask_packed 10081 (by norm_num)
  have h3 := oneMask_packed 9941 (by norm_num)
  have hfun : (fun s => if neighbourIndex s then 2 ^ 80 - 1 else 0) =
      (fun s => if s = 9799 then 2 ^ 80 - 1 else 0) +
      (fun s => if s = 9939 then 2 ^ 80 - 1 else 0) +
      (fun s => if s = 10081 then 2 ^ 80 - 1 else 0) +
      (fun s => if s = 9941 then 2 ^ 80 - 1 else 0) := by
    funext s
    by_cases h0 : s = 9799 <;> by_cases h1 : s = 9939 <;>
      by_cases h2 : s = 10081 <;> by_cases h3 : s = 9941 <;>
      simp [neighbourIndex, h0, h1, h2, h3]
  calc
    centreNeighbourMasks = oneMask 9799 + oneMask 9939 + oneMask 10081 + oneMask 9941 :=
      centreNeighbourMasks_sum
    _ = packFn 80 19881 (fun s => if s = 9799 then 2 ^ 80 - 1 else 0) +
          packFn 80 19881 (fun s => if s = 9939 then 2 ^ 80 - 1 else 0) +
          packFn 80 19881 (fun s => if s = 10081 then 2 ^ 80 - 1 else 0) +
          packFn 80 19881 (fun s => if s = 9941 then 2 ^ 80 - 1 else 0) := by
      rw [h0, h1, h2, h3]
    _ = packFn 80 19881 (fun s => if neighbourIndex s then 2 ^ 80 - 1 else 0) := by
      rw [← packFn_add, ← packFn_add, ← packFn_add, hfun]
      rfl

private theorem allMask_packed : allMask = packFn 80 19881 (fun _ => 2 ^ 80 - 1) := by
  have hr := repeatLane_eq 80 19881 (2 ^ 80 - 1) (by decide)
  have hconst : allMask = repeatLane 80 19881 (2 ^ 80 - 1) := by
    unfold allMask repeatLane
    rw [Nat.mul_div_cancel _ (by omega)]
  rw [hconst, hr]

private def complementLane (s : Nat) : Nat :=
  if s < 19881 ∧ ¬ neighbourIndex s then 2 ^ 80 - 1 else 0

private theorem allMask_sub_neighbours :
    allMask - centreNeighbourMasks = packFn 80 19881 complementLane := by
  have hpoint (s : Nat) (hs : s < 19881) :
      (if neighbourIndex s then 2 ^ 80 - 1 else 0) + complementLane s =
        2 ^ 80 - 1 := by
    by_cases hn : neighbourIndex s <;> simp [complementLane, hs, hn]
  have hsum : allMask = centreNeighbourMasks + packFn 80 19881 complementLane := by
    rw [allMask_packed, centreNeighbourMasks_packed]
    rw [← packFn_add]
    apply packFn_congr
    intro s hs
    exact (hpoint s hs).symm
  omega

private theorem neighbourIndex_iff (s : Nat) :
    neighbourIndex s ↔ ∃ d : Compass, gridSite s = -d.step := by
  constructor
  · intro h
    rcases h with h | h | h | h
    · exact ⟨.east, (gridSite_eq_neighbour_iff s .east).2 (by norm_num [siteIndex, Compass.step] at h ⊢; exact h)⟩
    · exact ⟨.north, (gridSite_eq_neighbour_iff s .north).2 (by norm_num [siteIndex, Compass.step] at h ⊢; exact h)⟩
    · exact ⟨.west, (gridSite_eq_neighbour_iff s .west).2 (by norm_num [siteIndex, Compass.step] at h ⊢; exact h)⟩
    · exact ⟨.south, (gridSite_eq_neighbour_iff s .south).2 (by norm_num [siteIndex, Compass.step] at h ⊢; exact h)⟩
  · rintro ⟨d, h⟩
    cases d with
    | east => exact Or.inl ((gridSite_eq_neighbour_iff s .east).1 h)
    | north => exact Or.inr (Or.inl ((gridSite_eq_neighbour_iff s .north).1 h))
    | west => exact Or.inr (Or.inr (Or.inl ((gridSite_eq_neighbour_iff s .west).1 h)))
    | south => exact Or.inr (Or.inr (Or.inr ((gridSite_eq_neighbour_iff s .south).1 h)))

theorem main : CertData.H3.Bridge.DeadMaskLeaf := by
  unfold CertData.H3.Bridge.DeadMaskLeaf
  intro j s hs
  fin_cases j
  · change lane (oneMask (siteIndex (-Compass.east.step))) 80 s =
      if gridSite s = -Compass.east.step then 2 ^ 80 - 1 else 0
    rw [lane_oneMask]
    simp only [← gridSite_eq_neighbour_iff s .east]
  · change lane (oneMask (siteIndex (-Compass.north.step))) 80 s =
      if gridSite s = -Compass.north.step then 2 ^ 80 - 1 else 0
    rw [lane_oneMask]
    simp only [← gridSite_eq_neighbour_iff s .north]
  · change lane (oneMask (siteIndex (-Compass.west.step))) 80 s =
      if gridSite s = -Compass.west.step then 2 ^ 80 - 1 else 0
    rw [lane_oneMask]
    simp only [← gridSite_eq_neighbour_iff s .west]
  · change lane (oneMask (siteIndex (-Compass.south.step))) 80 s =
      if gridSite s = -Compass.south.step then 2 ^ 80 - 1 else 0
    rw [lane_oneMask]
    simp only [← gridSite_eq_neighbour_iff s .south]
  · change lane (allMask - centreNeighbourMasks) 80 s =
      if (∀ d : Compass, gridSite s ≠ -d.step) then 2 ^ 80 - 1 else 0
    rw [allMask_sub_neighbours]
    rw [lane_packFn]
    · have hiff : (∀ d : Compass, gridSite s ≠ -d.step) ↔ ¬ neighbourIndex s := by
        rw [neighbourIndex_iff s]
        simp
      simp [complementLane, hs, hiff]
    · intro t ht
      unfold complementLane
      split_ifs <;> omega

#print axioms main

end AKLT.W.H3C023
