module
public import AKLT.W.H3C026.Masks

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Gen.Packed

namespace AKLT.W.H3C026

theorem deadMask_proved : CertData.H3.Bridge.DeadMaskLeaf := by
  intro j s hs
  by_cases hj : j.val<4
  · have hbox : inBox (-(direction j.val).step) := by
      interval_cases hjv : j.val <;> decide +kernel
    have hi : siteIndex (-(direction j.val).step)<19881 := by
      interval_cases hjv : j.val <;> decide +kernel
    simp only [deadMask, hj, ↓reduceIte, centreNeighbourMask, oneMask]
    rw [spike_pack 80 19881 _ hi,
      lane_packFn _ _ _ (by intro i hi; split <;> norm_num), if_pos hs]
    simp only [gridSite_eq s _ hbox]
  · have hj₄ : j.val=4 := by omega
    let a := siteIndex (-Compass.east.step)
    let b := siteIndex (-Compass.north.step)
    let c := siteIndex (-Compass.west.step)
    let d := siteIndex (-Compass.south.step)
    have hi : a<19881 ∧ b<19881 ∧ c<19881 ∧ d<19881 ∧
        b≠a ∧ c≠a ∧ c≠b ∧ d≠a ∧ d≠b ∧ d≠c := by decide +kernel
    rcases hi with ⟨ha,hb,hc,hd,hba,hca,hcb,hda,hdb,hdc⟩
    simp only [deadMask, hj, ↓reduceIte]
    have he : allMask-centreNeighbourMasks =
        (2^(80*19881)-1) - (2^80-1) <<< (80*a) - (2^80-1) <<< (80*b) -
          (2^80-1) <<< (80*c) - (2^80-1) <<< (80*d) := by
      simp only [centreNeighbourMasks, List.range_succ, List.range_zero,
        List.foldl_append, List.foldl_cons, List.foldl_nil, centreNeighbourMask,
        direction, Nat.zero_add, allMask, oneMask, Nat.sub_sub, Nat.add_assoc, a,b,c,d]
    rw [he, full_pack, erase_full 80 19881 a ha,
      erase_mask 80 19881 (fun s => s≠a) b hb hba,
      erase_mask 80 19881 (fun s => s≠a ∧ s≠b) c hc ⟨hca,hcb⟩,
      erase_mask 80 19881 (fun s => (s≠a ∧ s≠b) ∧ s≠c) d hd ⟨⟨hda,hdb⟩,hdc⟩,
      lane_packFn _ _ _ (by intro i hi; split <;> norm_num), if_pos hs]
    have heast : inBox (-Compass.east.step) := by decide +kernel
    have hnorth : inBox (-Compass.north.step) := by decide +kernel
    have hwest : inBox (-Compass.west.step) := by decide +kernel
    have hsouth : inBox (-Compass.south.step) := by decide +kernel
    have hforall : (∀ e : Compass, gridSite s ≠ -e.step) ↔
        s≠a ∧ s≠b ∧ s≠c ∧ s≠d := by
      constructor
      · intro h
        exact ⟨(not_congr (gridSite_eq s _ heast)).mp (h .east),
          (not_congr (gridSite_eq s _ hnorth)).mp (h .north),
          (not_congr (gridSite_eq s _ hwest)).mp (h .west),
          (not_congr (gridSite_eq s _ hsouth)).mp (h .south)⟩
      · rintro ⟨h₀,h₁,h₂,h₃⟩ e
        cases e with
        | east => exact (not_congr (gridSite_eq s _ heast)).mpr h₀
        | north => exact (not_congr (gridSite_eq s _ hnorth)).mpr h₁
        | west => exact (not_congr (gridSite_eq s _ hwest)).mpr h₂
        | south => exact (not_congr (gridSite_eq s _ hsouth)).mpr h₃
    simp only [hforall, and_assoc]

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.deadMask_proved
