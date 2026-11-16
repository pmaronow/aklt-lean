import AKLT.W.H3C026.Local

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Gen.Packed

namespace AKLT.W.H3C026

theorem full_pack (b n : Nat) :
    2^(b*n)-1 = packFn b n (fun _ => 2^b-1) := by
  induction n with
  | zero => simp [packFn]
  | succ n ih =>
    simp only [packFn, ←ih, Nat.mul_add, Nat.mul_one, pow_add]
    have h₁ : 0 < 2^b := by positivity
    have h₂ : 0 < 2^(b*n) := by positivity
    have h₃ : 0 < 2^(b*n)*2^b := by positivity
    have e₁ := Nat.sub_add_cancel (show 1 ≤ 2^b by omega)
    have e₂ := Nat.sub_add_cancel (show 1 ≤ 2^(b*n) by omega)
    have e₃ := Nat.sub_add_cancel (show 1 ≤ 2^(b*n)*2^b by omega)
    nlinarith

theorem spike_pack (b n t : Nat) (ht : t < n) :
    (2^b-1) <<< (b*t) = packFn b n (fun s => if s=t then 2^b-1 else 0) := by
  rw [packFn_eq_sum, Finset.sum_eq_single t]
  · simp [Nat.shiftLeft_eq]
  · intro s hs hst
    simp [hst]
  · intro h
    exact (h (Finset.mem_range.mpr ht)).elim

theorem pack_sub (b n : Nat) (f g : Nat → Nat) (h : ∀ s<n, g s ≤ f s) :
    packFn b n f - packFn b n g = packFn b n (fun s => f s - g s) := by
  have he : packFn b n f = packFn b n (fun s => f s - g s) + packFn b n g := by
    rw [←packFn_add]
    apply packFn_congr
    intro s hs
    exact (Nat.sub_add_cancel (h s hs)).symm
  omega

theorem erase_mask (b n : Nat) (p : Nat → Prop) [DecidablePred p]
    (t : Nat) (ht : t < n) (hpt : p t) :
    packFn b n (fun s => if p s then 2^b-1 else 0) - (2^b-1) <<< (b*t) =
      packFn b n (fun s => if p s ∧ s≠t then 2^b-1 else 0) := by
  rw [spike_pack b n t ht, pack_sub]
  · apply packFn_congr
    intro s hs
    by_cases hp : p s <;> by_cases he : s=t <;> simp_all
  · intro s hs
    by_cases he : s=t <;> simp_all

theorem erase_full (b n t : Nat) (ht : t<n) :
    packFn b n (fun _ => 2^b-1) - (2^b-1) <<< (b*t) =
      packFn b n (fun s => if s≠t then 2^b-1 else 0) := by
  simpa only [ite_true, true_and] using erase_mask b n (fun _ => True) t ht True.intro

theorem siteIndex_gridSite (s : Nat) : siteIndex (gridSite s) = s := by
  simp [siteIndex, gridSite]
  omega

theorem gridSite_siteIndex (x : Plane) (hx : inBox x) : gridSite (siteIndex x) = x := by
  rcases x with ⟨u,v⟩
  rcases hx with ⟨hu₀,hu₁,hv₀,hv₁⟩
  apply Prod.ext <;> simp only [gridSite, siteIndex, Prod.fst, Prod.snd]
  all_goals omega

theorem gridSite_eq (s : Nat) (x : Plane) (hx : inBox x) :
    gridSite s = x ↔ s = siteIndex x := by
  constructor
  · intro h; simpa [siteIndex_gridSite] using congrArg siteIndex h
  · rintro rfl; exact gridSite_siteIndex x hx

theorem ordinaryMask_proved : CertData.H3.Bridge.OrdinaryMaskLeaf := by
  intro X d₀ hcase s hs
  let c := siteIndex kernelCentre
  let t := siteIndex (kernelTarget X)
  let u := siteIndex kernelStart
  let v := siteIndex (kernelStart+d₀.step)
  have hi : c<19881 ∧ t<19881 ∧ u<19881 ∧ v<19881 ∧
      t≠c ∧ u≠c ∧ u≠t ∧ v≠c ∧ v≠t ∧ v≠u := by
    cases X <;> cases d₀ <;> simp [stationaryCases] at hcase <;> decide +kernel
  rcases hi with ⟨hc,ht,hu,hv,htc,huc,hut,hvc,hvt,hvu⟩
  have hcbox : inBox kernelCentre := by decide +kernel
  have htbox : inBox (kernelTarget X) := by cases X <;> decide +kernel
  have hubox : inBox kernelStart := by decide +kernel
  have hvbox : inBox (kernelStart+d₀.step) := by cases d₀ <;> decide +kernel
  change lane ((2^(80*19881)-1) - (2^80-1) <<< (80*c) -
    (2^80-1) <<< (80*t) - (2^80-1) <<< (80*u) - (2^80-1) <<< (80*v)) 80 s = _
  rw [full_pack, erase_full 80 19881 c hc,
    erase_mask 80 19881 (fun s => s≠c) t ht htc,
    erase_mask 80 19881 (fun s => s≠c ∧ s≠t) u hu ⟨huc,hut⟩,
    erase_mask 80 19881 (fun s => (s≠c ∧ s≠t) ∧ s≠u) v hv ⟨⟨hvc,hvt⟩,hvu⟩]
  rw [lane_packFn _ _ _ (by intro i hi; split <;> norm_num), if_pos hs]
  simp only [gridSite_eq s kernelCentre hcbox, gridSite_eq s (kernelTarget X) htbox,
    gridSite_eq s kernelStart hubox, gridSite_eq s (kernelStart+d₀.step) hvbox]
  by_cases hsc : s=c <;> by_cases hst : s=t <;> by_cases hsu : s=u <;>
    by_cases hsv : s=v <;> simp_all [c,t,u,v]

theorem pack_zero (b n : Nat) : packFn b n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [packFn, ih]

theorem merge_masks (b n : Nat) (p q : Nat → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ s<n, ¬(p s ∧ q s)) :
    packFn b n (fun s => if p s then 2^b-1 else 0) +
      packFn b n (fun s => if q s then 2^b-1 else 0) =
      packFn b n (fun s => if p s ∨ q s then 2^b-1 else 0) := by
  rw [←packFn_add]
  apply packFn_congr
  intro s hs
  have hh := h s hs
  by_cases hp : p s <;> by_cases hq : q s <;> simp_all


end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.full_pack
#print axioms AKLT.W.H3C026.spike_pack
#print axioms AKLT.W.H3C026.pack_sub
#print axioms AKLT.W.H3C026.erase_mask
#print axioms AKLT.W.H3C026.siteIndex_gridSite
#print axioms AKLT.W.H3C026.gridSite_siteIndex
#print axioms AKLT.W.H3C026.gridSite_eq
#print axioms AKLT.W.H3C026.erase_full
#print axioms AKLT.W.H3C026.ordinaryMask_proved
#print axioms AKLT.W.H3C026.pack_zero
#print axioms AKLT.W.H3C026.merge_masks
