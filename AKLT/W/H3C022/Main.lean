module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C022

open AKLT.Defs AKLT.Cert.H3 AKLT.Gen.Packed CertData.H3.Bridge

private theorem maxLane_lt : 2 ^ 80 - 1 < 2 ^ 80 := by
  exact Nat.sub_lt (by positivity) (by decide)

private theorem lane_oneMask (i s : Nat) :
    lane (AKLT.Cert.H3.oneMask i) 80 s = if i = s then 2 ^ 80 - 1 else 0 := by
  rw [AKLT.Cert.H3.oneMask, lane_shiftLeft _ _ _ _ (by omega)]
  by_cases his : i ≤ s
  · by_cases heq : i = s
    · subst s
      simp [lane]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s - i ≠ 0)
      rw [if_pos his, hk, lane_succ]
      have hz : (2 ^ 80 - 1) / 2 ^ 80 = 0 := Nat.div_eq_of_lt maxLane_lt
      simp [lane, hz, heq]
  · have hne : i ≠ s := by omega
    simp [his, hne]

private theorem oneMask_fits {i : Nat} (hi : i < 19881) :
    Fits (AKLT.Cert.H3.oneMask i) 80 19881 := by
  change AKLT.Cert.H3.oneMask i < 2 ^ (80 * 19881)
  calc
    AKLT.Cert.H3.oneMask i = (2 ^ 80 - 1) <<< (80 * i) := rfl
    _ < 2 ^ (80 + 80 * i) := Nat.shiftLeft_lt maxLane_lt
    _ ≤ 2 ^ (80 * 19881) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

private theorem lane_oneMask_add {i j s : Nat} (hij : i ≠ j)
    (hi : i < 19881) (hj : j < 19881) (hs : s < 19881) :
    lane (AKLT.Cert.H3.oneMask i + AKLT.Cert.H3.oneMask j) 80 s =
      (if i = s then 2 ^ 80 - 1 else 0) + (if j = s then 2 ^ 80 - 1 else 0) := by
  have hcarry : ∀ t < 19881,
      lane (AKLT.Cert.H3.oneMask i) 80 t + lane (AKLT.Cert.H3.oneMask j) 80 t < 2 ^ 80 := by
    intro t ht
    rw [lane_oneMask, lane_oneMask]
    by_cases hit : i = t
    · have hjt : j ≠ t := by
        intro h
        apply hij
        rw [hit, h]
      simp [hit, hjt]
    · by_cases hjt : j = t <;> simp [hit, hjt]
  rw [lane_add (oneMask_fits hi) (oneMask_fits hj) hcarry s hs,
    lane_oneMask, lane_oneMask]

private theorem gridSite_eq_coords (s r c : Nat) (hc : c < 141) :
    gridSite s = ((r : Int) - 70, (c : Int) - 70) ↔ s = r * 141 + c := by
  constructor
  · intro h
    have hrow : s / 141 = r := by
      have h' := congrArg Prod.fst h
      dsimp [gridSite] at h'
      omega
    have hcol : s % 141 = c := by
      have h' := congrArg Prod.snd h
      dsimp [gridSite] at h'
      omega
    omega
  · intro h
    subst s
    have hrow : (r * 141 + c) / 141 = r := by omega
    have hcol : (r * 141 + c) % 141 = c := by omega
    simp [gridSite, hrow, hcol]

theorem main : CertData.H3.Bridge.KnownMaskLeaf := by
  intro d₀ d hd s hs
  cases d₀ with
  | east => contradiction
  | north =>
    have hi : siteIndex kernelStart = 9799 := by norm_num [siteIndex, kernelStart]
    have hj : siteIndex (kernelStart + Compass.north.step) = 9800 := by
      norm_num [siteIndex, kernelStart, Compass.step]
    have hhi : 9799 < 19881 := by norm_num
    have hhj : 9800 < 19881 := by norm_num
    have hneq : 9799 ≠ 9800 := by norm_num
    have hstart : gridSite s = kernelStart ↔ s = 9799 := by
      simpa [kernelStart] using gridSite_eq_coords s 69 70 (by norm_num)
    have hnext : gridSite s = kernelStart + Compass.north.step ↔ s = 9800 := by
      simpa [kernelStart, Compass.step] using gridSite_eq_coords s 69 71 (by norm_num)
    cases d <;> simp [AKLT.Cert.H3.knownMask, Compass.reverse, hi, hj, hstart, hnext,
      lane_oneMask, lane_oneMask_add, eq_comm, hneq, hhi, hhj, hs]
    all_goals
      by_cases hs₁ : s = 9799 <;> by_cases hs₂ : s = 9800 <;> simp_all [hneq]
  | west =>
    have hi : siteIndex kernelStart = 9799 := by norm_num [siteIndex, kernelStart]
    have hj : siteIndex (kernelStart + Compass.west.step) = 9658 := by
      norm_num [siteIndex, kernelStart, Compass.step]
    have hhi : 9799 < 19881 := by norm_num
    have hhj : 9658 < 19881 := by norm_num
    have hneq : 9799 ≠ 9658 := by norm_num
    have hstart : gridSite s = kernelStart ↔ s = 9799 := by
      simpa [kernelStart] using gridSite_eq_coords s 69 70 (by norm_num)
    have hnext : gridSite s = kernelStart + Compass.west.step ↔ s = 9658 := by
      simpa [kernelStart, Compass.step] using gridSite_eq_coords s 68 70 (by norm_num)
    cases d <;> simp [AKLT.Cert.H3.knownMask, Compass.reverse, hi, hj, hstart, hnext,
      lane_oneMask, lane_oneMask_add, eq_comm, hneq, hhi, hhj, hs]
    all_goals
      by_cases hs₁ : s = 9799 <;> by_cases hs₂ : s = 9658 <;> simp_all [hneq]
  | south =>
    have hi : siteIndex kernelStart = 9799 := by norm_num [siteIndex, kernelStart]
    have hj : siteIndex (kernelStart + Compass.south.step) = 9798 := by
      norm_num [siteIndex, kernelStart, Compass.step]
    have hhi : 9799 < 19881 := by norm_num
    have hhj : 9798 < 19881 := by norm_num
    have hneq : 9799 ≠ 9798 := by norm_num
    have hstart : gridSite s = kernelStart ↔ s = 9799 := by
      simpa [kernelStart] using gridSite_eq_coords s 69 70 (by norm_num)
    have hnext : gridSite s = kernelStart + Compass.south.step ↔ s = 9798 := by
      simpa [kernelStart, Compass.step] using gridSite_eq_coords s 69 69 (by norm_num)
    cases d <;> simp [AKLT.Cert.H3.knownMask, Compass.reverse, hi, hj, hstart, hnext,
      lane_oneMask, lane_oneMask_add, eq_comm, hneq, hhi, hhj, hs]
    all_goals
      by_cases hs₁ : s = 9799 <;> by_cases hs₂ : s = 9798 <;> simp_all [hneq]

#print axioms main

end AKLT.W.H3C022
