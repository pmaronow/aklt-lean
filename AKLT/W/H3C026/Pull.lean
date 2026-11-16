import AKLT.W.H3C026.PullMasks
import AKLT.W.H3C026.Routing

set_option maxRecDepth 100000

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Gen.Packed

namespace AKLT.W.H3C026

def shiftedPlane (P : Nat) (d : Compass) : Nat := match d with
  | .east => P >>> (80*141) | .north => P >>> 80
  | .west => P <<< (80*141) | .south => P <<< 80

theorem pull_boundary_lane (P Z : Nat) (d : Compass) (hZ : Z<2^26)
    (s : Nat) (hs : s<19881) :
    lane (pull P Z d) 80 s = if boundaryAt d s then Z else lane (shiftedPlane P d) 80 s := by
  have hZ' : Z<2^80 := hZ.trans_le (by decide +kernel)
  let A := Nat.land (shiftedPlane P d) (allMask-boundaryMask d)
  let B := Nat.land (repeatLane 80 19881 Z) (boundaryMask d)
  have hAf : Fits A 80 19881 := by
    apply lt_of_le_of_lt Nat.and_le_right
    rw [complementMask_pack]
    apply packFn_lt
    intro i hi
    split <;> norm_num
  have hBf : Fits B 80 19881 := by
    apply lt_of_le_of_lt Nat.and_le_right
    rw [boundaryMask_pack]
    apply packFn_lt
    intro i hi
    split <;> norm_num
  have hAl (i : Nat) (hi : i<19881) : lane A 80 i =
      if boundaryAt d i then 0 else lane (shiftedPlane P d) 80 i := by
    have hm : lane (allMask-boundaryMask d) 80 i =
        if ¬boundaryAt d i then 2^80-1 else 0 := by
      rw [complementMask_pack, lane_packFn _ _ _ (by intro j hj; split <;> norm_num), if_pos hi]
      by_cases h : boundaryAt d i <;> simp [h]
    rw [lane_select _ _ _ _ _ hm]
    by_cases h : boundaryAt d i <;> simp [h]
  have hBl (i : Nat) (hi : i<19881) : lane B 80 i = if boundaryAt d i then Z else 0 := by
    have hm : lane (boundaryMask d) 80 i = if boundaryAt d i then 2^80-1 else 0 := by
      simp only [boundaryMask_lane, hi, true_and]
    rw [lane_select _ _ _ _ _ hm, repeatLane_eq _ _ _ (by decide),
      lane_packFn _ _ _ (fun _ _ => hZ'), if_pos hi]
  have hsum (i : Nat) (hi : i<19881) : lane A 80 i + lane B 80 i < 2^80 := by
    rw [hAl i hi, hBl i hi]
    by_cases h : boundaryAt d i
    · simpa [h] using hZ'
    · simpa [h] using lane_lt (shiftedPlane P d) 80 i
  change lane (A+B) 80 s = _
  rw [lane_add hAf hBf hsum s hs, hAl s hs, hBl s hs]
  by_cases h : boundaryAt d s <;> simp [h]

theorem successor_inside (d : Compass) (s : Nat) (hs : s<19881) :
    inBox (gridSite s+d.step) ↔ ¬boundaryAt d s := by
  cases d <;> simp [inBox, gridSite, Compass.step, boundaryAt] <;> omega

def shiftedIndex (d : Compass) (s : Nat) : Nat := match d with
  | .east => s+141 | .north => s+1 | .west => s-141 | .south => s-1

theorem successor_index (d : Compass) (s : Nat) (hs : s<19881) (hb : ¬boundaryAt d s) :
    siteIndex (gridSite s+d.step) = shiftedIndex d s := by
  cases d <;> simp_all [siteIndex, gridSite, Compass.step, shiftedIndex, boundaryAt] <;> omega

theorem shifted_lane (P : Nat) (d : Compass) (s : Nat) (hs : s<19881)
    (hb : ¬boundaryAt d s) :
    lane (shiftedPlane P d) 80 s = lane P 80 (siteIndex (gridSite s+d.step)) := by
  rw [successor_index d s hs hb]
  cases d with
  | east => exact lane_shiftRight P 80 141 s
  | north => exact lane_shiftRight P 80 1 s
  | west =>
    have hi : 141 ≤ s := by simp only [boundaryAt] at hb; omega
    exact (lane_shiftLeft P 80 141 s (by decide)).trans (ite_eq_left hi)
  | south =>
    have hi : 1 ≤ s := by simp only [boundaryAt] at hb; omega
    exact (lane_shiftLeft P 80 1 s (by decide)).trans (ite_eq_left hi)

theorem pull_proved : CertData.H3.Bridge.PullLeaf := by
  intro P Z d hP hZ s hs
  rw [pull_boundary_lane P Z d hZ s hs]
  by_cases hb : boundaryAt d s
  · have hout : ¬inBox (gridSite s+d.step) :=
      fun hin => ((successor_inside d s hs).mp hin) hb
    simp only [hb, hout, ↓reduceIte]
  · rw [if_neg hb, if_pos ((successor_inside d s hs).mpr hb)]
    exact shifted_lane P d s hs hb

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.pull_boundary_lane
#print axioms AKLT.W.H3C026.successor_inside
#print axioms AKLT.W.H3C026.successor_index
#print axioms AKLT.W.H3C026.shifted_lane
#print axioms AKLT.W.H3C026.pull_proved
