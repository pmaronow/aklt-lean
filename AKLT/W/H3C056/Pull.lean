module
public import AKLT.W.H3C056.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C056
open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3
set_option maxRecDepth 2048
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] allMask boundaryMask Nat.shiftLeft Nat.shiftRight

theorem lane_masked (P : Nat) {M : Nat} {p : Nat → Prop} (hM : Mask M p)
    (s : Nat) (hs : s < 19881) :
    lane (Nat.land P M) 80 s = if p s then lane P 80 s else 0 := by
  rw [lane_land, hM.2 s hs]
  by_cases h : p s
  · simp only [h, ite_true]
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (lane_lt P 80 s)
  · simp only [h, ite_false, Nat.land_eq, Nat.and_zero]

def shiftedPlane (P : Nat) (d : Compass) : Nat := match d with
  | .east => P >>> (80*141) | .north => P >>> 80
  | .west => P <<< (80*141) | .south => P <<< 80

theorem pull_lane_raw (P Z : Nat) (d : Compass) (hZ : Z < 2^26)
    (s : Nat) (hs : s < 19881) :
    lane (pull P Z d) 80 s =
      if boundary d s then Z else lane (shiftedPlane P d) 80 s := by
  have hcomp := mask_sub mask_all (mask_boundary d) (by simp)
  have hZ' : Z < 2^80 := hZ.trans_le (by decide)
  have hr (i : Nat) (hi : i < 19881) : lane (repeatLane 80 19881 Z) 80 i = Z := by
    rw [repeatLane_eq _ _ _ (by decide), lane_packFn _ _ _ (by intros; exact hZ'), ite_eq_left hi]
  have h1 (i : Nat) (hi : i < 19881) :
      lane (Nat.land (shiftedPlane P d) (allMask-boundaryMask d)) 80 i =
        if boundary d i then 0 else lane (shiftedPlane P d) 80 i := by
    rw [lane_masked _ hcomp i hi]
    by_cases h : boundary d i <;> simp [h]
  have h2 (i : Nat) (hi : i < 19881) :
      lane (Nat.land (repeatLane 80 19881 Z) (boundaryMask d)) 80 i =
        if boundary d i then Z else 0 := by
    rw [lane_masked _ (mask_boundary d) i hi, hr i hi]
  have hf1 : Fits (Nat.land (shiftedPlane P d) (allMask-boundaryMask d)) 80 19881 :=
    lt_of_le_of_lt Nat.and_le_right hcomp.1
  have hf2 : Fits (Nat.land (repeatLane 80 19881 Z) (boundaryMask d)) 80 19881 :=
    lt_of_le_of_lt Nat.and_le_right (mask_boundary d).1
  change lane (Nat.land (shiftedPlane P d) (allMask-boundaryMask d) +
    Nat.land (repeatLane 80 19881 Z) (boundaryMask d)) 80 s = _
  rw [lane_add hf1 hf2 (by
    intro i hi
    rw [h1 i hi, h2 i hi]
    by_cases h : boundary d i <;> simp only [h, ite_true, ite_false, Nat.zero_add, Nat.add_zero]
    · exact hZ'
    · exact lane_lt _ _ _) s hs, h1 s hs, h2 s hs]
  split_ifs <;> omega

theorem pull_lane (P Z : Nat) (d : Compass) (hZ : Z < 2^26)
    (s : Nat) (hs : s < 19881) :
    lane (pull P Z d) 80 s =
      if gridSite s+d.step ∈ square (0,0) certificateRadius
      then lane P 80 (siteIndex (gridSite s+d.step)) else Z := by
  rw [pull_lane_raw P Z d hZ s hs]
  by_cases h : boundary d s
  · rw [ite_eq_left h, ite_eq_right (by simpa only [step_box s hs d, not_not] using h)]
  · rw [ite_eq_right h, ite_eq_left ((step_box s hs d).mpr h), index_step s hs d h]
    cases d
    · unfold shiftedPlane
      exact lane_shiftRight P 80 141 s
    · unfold shiftedPlane
      simpa only [Nat.mul_one] using lane_shiftRight P 80 1 s
    · have hs' : 141 ≤ s := by dsimp [boundary] at h; omega
      unfold shiftedPlane
      rw [lane_shiftLeft P 80 141 s (by decide), ite_eq_left hs']
    · have hs' : 1 ≤ s := by
        have hm := Nat.mod_lt s (by decide : 0<141)
        dsimp [boundary] at h
        omega
      unfold shiftedPlane
      simpa only [Nat.mul_one, hs', ite_true] using lane_shiftLeft P 80 1 s (by decide)

end
end AKLT.W.H3C056
