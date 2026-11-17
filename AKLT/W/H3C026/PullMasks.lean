module
public import AKLT.W.H3C026.Masks

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option maxRecDepth 100000

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Gen.Packed

namespace AKLT.W.H3C026

theorem lane_full (b n s : Nat) :
    lane (2^(b*n)-1) b s = if s<n then 2^b-1 else 0 := by
  rw [full_pack, lane_packFn]
  intro i hi
  have h : 0<2^b := by positivity
  omega

theorem lane_refine (P b w r c : Nat) (hc : c<w) :
    lane P b (r*w+c) = lane (lane P (b*w) r) b c := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<b
  · have hci : b*c+i<b*w := by nlinarith
    simp only [testBit_lane, hi, hci, decide_true, Bool.true_and]
    congr 1
    ring
  · simp [testBit_lane, hi]

theorem lanes_ext_all (P Q b : Nat) (hb : 0<b)
    (h : ∀ s, lane P b s = lane Q b s) : P=Q := by
  apply Nat.eq_of_testBit_eq
  intro i
  have he := congrArg (fun n => n.testBit (i%b)) (h (i/b))
  have hi : i%b<b := Nat.mod_lt i hb
  have hidx : b*(i/b)+i%b=i := by
    simpa only [Nat.add_comm] using Nat.mod_add_div i b
  simpa only [testBit_lane, hi, decide_true, Bool.true_and, hidx] using he

theorem firstColumn_lane (s : Nat) :
    lane firstColumn 80 s = if s<19881 ∧ s%141=0 then 2^80-1 else 0 := by
  have hc : s%141<141 := Nat.mod_lt _ (by decide)
  have hr : (s/141)*141+s%141=s := by omega
  calc
    lane firstColumn 80 s = lane (lane firstColumn (80*141) (s/141)) 80 (s%141) := by
      simpa only [hr] using lane_refine firstColumn 80 141 (s/141) (s%141) hc
    _ = _ := by
      rw [firstColumn, repeatLane_eq _ _ _ (by decide),
        lane_packFn _ _ _ (by intro i hi; decide +kernel)]
      by_cases hs : s<19881
      · have hrow : s/141<141 := by omega
        rw [if_pos hrow, lane_full 80 1]
        simp only [hs, true_and, Nat.lt_one_iff]
      · have hrow : ¬s/141<141 := by omega
        simp [hrow, hs, lane]

theorem lastColumn_lane (s : Nat) :
    lane lastColumn 80 s = if s<19881 ∧ s%141=140 then 2^80-1 else 0 := by
  calc
    lane lastColumn 80 s = (if 140 ≤ s then lane firstColumn 80 (s-140) else 0) :=
      lane_shiftLeft firstColumn 80 140 s (by decide)
    _ = _ := by
      simp only [firstColumn_lane]
      split_ifs <;> first | rfl | (exfalso; omega)

theorem firstRow_lane (s : Nat) :
    lane firstRow 80 s = if s<19881 ∧ s/141=0 then 2^80-1 else 0 := by
  rw [firstRow, lane_full]
  have he : s<141 ↔ (s<19881 ∧ s/141=0) := by omega
  simp only [he]

theorem lastRow_lane (s : Nat) :
    lane lastRow 80 s = if s<19881 ∧ s/141=140 then 2^80-1 else 0 := by
  calc
    lane lastRow 80 s = (if 19740 ≤ s then lane firstRow 80 (s-19740) else 0) :=
      lane_shiftLeft firstRow 80 19740 s (by decide)
    _ = _ := by
      simp only [firstRow, lane_full]
      split_ifs <;> first | rfl | (exfalso; omega)

def boundaryAt (d : Compass) (s : Nat) : Prop := match d with
  | .east => s/141=140 | .north => s%141=140
  | .west => s/141=0 | .south => s%141=0

instance (d : Compass) (s : Nat) : Decidable (boundaryAt d s) := by
  unfold boundaryAt; cases d <;> infer_instance

theorem boundaryMask_lane (d : Compass) (s : Nat) :
    lane (boundaryMask d) 80 s = if s<19881 ∧ boundaryAt d s then 2^80-1 else 0 := by
  cases d <;>
    simp only [boundaryMask, lastRow_lane, lastColumn_lane, firstRow_lane, firstColumn_lane]
  all_goals split_ifs <;> simp_all [boundaryAt] <;> omega

theorem boundaryMask_pack (d : Compass) :
    boundaryMask d = packFn 80 19881 (fun s => if boundaryAt d s then 2^80-1 else 0) := by
  apply lanes_ext_all _ _ 80 (by decide)
  intro s
  rw [boundaryMask_lane, lane_packFn _ _ _ (by intro i hi; split <;> norm_num)]
  by_cases hs : s<19881 <;> simp [hs]

theorem complementMask_pack (d : Compass) :
    allMask-boundaryMask d =
      packFn 80 19881 (fun s => if boundaryAt d s then 0 else 2^80-1) := by
  rw [allMask, full_pack, boundaryMask_pack, pack_sub]
  · apply packFn_congr
    intro s hs
    by_cases h : boundaryAt d s <;> simp [h]
  · intro s hs
    split <;> omega

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.lane_full
#print axioms AKLT.W.H3C026.lane_refine
#print axioms AKLT.W.H3C026.lanes_ext_all
#print axioms AKLT.W.H3C026.firstColumn_lane
#print axioms AKLT.W.H3C026.lastColumn_lane
#print axioms AKLT.W.H3C026.firstRow_lane
#print axioms AKLT.W.H3C026.lastRow_lane
#print axioms AKLT.W.H3C026.boundaryMask_lane
#print axioms AKLT.W.H3C026.boundaryMask_pack
#print axioms AKLT.W.H3C026.complementMask_pack
