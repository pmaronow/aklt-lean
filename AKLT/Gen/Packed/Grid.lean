import AKLT.Gen.Packed.Routing
namespace AKLT.Gen.Packed

private theorem grid_lt {w r c : Nat} (hr : r < w) (hc : c < w) :
    gridIndex w r c < w*w := by unfold gridIndex; nlinarith
private theorem grid_mod {w r c : Nat} (hc : c < w) :
    gridIndex w r c % w = c := by simp [gridIndex, Nat.add_mod, Nat.mod_eq_of_lt hc]

/-- Translate a square plane one column to the right, filling the boundary with zero. -/
theorem moveRight_grid {P b w r c : Nat} (hb : 0 < b) (hr : r < w) (hc : c < w) :
    lane (moveRight P b w) b (gridIndex w r c) =
      if 0 < c then lane P b (gridIndex w r (c-1)) else 0 := by
  rw [lane_moveRight _ _ _ _ hb, grid_mod hc]
  simp only [grid_lt hr hc, true_and]
  split_ifs with h
  · congr 1
    unfold gridIndex
    omega
  · rfl

/-- Translate one column left; the last column is zero. -/
theorem moveLeft_grid {P b w r c : Nat} (hr : r < w) (hc : c < w) :
    lane (moveLeft P b w) b (gridIndex w r c) =
      if c+1 < w then lane P b (gridIndex w r (c+1)) else 0 := by
  rw [lane_moveLeft, grid_mod hc]
  simp only [grid_lt hr hc, true_and]
  rfl

/-- Translate one row down; the first row is zero. -/
theorem moveDown_grid {P b w r c : Nat} (hb : 0 < b) (hr : r < w) (hc : c < w) :
    lane (moveDown P b w) b (gridIndex w r c) =
      if 0 < r then lane P b (gridIndex w (r-1) c) else 0 := by
  rw [lane_moveDown _ _ _ _ hb]
  have he : (w ≤ gridIndex w r c) ↔ 0 < r := by
    unfold gridIndex
    constructor
    · intro h
      by_contra hn
      have hz : r = 0 := by omega
      simp [hz] at h
      omega
    · intro h; nlinarith
  simp only [grid_lt hr hc, true_and, he]
  split_ifs with h
  · congr 1
    unfold gridIndex
    have hm := Nat.sub_add_cancel (show 1 ≤ r by omega)
    have hm' := congrArg (fun q => q*w) hm
    simp only [Nat.add_mul, Nat.one_mul] at hm'
    have hle : w ≤ r*w+c := by nlinarith
    omega
  · rfl

/-- Translate one row up; finite input width makes the last row zero. -/
theorem moveUp_grid {P b w r c : Nat} (hb : 0 < b) (hr : r < w) (hc : c < w)
    (hP : Fits P b (w*w)) :
    lane (moveUp P b w) b (gridIndex w r c) =
      if r+1 < w then lane P b (gridIndex w (r+1) c) else 0 := by
  rw [lane_moveUp _ _ _ _ hb, ite_eq_left (grid_lt hr hc)]
  have he : gridIndex w r c + w = gridIndex w (r+1) c := by unfold gridIndex; ring
  rw [he]
  split_ifs with h
  · rfl
  · apply lane_eq_zero_of_fits hP
    unfold gridIndex
    have : w ≤ r+1 := by omega
    nlinarith

#print axioms moveRight_grid
#print axioms moveLeft_grid
#print axioms moveDown_grid
#print axioms moveUp_grid
end AKLT.Gen.Packed
