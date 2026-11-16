import AKLT.Gen.Packed.All
import AKLT.Gen.Packed.Example

#check @AKLT.Gen.Packed.lane
#check @AKLT.Gen.Packed.packFn
#check @AKLT.Gen.Packed.pack
#check @AKLT.Gen.Packed.Fits
#check @AKLT.Gen.Packed.lane_zero
#print axioms AKLT.Gen.Packed.lane_zero
#check @AKLT.Gen.Packed.lane_succ
#print axioms AKLT.Gen.Packed.lane_succ
#check @AKLT.Gen.Packed.lane_lt
#print axioms AKLT.Gen.Packed.lane_lt
#check @AKLT.Gen.Packed.lane_packFn
#print axioms AKLT.Gen.Packed.lane_packFn
#check @AKLT.Gen.Packed.packFn_lt
#print axioms AKLT.Gen.Packed.packFn_lt
#check @AKLT.Gen.Packed.packFn_lanes
#print axioms AKLT.Gen.Packed.packFn_lanes
#check @AKLT.Gen.Packed.lane_eq_zero_of_fits
#print axioms AKLT.Gen.Packed.lane_eq_zero_of_fits
#check @AKLT.Gen.Packed.lanes_ext
#print axioms AKLT.Gen.Packed.lanes_ext
#check @AKLT.Gen.Packed.packFn_add
#print axioms AKLT.Gen.Packed.packFn_add
#check @AKLT.Gen.Packed.packFn_mul
#print axioms AKLT.Gen.Packed.packFn_mul
#check @AKLT.Gen.Packed.lane_add
#print axioms AKLT.Gen.Packed.lane_add
#check @AKLT.Gen.Packed.lane_mul
#print axioms AKLT.Gen.Packed.lane_mul
#check @AKLT.Gen.Packed.packFn_congr
#print axioms AKLT.Gen.Packed.packFn_congr
#check @AKLT.Gen.Packed.pack_eq_packFn
#print axioms AKLT.Gen.Packed.pack_eq_packFn
#check @AKLT.Gen.Packed.lane_pack
#print axioms AKLT.Gen.Packed.lane_pack
#check @AKLT.Gen.Packed.repeatLane
#check @AKLT.Gen.Packed.repeatLane_eq
#print axioms AKLT.Gen.Packed.repeatLane_eq
#check @AKLT.Gen.Packed.packFn_eq_sum
#print axioms AKLT.Gen.Packed.packFn_eq_sum
#check @AKLT.Gen.Packed.pack_append
#print axioms AKLT.Gen.Packed.pack_append
#check @AKLT.Gen.Packed.testBit_lane
#print axioms AKLT.Gen.Packed.testBit_lane
#check @AKLT.Gen.Packed.lane_land
#print axioms AKLT.Gen.Packed.lane_land
#check @AKLT.Gen.Packed.lane_shiftRight
#print axioms AKLT.Gen.Packed.lane_shiftRight
#check @AKLT.Gen.Packed.lane_shiftLeft
#print axioms AKLT.Gen.Packed.lane_shiftLeft
#check @AKLT.Gen.Packed.laneMask
#check @AKLT.Gen.Packed.lane_laneMask
#print axioms AKLT.Gen.Packed.lane_laneMask
#check @AKLT.Gen.Packed.lane_mask
#print axioms AKLT.Gen.Packed.lane_mask
#check @AKLT.Gen.Packed.gridIndex
#check @AKLT.Gen.Packed.rightMask
#check @AKLT.Gen.Packed.leftMask
#check @AKLT.Gen.Packed.rowMask
#check @AKLT.Gen.Packed.columnMask
#check @AKLT.Gen.Packed.moveRight
#check @AKLT.Gen.Packed.moveLeft
#check @AKLT.Gen.Packed.moveDown
#check @AKLT.Gen.Packed.moveUp
#check @AKLT.Gen.Packed.lane_moveRight
#print axioms AKLT.Gen.Packed.lane_moveRight
#check @AKLT.Gen.Packed.lane_moveLeft
#print axioms AKLT.Gen.Packed.lane_moveLeft
#check @AKLT.Gen.Packed.lane_truncate
#print axioms AKLT.Gen.Packed.lane_truncate
#check @AKLT.Gen.Packed.lane_moveDown
#print axioms AKLT.Gen.Packed.lane_moveDown
#check @AKLT.Gen.Packed.lane_moveUp
#print axioms AKLT.Gen.Packed.lane_moveUp
#check @AKLT.Gen.Packed.lane_rowMask
#print axioms AKLT.Gen.Packed.lane_rowMask
#check @AKLT.Gen.Packed.lane_columnMask
#print axioms AKLT.Gen.Packed.lane_columnMask
#check @AKLT.Gen.Packed.moveRight_grid
#print axioms AKLT.Gen.Packed.moveRight_grid
#check @AKLT.Gen.Packed.moveLeft_grid
#print axioms AKLT.Gen.Packed.moveLeft_grid
#check @AKLT.Gen.Packed.moveDown_grid
#print axioms AKLT.Gen.Packed.moveDown_grid
#check @AKLT.Gen.Packed.moveUp_grid
#print axioms AKLT.Gen.Packed.moveUp_grid
#check @AKLT.Gen.Packed.guardMask
#check @AKLT.Gen.Packed.lane_guardMask
#print axioms AKLT.Gen.Packed.lane_guardMask
#check @AKLT.Gen.Packed.guardMask_fits
#print axioms AKLT.Gen.Packed.guardMask_fits
#check @AKLT.Gen.Packed.lane_guard_sub
#print axioms AKLT.Gen.Packed.lane_guard_sub
#check @AKLT.Gen.Packed.guard_compare
#print axioms AKLT.Gen.Packed.guard_compare
#check @AKLT.Gen.Packed.guard_compare_all
#print axioms AKLT.Gen.Packed.guard_compare_all
#check @AKLT.Gen.Packed.guardCheck
#check @AKLT.Gen.Packed.guardCheck_iff
#print axioms AKLT.Gen.Packed.guardCheck_iff
#check @AKLT.Gen.Packed.capMask
#check @AKLT.Gen.Packed.capCheck
#check @AKLT.Gen.Packed.capCheck_sound
#print axioms AKLT.Gen.Packed.capCheck_sound
#check @AKLT.Gen.Packed.linearRHS
#check @AKLT.Gen.Packed.linearRHS_pack
#print axioms AKLT.Gen.Packed.linearRHS_pack
#check @AKLT.Gen.Packed.rowCheck
#check @AKLT.Gen.Packed.rowCheck_sound
#print axioms AKLT.Gen.Packed.rowCheck_sound
#check @AKLT.Gen.Packed.rowsCheck
#check @AKLT.Gen.Packed.rowsCheck_sound
#print axioms AKLT.Gen.Packed.rowsCheck_sound

#check @AKLT.Gen.Packed.Example.checked
#check @AKLT.Gen.Packed.Example.all_lanes
#print axioms AKLT.Gen.Packed.Example.checked
#print axioms AKLT.Gen.Packed.Example.all_lanes
