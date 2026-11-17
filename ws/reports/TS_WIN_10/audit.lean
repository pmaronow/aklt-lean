import AKLT.Blueprint.Win.NodesTail
import AKLT.Blueprint.Win.NodesCut

-- Inspection only: no theorem declarations or proofs.
open AKLT.Defs AKLT.Blueprint.Win
open scoped BigOperators

#print TailThresholdStatement
#print FrameWeightPositiveStatement
#print tailCost
#print tailConstant
#print shellSpacing
#print planeWeight
#print ProperPlaneColouring
#print PlaneConfiguration
#print FrameBoundary
#synth Fintype (PlaneConfiguration (∅ : Finset Plane))
#synth Nonempty (PlaneConfiguration (∅ : Finset Plane))
#synth Fintype (FrameBoundary (∅ : Finset Plane))
#synth Nonempty (FrameBoundary (∅ : Finset Plane))
#check Nat.le_ceil
#check Real.sq_sqrt
#check Real.sqrt_le_left
#check Real.log_neg
#check zpow_neg
#check Finset.prod_pos
#reduce geometryThreshold 64
