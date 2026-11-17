import AKLT.Blueprint.Win.NodesCut
import AKLT.Blueprint.Win.NodesTail

set_option pp.explicit true in
#print AKLT.Blueprint.Win.OverlapMinorizationStatement

set_option pp.explicit true in
#print AKLT.Blueprint.Win.BoundedTiltStatement

#print AKLT.Blueprint.Win.TailExponentialStatement
#print AKLT.Blueprint.Win.WindowRewriteStatement
#print AKLT.Defs.shellSpacing
#print AKLT.Blueprint.Top.ThreeFramesStatement

#synth Nonempty (AKLT.Defs.PlaneConfiguration ∅)
#synth Nonempty (AKLT.Defs.FrameBoundary ∅)

set_option pp.explicit true in
#print AKLT.Blueprint.Win.tailCost

set_option pp.explicit true in
#print AKLT.Blueprint.Win.TailExponentialStatement

#check Real.pow_div_factorial_le_exp
#check Real.rpow_def_of_pos
#check Real.sq_sqrt
