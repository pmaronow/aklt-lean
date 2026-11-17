import AKLT.Blueprint.Win.NodesTaper
import AKLT.Blueprint.Win.NodesRemoval

set_option pp.notation false in
#print AKLT.Blueprint.Win.nearCost

set_option pp.notation false in
#print AKLT.Blueprint.Win.tailCost

set_option pp.notation false in
#print AKLT.Blueprint.Win.NearSeriesStatement

#print AKLT.Blueprint.Win.SignedSideExclusionStatement
#print AKLT.Blueprint.Win.SquareIntersectionStatement
#print AKLT.Blueprint.Win.RawLayerCountStatement
#print AKLT.Blueprint.Win.RawWeightSumStatement
#print AKLT.Blueprint.Win.ThickDepthStatement
#print AKLT.Blueprint.Win.CutSeparationStatement
#print AKLT.Blueprint.Win.OriginalPositivityStatement

#check AKLT.Defs.FiniteSpinNetwork.Valid
#check AKLT.Defs.FiniteSpinNetwork.partition
#synth Fintype AKLT.Defs.IcoLetter
#synth Fintype AKLT.Defs.SpinLetter
#synth Fintype (↥(∅ : Finset AKLT.Defs.Plane) → AKLT.Defs.IcoLetter)

#eval max (0 : Nat) 16 - 2
#eval max (16 : Nat) 16 - 2
#eval max (17 : Nat) 16 - 2
#eval max (18 : Nat) 16 - 2
#eval Fintype.card (↥(∅ : Finset AKLT.Defs.Plane) → AKLT.Defs.IcoLetter)

set_option pp.explicit true in
#print AKLT.Blueprint.Win.nearCost

set_option pp.explicit true in
#print AKLT.Blueprint.Win.tailCost
