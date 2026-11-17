import AKLT.Blueprint.Win.NodesTopology
import AKLT.Blueprint.Win.NodesTaper

-- Read-only elaboration inspection. This file contains no proofs.
set_option pp.explicit true
set_option pp.universes true

#print AKLT.Blueprint.Win.CrossFactsStatement
#print AKLT.Blueprint.Win.CrossOverlapStatement
#print AKLT.Blueprint.Win.CrossUnionStatement
#print AKLT.Blueprint.Win.NeighbourDecayStatement
#print AKLT.Blueprint.Win.CrossWeightSumStatement
#print AKLT.Blueprint.Win.ConnectedEnumerationStatement
#print AKLT.Blueprint.Win.CutScalesStatement
#print AKLT.Blueprint.Win.CoreConnectedStatement
#print AKLT.Blueprint.Win.CutSetup
#print AKLT.Blueprint.Win.ShellSetup
#print AKLT.Blueprint.Win.RemovalEnumeration
#print AKLT.Blueprint.Win.ConnectedIn
#print AKLT.Blueprint.Win.JoinedIn
#print AKLT.Defs.decay
#print AKLT.Defs.setDistance
#eval AKLT.Defs.geometryThreshold 64

set_option pp.all true in
#check (fun i : ℤ => (i - 1 : ℝ))
