import AKLT.Blueprint.Win.NodesRemoval

/- Declaration inspection only: no proofs or new axioms. -/
#print AKLT.Blueprint.Win.PartLawBridgeStatement
#print AKLT.Blueprint.Win.EnumerationStepsStatement
#print AKLT.Blueprint.Win.SurvivorGeometryStatement
#print AKLT.Blueprint.Win.RemovalIntegralStatement
#print AKLT.Blueprint.Win.NeighbourFibresStatement
#print AKLT.Blueprint.Win.PairMeanAveragingStatement
#print AKLT.Blueprint.Win.QuarticMeanBoundStatement
#print AKLT.Blueprint.Win.PolynomialLowerStatement
#print AKLT.Blueprint.Win.NeighbourControl
#print AKLT.Blueprint.Win.partWeight
#print AKLT.Defs.PlaneConfiguration
#print AKLT.Defs.Probability
#check AKLT.Defs.Probability
#check AKLT.Defs.expectation
#check AKLT.Defs.normalize
#check AKLT.Defs.eventMass
#check AKLT.Blueprint.Win.fibreMean
#check AKLT.Blueprint.Win.fibreSpinMean
#check AKLT.Blueprint.Win.partLaw
#check AKLT.Defs.boundaryDepth

/- Print explicitly elaborated numeric types and finite configuration types. -/
set_option pp.explicit true in
#print AKLT.Blueprint.Win.removalPolynomial
set_option pp.explicit true in
#print AKLT.Blueprint.Win.partLaw
set_option pp.explicit true in
#print AKLT.Blueprint.Win.removedPrefix
