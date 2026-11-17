import AKLT.Blueprint.Q.NodesSplits
import AKLT.Blueprint.Q.NodesQuantum

-- Declaration and instance inspection only; this file contains no proofs.
#print AKLT.Blueprint.Q.CentreDegreeCancellationStatement
#print AKLT.Blueprint.Q.IncidentProductDegreeStatement
#print AKLT.Blueprint.Q.StateCentreDegreeStatement
#print AKLT.Blueprint.Q.StarEdgeEnumerationStatement
#print AKLT.Blueprint.Q.StarCasimirChartStatement
#print AKLT.Blueprint.Q.StarProjectorTransportStatement
#print AKLT.Blueprint.Q.DeterminantModulusStatement
#print AKLT.Blueprint.Q.GroundProductWeightStatement
#print AKLT.Blueprint.Q.casimirCopies
#print AKLT.Challenge.Size
#check Submodule.starProjection_map_apply
#check LinearIsometry.map_starProjection
#check Submodule.eq_starProjection_of_mem_orthogonal
variable (L N : AKLT.Challenge.Size)
#synth Fintype (AKLT.Challenge.Site L N)
#synth Fintype (AKLT.Challenge.Bond L N)
