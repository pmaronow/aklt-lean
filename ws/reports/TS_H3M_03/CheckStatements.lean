import AKLT.Blueprint.H3.NodesDomination
import AKLT.Blueprint.H3.NodesCertificate
import AKLT.Blueprint.H3.NodesPrefix
import AKLT.Blueprint.H3.NodesReflection

-- Inspection only: this file contains no theorem or proof declarations.
set_option pp.fullNames true

#check (AKLT.Blueprint.H3.ClosedTrailStepGeometryStatement : Prop)
#print AKLT.Blueprint.H3.ClosedTrailStepGeometryStatement
#check (AKLT.Blueprint.H3.SuffixWordComparisonStatement : Prop)
#print AKLT.Blueprint.H3.SuffixWordComparisonStatement
#check (AKLT.Blueprint.H3.StationaryWordExpansionStatement : Prop)
#print AKLT.Blueprint.H3.StationaryWordExpansionStatement
#check (AKLT.Blueprint.H3.StationaryFreeEdgeStatement : Prop)
#print AKLT.Blueprint.H3.StationaryFreeEdgeStatement
#check (AKLT.Blueprint.H3.LongTrailPrefixStatement : Prop)
#print AKLT.Blueprint.H3.LongTrailPrefixStatement
#check (AKLT.Blueprint.H3.LongRowRegroupingStatement : Prop)
#print AKLT.Blueprint.H3.LongRowRegroupingStatement
#check (AKLT.Blueprint.H3.ReflectionGeometryStatement : Prop)
#print AKLT.Blueprint.H3.ReflectionGeometryStatement
#check (AKLT.Blueprint.H3.ReflectionLivePairsStatement : Prop)
#print AKLT.Blueprint.H3.ReflectionLivePairsStatement

#synth Fintype (AKLT.Defs.DirectionWord 0)
#synth Fintype (AKLT.Defs.DirectionWord 2)
#eval Fintype.card (AKLT.Defs.DirectionWord 0)
#eval Fintype.card (AKLT.Defs.DirectionWord 2)
