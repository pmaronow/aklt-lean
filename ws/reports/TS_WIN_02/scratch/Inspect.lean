import AKLT.Blueprint.Win.NodesShell
import AKLT.Blueprint.Win.NodesTopology

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs false

#print AKLT.Blueprint.Win.PredecessorShellStatement
#print AKLT.Blueprint.Win.SeedSeparationStatement
#print AKLT.Blueprint.Win.FiniteDepthStatement
#print AKLT.Blueprint.Win.BoundaryMembershipStatement
#print AKLT.Blueprint.Win.ChainBoxStatement
#print AKLT.Blueprint.Win.DiagonalEliminationStatement
#print AKLT.Blueprint.Win.ColumnFluxStatement
#print AKLT.Blueprint.Win.TailSupportStatement

#print AKLT.Defs.setDistance
#print AKLT.Defs.boundaryDepth
#print AKLT.Defs.farVolume
#print AKLT.Defs.shellRadius
#print AKLT.Blueprint.Win.ChainEven
#print AKLT.Blueprint.Win.ChainInBox
#print AKLT.Blueprint.Win.tailCoefficient
#print AKLT.Blueprint.Win.triangleSpan

#check ENat.iInf_natCast_ne_top
#check ENat.exists_eq_iInf
#check ENat.iInf_eq_natCast_iff
#check ENat.toNat_top
#check Sym2.mem_iff
#check Sym2.toFinset
#check Finsupp.mem_support_iff
#check Finsupp.single_apply
#synth CharP (ZMod 2) 2

#eval AKLT.Defs.supDist (0, 0) (1, -1)
#eval AKLT.Defs.latticeDist (0, 0) (1, -1)
