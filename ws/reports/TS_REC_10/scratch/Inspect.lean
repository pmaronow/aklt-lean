import AKLT.Blueprint.Rec.NodesRecursion

set_option pp.explicit false
set_option pp.proofs false
set_option pp.fullNames true

#print AKLT.Blueprint.Rec.EnvelopeBoundsStatement
#print AKLT.Blueprint.Rec.EnvelopeOrderStatement
#print AKLT.Blueprint.Rec.ProtectedDistanceFiniteStatement
#print AKLT.Blueprint.Rec.PairCanonicalGeometryStatement
#print AKLT.Blueprint.Rec.TraceExposureStatement
#print AKLT.Blueprint.Rec.PairEnvelopeShiftStatement
#print AKLT.Blueprint.Rec.TraceKernelLengthStatement
#print AKLT.Blueprint.Rec.ResidualTargetBoundStatement
#print AKLT.Blueprint.Rec.PairData
#print AKLT.Defs.Network.ResponsePair
#print AKLT.Defs.OpenTrailBound
#print AKLT.Blueprint.Top.H1Statement
#print AKLT.Blueprint.Rec.firstLength
#print AKLT.Defs.responseEnvelope

#check AKLT.Defs.PairType
#synth Fintype AKLT.Defs.PairType
#synth Fintype (AKLT.Defs.DirectionWord 0)
#check AKLT.Blueprint.Rec.protectedDistance
#check AKLT.Blueprint.Rec.kernelMajorant

#reduce Int.toNat (-3)
#reduce Int.toNat ((2 : Int) - (5 : Nat))
#reduce Finset.range (0 + 2)
