import AKLT.Blueprint.H3.NodesV2Stationary
import AKLT.Blueprint.H3.NodesV2Quotient

-- Declaration inspection only: no new proofs, axioms, or admitted goals.
set_option pp.proofs false
set_option pp.universes true

#print AKLT.Blueprint.H3.StationaryCoefficientOffCentreStatementV2
#print AKLT.Blueprint.H3.StationaryCentreZeroOperatorStatementV2
#print AKLT.Blueprint.H3.StationaryContinuationBridgeStatementV2
#print AKLT.Blueprint.H3.StationaryCertificateBridgeStatementV2
#print AKLT.Blueprint.H3.StoppedQuotientIntertwiningStatementV2

#print AKLT.Defs.MemoryQuotient
#print AKLT.Defs.MemoryQuotient.Correct
#print AKLT.Defs.stationaryCoefficient
#print AKLT.Defs.stationaryCoefficientV2
#print AKLT.Defs.stationaryApply
#print AKLT.Defs.stationaryApplyV2
#print AKLT.Defs.stationaryReward
#print AKLT.Defs.stationaryContinuationSum
#print AKLT.Defs.stationaryContinuationSumV2
#print AKLT.Defs.StationaryData.Passes
#print AKLT.Defs.StationaryData.PassesV2
#print AKLT.Blueprint.H3.rawStoppedBackwardV2
#print AKLT.Blueprint.H3.quotientStoppedBackwardV2

#check Function.iterate_zero_apply
#check Function.iterate_succ_apply'

-- Closed coordinate/scale checks, without theorem declarations.
#reduce AKLT.Defs.kernelTarget AKLT.Defs.PairType.B
#reduce AKLT.Defs.kernelTarget AKLT.Defs.PairType.C
#reduce AKLT.Defs.kernelCentre
#reduce AKLT.Defs.certificateValueScale
#reduce AKLT.Defs.certificateCoefficientScale
