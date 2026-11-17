import AKLT.Blueprint.H1.NodesPauli

set_option autoImplicit false
set_option relaxedAutoImplicit false

open AKLT.Defs AKLT.Blueprint.H1

#print OriginalDegreeStatement
#print OriginalFactorStructureStatement
#print OriginalRawEvaluationStatement
#print MomentContractionStatement
#print MomentCovarianceTransferStatement
#print ContractionAffineStatement
#print ContractionSupportStatement
#print BlochAlgebraStatement
#print MonomialMoments
#print ProductMomentCovariance
#print InternalAdmissible
#print contractSpins
#check Finsupp.comapDomain_apply

variable (V : Finset Plane)
#synth Fintype (V → SpinLetter)
#synth DecidableEq (Fin 20 × Fin 3)

#eval rationalMoment ![0, 0, 0]
#eval rationalStatusMoment .D ![0, 0, 0]
#eval rationalMoment ![2, 0, 0]
#eval rationalStatusMoment .D ![2, 0, 0]
#eval rationalMoment ![4, 0, 0]
#eval rationalStatusMoment .D ![4, 0, 0]
#eval rationalMoment ![2, 2, 0]
#eval rationalStatusMoment .D ![2, 2, 0]
#eval rationalMoment ![1, 1, 1]
