import AKLT.W.REC095.Main
import AKLT.W.REC095.Positivity

#check AKLT.W.REC095.departureCoefficient

#check AKLT.W.REC095.departureCoefficient_nonneg
#print axioms AKLT.W.REC095.departureCoefficient_nonneg

#check AKLT.W.REC095.present_neighbour
#print axioms AKLT.W.REC095.present_neighbour

#check AKLT.W.REC095.revisit_status_ne_U
#print axioms AKLT.W.REC095.revisit_status_ne_U

#check AKLT.W.REC095.traceDynamics
#print axioms AKLT.W.REC095.traceDynamics

#check AKLT.W.REC095.icoVector_normSq
#print axioms AKLT.W.REC095.icoVector_normSq

#check AKLT.W.REC095.normSq_nonneg
#print axioms AKLT.W.REC095.normSq_nonneg

#check AKLT.W.REC095.normSq_zero
#print axioms AKLT.W.REC095.normSq_zero

#check AKLT.W.REC095.dot_ge_neg_one
#print axioms AKLT.W.REC095.dot_ge_neg_one

#check AKLT.W.REC095.spinVector_normSq_le
#print axioms AKLT.W.REC095.spinVector_normSq_le

#check AKLT.W.REC095.spinWeight_nonneg
#print axioms AKLT.W.REC095.spinWeight_nonneg

#check AKLT.W.REC095.spins_normSq_le
#print axioms AKLT.W.REC095.spins_normSq_le

#check AKLT.W.REC095.partition_nonneg
#print axioms AKLT.W.REC095.partition_nonneg

#check AKLT.W.REC095.Residual_CoveredRatio

#check AKLT.W.REC095.traceCoefficient_product
#print axioms AKLT.W.REC095.traceCoefficient_product

#check AKLT.W.REC095.pointwise_of_coveredRatio
#print axioms AKLT.W.REC095.pointwise_of_coveredRatio

#check AKLT.W.REC095.coveredRatio_of_localMixture
#print axioms AKLT.W.REC095.coveredRatio_of_localMixture

#check AKLT.W.REC095.Residual_OnePointPointwise

#check AKLT.W.REC095.Residual_StoppedTrailGeometry

#check AKLT.W.REC095.stoppedTrailGeometry
#print axioms AKLT.W.REC095.stoppedTrailGeometry

#check AKLT.W.REC095.main_of_residuals
#print axioms AKLT.W.REC095.main_of_residuals

#check AKLT.W.REC095.main_of_pointwise
#print axioms AKLT.W.REC095.main_of_pointwise

#check AKLT.W.REC095.main_of_coveredRatio
#print axioms AKLT.W.REC095.main_of_coveredRatio

#check AKLT.W.REC095.main
#print axioms AKLT.W.REC095.main

#check AKLT.W.REC095.main_of_localMixture
#print axioms AKLT.W.REC095.main_of_localMixture

example : AKLT.W.REC095.Residual_CoveredRatio →
    AKLT.Blueprint.Rec.OnePointSumStatementV2 := AKLT.W.REC095.main_of_coveredRatio

example : AKLT.Blueprint.Rec.LocalMixtureStatementV2 →
    AKLT.Blueprint.Rec.OnePointSumStatementV2 := AKLT.W.REC095.main_of_localMixture

example : AKLT.Blueprint.Rec.OnePointSumStatementV2 := AKLT.W.REC095.main
