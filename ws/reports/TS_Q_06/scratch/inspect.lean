import AKLT.Blueprint.Q.NodesQuantum
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q
#print IncidentEvaluationStatement
#print GroundFibreFactorizationStatement
#print GroundTransformStatement
#print FibreIntertwiningStatement
#print FibreProjectionStatement
#print WeightedPolarizationStatement
#print GroundQuotientVarianceStatement
#print BetaNonzeroStatement
#print physicalEval
#print monomialDegree
#check @weightedNorm
#check @weightedInner
#check @conditionalExpectation
#check @inFibreSpan
#check @inner_smul_left
#check @inner_smul_right
#check @Complex.normSq_eq_conj_mul_self
section
variable (L N : Size)
#synth Fintype (Site L N)
#synth DecidableEq (Site L N)
#synth Fintype (TorusConfiguration L N)
#synth Fintype IcoLetter
end
