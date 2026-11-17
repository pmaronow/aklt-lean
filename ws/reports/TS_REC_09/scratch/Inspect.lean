import AKLT.Blueprint.Rec.NodesKernel

open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

#print AKLT.Blueprint.Rec.KernelLengthMajorantStatement
#print AKLT.Blueprint.Rec.MajorantFiniteStatement
#print AKLT.Blueprint.Rec.UnshiftedWitnessStatement
#print AKLT.Blueprint.Rec.ShiftPowerIncrementStatement
#print AKLT.Blueprint.Rec.TransportChoiceStatement
#print AKLT.Blueprint.Rec.WitnessPerturbationStatement
#print AKLT.Blueprint.Rec.ShiftedRowsRealStatement
#print AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement
#print AKLT.Defs.OpenTrailBound
#print AKLT.Blueprint.Top.ShiftedWitness
#print AKLT.Blueprint.Rec.RenewalRows
#check ENNReal.summable_toReal
#check ENNReal.tsum_toReal_eq
#check ENNReal.ofReal_tsum_of_nonneg
#check Summable.tsum_ofReal_ne_top
#check hasSum_coe_mul_geometric_of_norm_lt_one
#check hasSum_sq_mul_geometric_of_norm_lt_one
#eval (kernelWitness .B, kernelWitness .C, kernelRho)
#eval (alphaBound true, alphaBound false, betaBound true, betaBound false, betaPrimeBound true, betaPrimeBound false)
#eval (Fintype.card PairType, Fintype.card (DirectionWord 0), Fintype.card (DirectionWord 1))
