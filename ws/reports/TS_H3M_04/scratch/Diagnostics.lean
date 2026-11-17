import AKLT.Blueprint.H3.NodesReflection
import AKLT.Blueprint.H3.NodesKernel

-- Declaration and library-signature inspection only: no proofs are written here.
set_option pp.explicit true in
#check AKLT.Blueprint.H3.ReflectionPairLabelsStatement
set_option pp.explicit true in
#check AKLT.Blueprint.H3.FirstDirectionPartitionStatement
set_option pp.explicit true in
#check AKLT.Blueprint.H3.LengthShiftSupportStatement
set_option pp.explicit true in
#check AKLT.Blueprint.H3.LengthRewardPartitionStatement
set_option pp.explicit true in
#check AKLT.Blueprint.H3.KernelSeriesRegroupingStatement
set_option pp.explicit true in
#check AKLT.Blueprint.H3.CutoffSeriesLiftStatement

#synth Fintype (AKLT.Defs.DirectionWord 0)
#synth Fintype (AKLT.Defs.DirectionWord 1)
#synth Fintype AKLT.Defs.PairType
#print AKLT.Blueprint.H3.KernelSeriesRegroupingStatement
#print AKLT.Blueprint.H3.CutoffSeriesLiftStatement
#check AKLT.Blueprint.H3.kernelLengthCoefficient_nonneg
#check AKLT.Blueprint.H3.kernelWitness_pos
#check ENNReal.tsum_comm
#check ENNReal.tsum_mul_right
#check ENNReal.tsum_eq_iSup_nat
