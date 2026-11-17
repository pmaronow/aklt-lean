import AKLT.Blueprint.Gap.NodesFinite

/- Declaration inspection only: no proof terms or theorem implementations. -/
set_option pp.universes true
set_option pp.funBinderTypes true

#print AKLT.Blueprint.Gap.DensityComparisonStatement
#print AKLT.Blueprint.Gap.ConditionalBlockComparisonStatement
#print AKLT.Blueprint.Gap.MultiplicityEstimateStatement
#print AKLT.Blueprint.Gap.HammingPathStatement
#print AKLT.Blueprint.Gap.LipschitzCouplingStatement
#print AKLT.Blueprint.Gap.LipschitzEigenvalueStatement
#print AKLT.Blueprint.Gap.ReversibleEigenvalueGapStatement
#print AKLT.Blueprint.Gap.BlockAverageFormStatement
#print AKLT.Blueprint.Gap.lipschitz
#print AKLT.Blueprint.Gap.Reversible
#print AKLT.Blueprint.Gap.blockLaw
#print AKLT.Blueprint.Gap.blockAverage
#print AKLT.Blueprint.Gap.kernelForm

#check @Fintype.card_pos
#check @Set.Finite.bddAbove
#check @le_csSup
#check @csSup_le
#check @Complex.normSq_nonneg
