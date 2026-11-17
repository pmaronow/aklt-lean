import AKLT.Blueprint.Rec.NodesV2Handoff

-- Diagnostics only: inspect elaborated constants, without proving any leaf.
set_option autoImplicit false
set_option relaxedAutoImplicit false

#check @AKLT.Blueprint.Rec.PairSetup.mk
#check @AKLT.Blueprint.Rec.PairData.normalized
#check @AKLT.Defs.StoppedNetworkTrail
#check @AKLT.Defs.Network.ResponsePair
#check @AKLT.Defs.CoveredDepartureV2
#check @AKLT.Blueprint.Rec.CoveredDepartureV2
#check @AKLT.Defs.MemoryQuotient.Correct
#check @AKLT.Defs.finiteOperatorSum
#check @List.pairwise_mergeSort

#print AKLT.Blueprint.Rec.PairClosureStatementV2
#print AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2
#print AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2
#print AKLT.Blueprint.Rec.ShortKernelOrderingStatementV2
#print AKLT.Blueprint.Rec.LongKernelOrderingStatementV2
#print AKLT.Blueprint.Rec.StoppedQuotientSumStatementV2
