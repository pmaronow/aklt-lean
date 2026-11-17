import AKLT.Blueprint.Rec.NodesKernel
open AKLT.Defs AKLT.Blueprint.Rec
#print UDepartureInjectiveStatement
#print DiamondTwelveStatement
#print TerminalExceptionCountStatement
#print KernelOrderingStatement
#print KernelPositivityStatement
#print ShiftGeometryStatement
#print KernelSupportStatement
#print KernelRegroupStatement
#eval ((square (0, 0) 2).filter fun z => 0 < latticeDist z (0, 0) ∧ latticeDist z (0, 0) ≤ 2).card
#eval ((square (-11, 7) 2).filter fun z => 0 < latticeDist z (-11, 7) ∧ latticeDist z (-11, 7) ≤ 2).card
