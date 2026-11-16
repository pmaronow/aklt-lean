import AKLT.Blueprint.Q.NodesPolynomial
import AKLT.Uniq.BondAlgebra

noncomputable section

namespace AKLT.W.Q026

/-- The blueprint's nonassociate leaf follows from the checked bond-algebra result. -/
theorem main : AKLT.Blueprint.Q.SingletNonassociateStatement :=
  AKLT.Uniq.singletNonassociate

#print axioms main

end AKLT.W.Q026
