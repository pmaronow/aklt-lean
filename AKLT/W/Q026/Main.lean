module
public import AKLT.Blueprint.Q.NodesPolynomial
public import AKLT.Uniq.BondAlgebra

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.Q026

/-- The blueprint's nonassociate leaf follows from the checked bond-algebra result. -/
theorem main : AKLT.Blueprint.Q.SingletNonassociateStatement :=
  AKLT.Uniq.singletNonassociate

#print axioms main

end AKLT.W.Q026
