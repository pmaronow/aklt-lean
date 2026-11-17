module
public import AKLT.Blueprint.Mom.Assembly
public import AKLT.Blueprint.H1.Assembly
public import AKLT.W.MOM001.Main
public import AKLT.W.MOM002.Main
public import AKLT.W.MOM003.Main
public import AKLT.W.MOM004.Main
public import AKLT.W.MOM005.Main
public import AKLT.W.MOM006.Main
public import AKLT.W.MOM007.Main
public import AKLT.W.MOM008.Main
public import AKLT.W.MOM009.Main
public import AKLT.W.MOM010.Main
public import AKLT.W.H1M013.Main
public import AKLT.W.H1M014.Main
public import AKLT.W.H1M015.Main
public import AKLT.W.H1M020.Main
public import AKLT.W.H1M023.Main
public import AKLT.W.H1M024.Main
public import AKLT.W.H1M031.Main
public import AKLT.W.H1M042.Main
public import AKLT.W.H1M043.Main
public import AKLT.W.H1M044.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C002

private theorem moments : AKLT.Blueprint.Top.MomentsStatement :=
  AKLT.Blueprint.Mom.moments_of_leaves
    AKLT.W.MOM001.main AKLT.W.MOM002.main AKLT.Blueprint.Mom.icoAntipodal
    AKLT.W.MOM003.main AKLT.W.MOM004.main AKLT.W.MOM005.main AKLT.W.MOM006.main
    AKLT.W.MOM007.main AKLT.W.MOM008.main AKLT.W.MOM009.main AKLT.W.MOM010.main
    AKLT.Blueprint.Mom.productFactorization

private theorem reducedStructure : ReducedStructureStatement :=
  reducedStructure_of_nodes moments AKLT.W.H1M023.main AKLT.W.H1M024.main
    AKLT.W.H1M013.main AKLT.W.H1M014.main AKLT.W.H1M015.main AKLT.W.H1M031.main

/-- Orthogonal reflection removes all odd imaginary Pauli contributions. -/
theorem invertedDifference_real (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (c : ℚ) :
    ∀ σ τ, (pauliOperator (reductionVectors π r)
      (invertPolynomial I (reducedDifference π r c)) σ τ).im = 0 := by
  obtain ⟨ha, hi, hs⟩ := reducedStructure π hπ r c
  obtain ⟨hia, his, _⟩ := AKLT.W.H1M020.main (reductionVectors π r) I _ ha hs
  exact AKLT.W.H1M043.main _ _
    (AKLT.W.H1M042.main _ _ hia his (AKLT.W.H1M044.main _ hi I))

end AKLT.W.H1C002

#print axioms AKLT.W.H1C002.invertedDifference_real
