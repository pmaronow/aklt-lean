module
public import AKLT.Blueprint.H1.AssemblyV2
public import AKLT.Blueprint.Mom.Assembly
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
public import AKLT.W.MOM018.Main
public import AKLT.W.MOM019.Main
public import AKLT.W.MOM020.Main
public import AKLT.W.MOM021.Main
public import AKLT.W.MOM022.Main
public import AKLT.W.MOM023.Main
public import AKLT.W.MOM024.Main
public import AKLT.W.MOM025.Main
public import AKLT.W.MOM026.Main
public import AKLT.W.MOM027.Main
public import AKLT.W.MOM028.Main
public import AKLT.W.MOM029.Main
public import AKLT.W.MOM030.Main
public import AKLT.W.H1M002.Main
public import AKLT.W.H1M003.Main
public import AKLT.W.H1M004.Main
public import AKLT.W.H1M012.Main
public import AKLT.W.H1M013.Main
public import AKLT.W.H1M014.Main
public import AKLT.W.H1M015.Main
public import AKLT.W.H1M016.Main
public import AKLT.W.H1M017.Main
public import AKLT.W.H1M020.Main
public import AKLT.W.H1M022.Main
public import AKLT.W.H1M023.Main
public import AKLT.W.H1M024.Main
public import AKLT.W.H1M025.Main
public import AKLT.W.H1M026.Main
public import AKLT.W.H1M027.Main
public import AKLT.W.H1M028.Main
public import AKLT.W.H1M030.Main
public import AKLT.W.H1M031.Main
public import AKLT.W.H1M032.Main
public import AKLT.W.H1M033.Main
public import AKLT.W.H1M034.Main
public import AKLT.W.H1M035.Main
public import AKLT.W.H1M036.Main
public import AKLT.W.H1M037.Main
public import AKLT.W.H1M038.Main
public import AKLT.W.H1M039.Main
public import AKLT.W.H1M040.Main
public import AKLT.W.H1M041.Main
public import AKLT.W.H1M042.Main
public import AKLT.W.H1M043.Main
public import AKLT.W.H1M044.Main
public import AKLT.W.H1M045.Main
public import AKLT.W.H1M046.Main
public import AKLT.W.H1M047.Main
public import AKLT.W.H1M048.Main
public import AKLT.W.H1M049.Main
public import AKLT.W.H1M050.Main
public import AKLT.W.H1M051.Main
public import AKLT.W.H1M052.Main
public import AKLT.W.H1M053.Main
public import AKLT.W.H1M054.Main
public import AKLT.W.H1M055.Main
public import AKLT.W.H1M056.Main
public import AKLT.W.H1M057.Main
public import AKLT.W.H1M058.Main
public import AKLT.W.H1M059.Main
public import AKLT.W.H1M060.Main
public import AKLT.W.H1M061.Main
public import AKLT.W.H1M062.Main
public import AKLT.W.H1M063.Main
public import AKLT.W.H1M064.Main
public import AKLT.W.H1M065.Main
public import AKLT.W.H1M066.Main
public import AKLT.W.H1M067.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

theorem moments : AKLT.Blueprint.Top.MomentsStatement :=
  AKLT.Blueprint.Mom.moments_of_leaves MOM001.main MOM002.main
    AKLT.Blueprint.Mom.icoAntipodal MOM003.main MOM004.main MOM005.main MOM006.main
    MOM007.main MOM008.main MOM009.main MOM010.main AKLT.Blueprint.Mom.productFactorization

theorem threeFactorMean : AKLT.Blueprint.Top.ThreeFactorMeanStatement :=
  AKLT.Blueprint.Mom.threeFactorMean_of_leaves MOM018.main MOM019.main MOM020.main
    MOM021.main MOM022.main MOM023.main MOM024.main MOM025.main
    AKLT.Blueprint.Mom.meanPathUnit MOM026.main MOM027.main MOM028.main MOM029.main MOM030.main

theorem leaf : AKLT.Blueprint.Top.LeafStatement :=
  leaf_of_nodesV2 moments threeFactorMean H1M002.main H1M003.main H1M004.main

theorem reconstruction : SimultaneousLeafReconstructionStatement :=
  simultaneousLeafReconstruction_of_nodes H1M025.main H1M026.main H1M027.main

theorem reducedStructure : ReducedStructureStatement :=
  reducedStructure_of_nodes moments H1M023.main H1M024.main H1M013.main
    H1M014.main H1M015.main H1M031.main

theorem reducedStructureReal : ReducedStructureStatementV2 :=
  reducedStructure_of_nodesV2
    (rationalPartitionsStructure_of_nodesV2 moments H1M023.main H1M024.main
      H1M013.main H1M014.main H1M015.main)
    H1M061.main H1M062.main H1M063.main

theorem reduceReal : AKLT.Blueprint.Top.ReduceStatementV2 :=
  reduce_of_nodesV2 moments leaf H1M023.main H1M012.main reconstruction
    reducedStructureReal H1M028.main H1M065.main H1M030.main H1M064.main

theorem inversionReal : AKLT.Blueprint.Top.InversionStatementV2 :=
  inversion_of_nodesV2 H1M016.main H1M017.main H1M056.main H1M057.main
    H1M058.main H1M059.main H1M060.main H1M022.main

theorem operatorStructure : AKLT.Blueprint.Top.OperatorStructureStatement :=
  operatorStructure_of_nodes moments H1M023.main reducedStructure H1M020.main
    H1M044.main H1M041.main H1M042.main H1M043.main H1M045.main H1M046.main
    H1M047.main H1M048.main H1M049.main H1M050.main
    (retainedPairExpansion_of_nodes H1M051.main H1M052.main)
    H1M053.main H1M054.main H1M055.main

theorem operatorStructureReal : AKLT.Blueprint.Top.OperatorStructureStatementV2 :=
  operatorStructure_of_legacyV2 operatorStructure H1M066.main H1M067.main

theorem sector : AKLT.Blueprint.Top.SectorStatement :=
  sector_of_nodesV2 H1M032.main H1M033.main H1M034.main H1M035.main H1M036.main
    H1M037.main H1M038.main H1M039.main H1M040.main

/-- The old reconstruction residual is now unconditional. -/
theorem commonReconstruction (π : PatternData) (hπ : π.Covered) (r : Representation)
    (m : Fin 20 → UnitVector) :
    ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3,
      (∀ j ∈ reductionVectors π r, normSq (u j) ≤ 1) ∧
      patternCurrent π m = K * evaluateReduced (reducedPolynomial π r false) u ∧
      patternNext π m = K * evaluateReduced (reducedPolynomial π r true) u := by
  have hExact (next : Bool) (u : Fin 20 → Vec3) :=
    H1M012.main (momentInputs moments).1 _ _ (reducedStatuses π r next) _
      (H1M023.main π hπ r next) u
  obtain ⟨K, hK, u, hu, hc, hn⟩ :=
    reconstruction (momentInputs moments).2.2 π hπ r hExact m (leaf π hπ m)
  exact ⟨K, hK, u, fun j _ => hu j, hc, hn⟩

end AKLT.W.H1C006
