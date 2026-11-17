import AKLT.Blueprint.Q.NodesEnergy
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q
#print FrameWeightsPositiveStatement
#print PlaneConditioningStatement
#print TorusMarkovStatement
#print PlaneOneSiteEnergyStatement
#print TorusOneSiteEnergyStatement
#print PartialAssignmentStatement
#print PlaneAssignmentReindexStatement
#print PlaneProductReferenceStatement
set_option pp.explicit true in
#print PartialAssignmentStatement
#print axioms PartialAssignmentStatement
#print axioms PlaneAssignmentReindexStatement
#print axioms PlaneProductReferenceStatement
#eval Fintype.card IcoLetter
#eval (internalBonds (∅ : Finset Plane)).card
#eval (originalLegs ({(0, 0)} : Finset Plane)).card
#eval (internalBonds ({(0, 0), (1, 0)} : Finset Plane)).card
#eval (originalLegs ({(0, 0), (1, 0)} : Finset Plane)).card
#eval Fintype.card (PlaneConfiguration (∅ : Finset Plane))
#eval (torusNeighbours (L := ⟨3, Nat.le_refl 3⟩) (N := ⟨3, Nat.le_refl 3⟩) (0, 0)).card
