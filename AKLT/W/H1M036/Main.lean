module
public import AKLT.W.H1M036.Proof

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder

namespace AKLT.W.H1M036

theorem main : AKLT.Blueprint.H1.SpinCommutatorStatement := by
  intro J ψ
  exact ⟨
    by
      simpa [LinearMap.sub_apply] using
        congrArg (fun T : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) => T ψ) (endZP J),
    by
      simpa [LinearMap.sub_apply] using
        congrArg (fun T : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) => T ψ) (endZM J),
    by
      simpa [LinearMap.sub_apply] using
        congrArg (fun T : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)) => T ψ) (endPM J)⟩

#print axioms endZP
#print axioms endZM
#print axioms endPM
#print axioms main

end AKLT.W.H1M036
