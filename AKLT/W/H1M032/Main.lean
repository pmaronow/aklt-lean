module
public import AKLT.W.H1M032.Sector

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M032

theorem main : AKLT.Blueprint.H1.SectorSpinStableStatement := by
  intro π r ε
  refine ⟨?_, ?_, ?_⟩
  · intro ψ hψ
    simpa only [totalSpinZ, map_smul, LinearMap.smul_apply] using
      (exchangeSpace π r ε).smul_mem (1 / 2 : ℂ)
        (exchangeSpace_matrix_stable π r ε (pauli 3) ψ hψ)
  · intro ψ hψ
    simpa only [totalSpinPlus, map_smul, LinearMap.smul_apply] using
      (exchangeSpace π r ε).smul_mem (1 / 2 : ℂ)
        (exchangeSpace_matrix_stable π r ε (pauli 1 + Complex.I • pauli 2) ψ hψ)
  · intro ψ hψ
    simpa only [totalSpinMinus, map_smul, LinearMap.smul_apply] using
      (exchangeSpace π r ε).smul_mem (1 / 2 : ℂ)
        (exchangeSpace_matrix_stable π r ε (pauli 1 - Complex.I • pauli 2) ψ hψ)

end AKLT.W.H1M032

#print axioms AKLT.W.H1M032.main
