import AKLT.W.Q030.Blocks

noncomputable section
open AKLT.Blueprint.Q

namespace AKLT.W.Q030

theorem eigen_coordinates_iff (v : PairHilbert) :
    v ∈ Module.End.eigenspace pairCasimir (20 : ℂ) ↔
      blockCasimir (coordinates v) = (20 : ℂ) • coordinates v := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    rw [← coordCasimir_eq, ← coordinates_casimir, h, map_smul]
  · intro h
    apply coordinates.injective
    rw [map_smul, coordinates_casimir, coordCasimir_eq]
    exact h

/-- The nine independent total-weight coefficients of a top eigenvector. -/
def eigenspaceParameters :
    Module.End.eigenspace pairCasimir (20 : ℂ) →ₗ[ℂ] (Fin 9 → ℂ) :=
  parameters.comp (coordinates.toLinearMap.comp (Submodule.subtype _))

theorem eigenspaceParameters_injective : Function.Injective eigenspaceParameters := by
  intro v w h
  apply Subtype.ext
  apply coordinates.injective
  have hv := reconstruct_eigenvector (coordinates (v : PairHilbert))
    ((eigen_coordinates_iff _).mp v.property)
  have hw := reconstruct_eigenvector (coordinates (w : PairHilbert))
    ((eigen_coordinates_iff _).mp w.property)
  change parameters (coordinates (v : PairHilbert)) =
    parameters (coordinates (w : PairHilbert)) at h
  calc
    coordinates (v : PairHilbert) =
        topCoordinates (parameters (coordinates (v : PairHilbert))) := hv.symm
    _ = topCoordinates (parameters (coordinates (w : PairHilbert))) :=
      congrArg topCoordinates h
    _ = coordinates (w : PairHilbert) := hw

theorem eigenspaceParameters_surjective : Function.Surjective eigenspaceParameters := by
  intro c
  refine ⟨⟨coordinates.symm (topCoordinates c), ?_⟩, ?_⟩
  · apply (eigen_coordinates_iff _).mpr
    simpa only [LinearEquiv.apply_symm_apply] using blockCasimir_topCoordinates c
  · change parameters (coordinates (coordinates.symm (topCoordinates c))) = c
    rw [LinearEquiv.apply_symm_apply, parameters_topCoordinates]

/-- An explicit parameterization of the eigenvalue-twenty space by nine scalars. -/
def eigenspaceEquiv :
    Module.End.eigenspace pairCasimir (20 : ℂ) ≃ₗ[ℂ] (Fin 9 → ℂ) :=
  LinearEquiv.ofBijective eigenspaceParameters
    ⟨eigenspaceParameters_injective, eigenspaceParameters_surjective⟩

theorem main : AKLT.Blueprint.Q.PairTopDimensionStatement := by
  change Module.finrank ℂ (Module.End.eigenspace pairCasimir (20 : ℂ)) = 9
  calc
    _ = Module.finrank ℂ (Fin 9 → ℂ) := eigenspaceEquiv.finrank_eq
    _ = 9 := by simp

end AKLT.W.Q030
