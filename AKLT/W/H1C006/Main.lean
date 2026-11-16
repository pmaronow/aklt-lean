import AKLT.W.H1C006.Supported
import AKLT.W.H1C006.Scaling
import AKLT.W.H1C006.RealBridge
import AKLT.W.H1C002.Main

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1C006

/-- Positivity of the indexed integer central sectors implies the original
pattern bound. The full tensor operator is allowed a kernel outside its U support. -/
theorem main :
    AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound := by
  intro π hπ r I hI D₀ hD₀ p q hp hq hpq hPositive m
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hc : (0 : ℚ) < (p : ℚ) / q := div_pos hpQ hqQ
  have hCentral := central_matrix_positive_of_indexed H1C002.main π hπ r I hI D₀ hD₀
    p q hp hq hpq hPositive
  have hPauli := positive_pauli_of_central π hπ r I hI ((p : ℚ) / q) hc hpq hCentral
  obtain ⟨ha, _, hs⟩ := reducedStructure π hπ r ((p : ℚ) / q)
  obtain ⟨K, hK, u, hu, hCurrent, hNext⟩ := commonReconstruction π hπ r m
  have hReduced := rational_ball_nonnegative _ _ ha hs I hI.1 hPauli u hu
  have hDifference := differenceEvaluation π r ((p : ℚ) / q) u
  have hCast : (((p : ℚ) / q : ℚ) : ℝ) = (p : ℝ) / q := by
    push_cast
    rfl
  rw [hCurrent, hNext]
  rw [hDifference, hCast] at hReduced
  nlinarith [mul_nonneg hK.le hReduced]

#print axioms moments
#print axioms threeFactorMean
#print axioms leaf
#print axioms reconstruction
#print axioms reducedStructure
#print axioms reducedStructureReal
#print axioms reduceReal
#print axioms inversionReal
#print axioms operatorStructure
#print axioms operatorStructureReal
#print axioms sector
#print axioms commonReconstruction
#print axioms eigenspace_span_weight
#print axioms centralSpace_eq_span
#print axioms positiveOn_span_of_form_posDef
#print axioms complexSectorMatrix_eq_inner
#print axioms central_positive_of_matrix
#print axioms swapConfiguration_involutive
#print axioms exchange_apply
#print axioms exchange_involutive
#print axioms exchange_symmetric
#print axioms exchange_commute_of_disjoint
#print axioms groupExchange_pair
#print axioms groupExchange_involutive
#print axioms groupExchange_commute
#print axioms localVector_swap
#print axioms groupVector_swap_self
#print axioms groupVector_swap_other
#print axioms sectorVector_exchange
#print axioms exchangeSpace_eigenvectors
#print axioms common_sign_eigenvector
#print axioms localCode_spec
#print axioms localVector_representative
#print axioms token_has_owner
#print axioms tokenOwner_mem
#print axioms tokenOwner_eq
#print axioms basisConfiguration_leader
#print axioms basisConfiguration_second
#print axioms groupVector_basisConfiguration
#print axioms sectorVector_basisConfiguration
#print axioms canonical_configuration
#print axioms not_localCanonical
#print axioms swapConfiguration_eq_of_equal
#print axioms canonical_swap_other
#print axioms canonical_swap_self
#print axioms exchangeEigenvectors_coord
#print axioms exchangeSign_ne_zero
#print axioms eq_zero_of_canonical_zero
#print axioms exchange_complete
#print axioms groupStatus
#print axioms supported_fixes
#print axioms groupExchange_single
#print axioms pairStructure_commute
#print axioms pairStructure_preserves
#print axioms nonzero_eigenvector_in_sector
#print axioms posSemidef_of_supported_sectors
#print axioms positive_pauli_of_central
#print axioms posDef_of_positive_real_scale
#print axioms positiveScale_of_thresholdScale
#print axioms central_matrix_positive_of_indexed
#print axioms invert_map_real
#print axioms pauli_map_real
#print axioms rational_ball_nonnegative
#print axioms main

end AKLT.W.H1C006
