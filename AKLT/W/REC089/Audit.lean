import AKLT.W.REC089.Main

/-! Exact target-type check and declaration/axiom inventory. -/

#check (AKLT.W.REC089.main : AKLT.Blueprint.Rec.LocalMixtureStatementV2)

example : AKLT.Blueprint.Rec.LocalMixtureStatementV2 := AKLT.W.REC089.main

-- ActualDisintegration.lean: theorem
#check AKLT.W.REC089.actual_fibre_reduced
#print axioms AKLT.W.REC089.actual_fibre_reduced

-- ActualDisintegration.lean: theorem
#check AKLT.W.REC089.actual_fibre_factorization
#print axioms AKLT.W.REC089.actual_fibre_factorization

-- ActualFactorization.lean: def
#check AKLT.W.REC089.cornerFields

-- ActualFactorization.lean: def
#check AKLT.W.REC089.tipFields

-- ActualFactorization.lean: theorem
#check AKLT.W.REC089.prod_activeTips
#print axioms AKLT.W.REC089.prod_activeTips

-- ActualFactorization.lean: theorem
#check AKLT.W.REC089.actual_slots_separate
#print axioms AKLT.W.REC089.actual_slots_separate

-- ActualFactorization.lean: def
#check AKLT.W.REC089.actualTipFactor

-- ActualFactorization.lean: theorem
#check AKLT.W.REC089.actual_factors_separate
#print axioms AKLT.W.REC089.actual_factors_separate

-- Basic.lean: theorem
#check AKLT.W.REC089.dot_comm
#print axioms AKLT.W.REC089.dot_comm

-- Basic.lean: theorem
#check AKLT.W.REC089.dot_zero_right
#print axioms AKLT.W.REC089.dot_zero_right

-- Basic.lean: theorem
#check AKLT.W.REC089.dot_zero_left
#print axioms AKLT.W.REC089.dot_zero_left

-- Basic.lean: theorem
#check AKLT.W.REC089.dot_neg_right
#print axioms AKLT.W.REC089.dot_neg_right

-- Basic.lean: theorem
#check AKLT.W.REC089.dot_div_right
#print axioms AKLT.W.REC089.dot_div_right

-- Basic.lean: theorem
#check AKLT.W.REC089.normSq_nonneg
#print axioms AKLT.W.REC089.normSq_nonneg

-- Basic.lean: theorem
#check AKLT.W.REC089.ball_factor_nonneg
#print axioms AKLT.W.REC089.ball_factor_nonneg

-- Basic.lean: def
#check AKLT.W.REC089.fixedUnit

-- Basic.lean: def
#check AKLT.W.REC089.negateUnit

-- Basic.lean: theorem
#check AKLT.W.REC089.ico_unit
#print axioms AKLT.W.REC089.ico_unit

-- Basic.lean: theorem
#check AKLT.W.REC089.spin_ball
#print axioms AKLT.W.REC089.spin_ball

-- Basic.lean: theorem
#check AKLT.W.REC089.spinWeight_nonneg
#print axioms AKLT.W.REC089.spinWeight_nonneg

-- Basic.lean: theorem
#check AKLT.W.REC089.site_U_mass
#print axioms AKLT.W.REC089.site_U_mass

-- Basic.lean: theorem
#check AKLT.W.REC089.site_U_mean
#print axioms AKLT.W.REC089.site_U_mean

-- Basic.lean: theorem
#check AKLT.W.REC089.site_U_affine
#print axioms AKLT.W.REC089.site_U_affine

-- Basic.lean: theorem
#check AKLT.W.REC089.site_D_split
#print axioms AKLT.W.REC089.site_D_split

-- Basic.lean: theorem
#check AKLT.W.REC089.ball_slot_split
#print axioms AKLT.W.REC089.ball_slot_split

-- CutBonds.lean: theorem
#check AKLT.W.REC089.inside_image_endpoints
#print axioms AKLT.W.REC089.inside_image_endpoints

-- CutBonds.lean: theorem
#check AKLT.W.REC089.crossing_image_endpoints
#print axioms AKLT.W.REC089.crossing_image_endpoints

-- CutBonds.lean: theorem
#check AKLT.W.REC089.cut_disjoint_oi
#print axioms AKLT.W.REC089.cut_disjoint_oi

-- CutBonds.lean: theorem
#check AKLT.W.REC089.cut_disjoint_c
#print axioms AKLT.W.REC089.cut_disjoint_c

-- CutBonds.lean: theorem
#check AKLT.W.REC089.bond_product_cut
#print axioms AKLT.W.REC089.bond_product_cut

-- CutBonds.lean: theorem
#check AKLT.W.REC089.pair_finset_eq
#print axioms AKLT.W.REC089.pair_finset_eq

-- CutBonds.lean: theorem
#check AKLT.W.REC089.trace_present_iff
#print axioms AKLT.W.REC089.trace_present_iff

-- CutBonds.lean: theorem
#check AKLT.W.REC089.trace_bonds_filter
#print axioms AKLT.W.REC089.trace_bonds_filter

-- CutBonds.lean: def
#check AKLT.W.REC089.networkBondTerm

-- CutBonds.lean: theorem
#check AKLT.W.REC089.trace_bond_product
#print axioms AKLT.W.REC089.trace_bond_product

-- CutBonds.lean: theorem
#check AKLT.W.REC089.networkBondTerm_chart
#print axioms AKLT.W.REC089.networkBondTerm_chart

-- CutBonds.lean: theorem
#check AKLT.W.REC089.outgoing_local
#print axioms AKLT.W.REC089.outgoing_local

-- CutBonds.lean: theorem
#check AKLT.W.REC089.network_drop_local
#print axioms AKLT.W.REC089.network_drop_local

-- CutGeometry.lean: abbrev
#check AKLT.W.REC089.chartEquiv

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chart_eq
#print axioms AKLT.W.REC089.chart_eq

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chart_mem_local
#print axioms AKLT.W.REC089.chart_mem_local

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.localSites_sub_G
#print axioms AKLT.W.REC089.localSites_sub_G

-- CutGeometry.lean: def
#check AKLT.W.REC089.slotEdge

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.slotEdge_facts
#print axioms AKLT.W.REC089.slotEdge_facts

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.slotEdge_injective
#print axioms AKLT.W.REC089.slotEdge_injective

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.boundary_slot_classification
#print axioms AKLT.W.REC089.boundary_slot_classification

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.boundary_slot_exists
#print axioms AKLT.W.REC089.boundary_slot_exists

-- CutGeometry.lean: def
#check AKLT.W.REC089.chartEdge

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chartEdge_cases
#print axioms AKLT.W.REC089.chartEdge_cases

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chartEdge_eq_cases
#print axioms AKLT.W.REC089.chartEdge_eq_cases

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chartEdge_injective_internal
#print axioms AKLT.W.REC089.chartEdge_injective_internal

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chartEdge_injective_slots
#print axioms AKLT.W.REC089.chartEdge_injective_slots

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chartEdge_mem
#print axioms AKLT.W.REC089.chartEdge_mem

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.chartEdge_of_bond
#print axioms AKLT.W.REC089.chartEdge_of_bond

-- CutGeometry.lean: def
#check AKLT.W.REC089.outsideBonds

-- CutGeometry.lean: def
#check AKLT.W.REC089.insideBonds

-- CutGeometry.lean: def
#check AKLT.W.REC089.crossingSlots

-- CutGeometry.lean: theorem
#check AKLT.W.REC089.bonds_cut_union
#print axioms AKLT.W.REC089.bonds_cut_union

-- Disintegration.lean: def
#check AKLT.W.REC089.joinSpins

-- Disintegration.lean: theorem
#check AKLT.W.REC089.finite_disintegration
#print axioms AKLT.W.REC089.finite_disintegration

-- Disintegration.lean: def
#check AKLT.W.REC089.localChart

-- Disintegration.lean: def
#check AKLT.W.REC089.localSites

-- Disintegration.lean: def
#check AKLT.W.REC089.insideTemplate

-- Disintegration.lean: abbrev
#check AKLT.W.REC089.ExteriorSpins

-- Disintegration.lean: abbrev
#check AKLT.W.REC089.InteriorSpins

-- Disintegration.lean: theorem
#check AKLT.W.REC089.centre_mem_localSites
#print axioms AKLT.W.REC089.centre_mem_localSites

-- Disintegration.lean: theorem
#check AKLT.W.REC089.trace_active
#print axioms AKLT.W.REC089.trace_active

-- Disintegration.lean: def
#check AKLT.W.REC089.commonFactors

-- Disintegration.lean: def
#check AKLT.W.REC089.commonStatus

-- Disintegration.lean: def
#check AKLT.W.REC089.exteriorMass

-- Disintegration.lean: def
#check AKLT.W.REC089.actualFibre

-- Disintegration.lean: theorem
#check AKLT.W.REC089.exteriorMass_nonneg
#print axioms AKLT.W.REC089.exteriorMass_nonneg

-- Disintegration.lean: def
#check AKLT.W.REC089.supportSpins

-- Disintegration.lean: def
#check AKLT.W.REC089.partitionOn

-- Disintegration.lean: theorem
#check AKLT.W.REC089.partition_eq_partitionOn
#print axioms AKLT.W.REC089.partition_eq_partitionOn

-- Disintegration.lean: theorem
#check AKLT.W.REC089.common_partition
#print axioms AKLT.W.REC089.common_partition

-- Disintegration.lean: theorem
#check AKLT.W.REC089.partition_disintegration
#print axioms AKLT.W.REC089.partition_disintegration

-- ExternalFields.lean: def
#check AKLT.W.REC089.exteriorSpin

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.exteriorSpin_ball
#print axioms AKLT.W.REC089.exteriorSpin_ball

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.joined_exterior
#print axioms AKLT.W.REC089.joined_exterior

-- ExternalFields.lean: def
#check AKLT.W.REC089.pinField

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.pinField_ball
#print axioms AKLT.W.REC089.pinField_ball

-- ExternalFields.lean: def
#check AKLT.W.REC089.physicalSlot

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.physicalSlot_injective
#print axioms AKLT.W.REC089.physicalSlot_injective

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.physicalSlot_facts
#print axioms AKLT.W.REC089.physicalSlot_facts

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.leg_facts
#print axioms AKLT.W.REC089.leg_facts

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.local_legs_image
#print axioms AKLT.W.REC089.local_legs_image

-- ExternalFields.lean: def
#check AKLT.W.REC089.pinTerm

-- ExternalFields.lean: def
#check AKLT.W.REC089.outsidePinProduct

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.pin_product_as_finset
#print axioms AKLT.W.REC089.pin_product_as_finset

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.pin_product_cut
#print axioms AKLT.W.REC089.pin_product_cut

-- ExternalFields.lean: def
#check AKLT.W.REC089.slotField

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.slotField_ball
#print axioms AKLT.W.REC089.slotField_ball

-- ExternalFields.lean: theorem
#check AKLT.W.REC089.slot_cross_pin_product
#print axioms AKLT.W.REC089.slot_cross_pin_product

-- FibreFactors.lean: def
#check AKLT.W.REC089.exteriorFactor

-- FibreFactors.lean: theorem
#check AKLT.W.REC089.exteriorFactor_nonneg
#print axioms AKLT.W.REC089.exteriorFactor_nonneg

-- FibreFactors.lean: theorem
#check AKLT.W.REC089.slot_source_not_zero
#print axioms AKLT.W.REC089.slot_source_not_zero

-- FibreFactors.lean: theorem
#check AKLT.W.REC089.crossing_term
#print axioms AKLT.W.REC089.crossing_term

-- FibreFactors.lean: theorem
#check AKLT.W.REC089.outside_bond_product
#print axioms AKLT.W.REC089.outside_bond_product

-- FibreFactors.lean: theorem
#check AKLT.W.REC089.outside_pin_product
#print axioms AKLT.W.REC089.outside_pin_product

-- FibreFactors.lean: def
#check AKLT.W.REC089.localSlotProduct

-- FibreFactors.lean: theorem
#check AKLT.W.REC089.network_factors_cut
#print axioms AKLT.W.REC089.network_factors_cut

-- FiniteSums.lean: theorem
#check AKLT.W.REC089.joinSpins_inside
#print axioms AKLT.W.REC089.joinSpins_inside

-- FiniteSums.lean: theorem
#check AKLT.W.REC089.joinSpins_outside
#print axioms AKLT.W.REC089.joinSpins_outside

-- FiniteSums.lean: def
#check AKLT.W.REC089.sumAssignmentEquiv

-- FiniteSums.lean: theorem
#check AKLT.W.REC089.sum_eliminate_leaves
#print axioms AKLT.W.REC089.sum_eliminate_leaves

-- InteriorCoordinates.lean: abbrev
#check AKLT.W.REC089.InteriorSite

-- InteriorCoordinates.lean: abbrev
#check AKLT.W.REC089.ActiveTips

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.core_membership
#print axioms AKLT.W.REC089.core_membership

-- InteriorCoordinates.lean: def
#check AKLT.W.REC089.coreInterior

-- InteriorCoordinates.lean: def
#check AKLT.W.REC089.tipInterior

-- InteriorCoordinates.lean: def
#check AKLT.W.REC089.interiorSumMap

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.interiorSumMap_injective
#print axioms AKLT.W.REC089.interiorSumMap_injective

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.interiorSumMap_surjective
#print axioms AKLT.W.REC089.interiorSumMap_surjective

-- InteriorCoordinates.lean: def
#check AKLT.W.REC089.interiorSiteEquiv

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.interiorSiteEquiv_inl
#print axioms AKLT.W.REC089.interiorSiteEquiv_inl

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.interiorSiteEquiv_inr
#print axioms AKLT.W.REC089.interiorSiteEquiv_inr

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.joined_interior
#print axioms AKLT.W.REC089.joined_interior

-- InteriorCoordinates.lean: def
#check AKLT.W.REC089.actualCoreSpins

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.joined_core
#print axioms AKLT.W.REC089.joined_core

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.core_commonStatus
#print axioms AKLT.W.REC089.core_commonStatus

-- InteriorCoordinates.lean: theorem
#check AKLT.W.REC089.tip_commonStatus
#print axioms AKLT.W.REC089.tip_commonStatus

-- InternalBonds.lean: theorem
#check AKLT.W.REC089.pattern_oriented_iff
#print axioms AKLT.W.REC089.pattern_oriented_iff

-- InternalBonds.lean: theorem
#check AKLT.W.REC089.actual_tip_oriented
#print axioms AKLT.W.REC089.actual_tip_oriented

-- InternalBonds.lean: theorem
#check AKLT.W.REC089.inside_bonds_split
#print axioms AKLT.W.REC089.inside_bonds_split

-- InternalBonds.lean: theorem
#check AKLT.W.REC089.inside_bonds_disjoint
#print axioms AKLT.W.REC089.inside_bonds_disjoint

-- InternalBonds.lean: theorem
#check AKLT.W.REC089.networkBondTerm_canonical
#print axioms AKLT.W.REC089.networkBondTerm_canonical

-- InternalBonds.lean: theorem
#check AKLT.W.REC089.inside_bond_product
#print axioms AKLT.W.REC089.inside_bond_product

-- Main.lean: def
#check AKLT.W.REC089.Residual_ActualFibreFactorization

-- Main.lean: def
#check AKLT.W.REC089.Residual_PatternTipFactorization

-- Main.lean: theorem
#check AKLT.W.REC089.actual_fibre_mixture
#print axioms AKLT.W.REC089.actual_fibre_mixture

-- Main.lean: theorem
#check AKLT.W.REC089.main_of_residuals
#print axioms AKLT.W.REC089.main_of_residuals

-- Main.lean: theorem
#check AKLT.W.REC089.main
#print axioms AKLT.W.REC089.main

-- Mixtures.lean: structure
#check AKLT.W.REC089.ConditionalFamily

-- Mixtures.lean: theorem
#check AKLT.W.REC089.flattenConditionalFamily
#print axioms AKLT.W.REC089.flattenConditionalFamily

-- Mixtures.lean: theorem
#check AKLT.W.REC089.ballPatternFamily
#print axioms AKLT.W.REC089.ballPatternFamily

-- PatternFactorization.lean: def
#check AKLT.W.REC089.templateBondTerm

-- PatternFactorization.lean: theorem
#check AKLT.W.REC089.pattern_bond_product_split
#print axioms AKLT.W.REC089.pattern_bond_product_split

-- PatternFactorization.lean: theorem
#check AKLT.W.REC089.pattern_slot_product_split
#print axioms AKLT.W.REC089.pattern_slot_product_split

-- PatternFactorization.lean: def
#check AKLT.W.REC089.patternCoreSpins

-- PatternFactorization.lean: theorem
#check AKLT.W.REC089.pattern_spins_core
#print axioms AKLT.W.REC089.pattern_spins_core

-- PatternFactorization.lean: theorem
#check AKLT.W.REC089.pattern_spins_tip
#print axioms AKLT.W.REC089.pattern_spins_tip

-- PatternFactorization.lean: def
#check AKLT.W.REC089.patternCoreFactors

-- PatternFactorization.lean: def
#check AKLT.W.REC089.patternTipFactor

-- PatternFactorization.lean: theorem
#check AKLT.W.REC089.pattern_factors_separate
#print axioms AKLT.W.REC089.pattern_factors_separate

-- PatternFactorization.lean: theorem
#check AKLT.W.REC089.pattern_tip_factorization
#print axioms AKLT.W.REC089.pattern_tip_factorization

-- Slots.lean: def
#check AKLT.W.REC089.ballPatternFunctional

-- Slots.lean: def
#check AKLT.W.REC089.binaryCoefficient

-- Slots.lean: def
#check AKLT.W.REC089.binaryUnit

-- Slots.lean: theorem
#check AKLT.W.REC089.binaryCoefficient_nonneg
#print axioms AKLT.W.REC089.binaryCoefficient_nonneg

-- Slots.lean: theorem
#check AKLT.W.REC089.binaryCoefficient_sum
#print axioms AKLT.W.REC089.binaryCoefficient_sum

-- Slots.lean: theorem
#check AKLT.W.REC089.product_binary_sum
#print axioms AKLT.W.REC089.product_binary_sum

-- Slots.lean: theorem
#check AKLT.W.REC089.pattern_slots_mixture
#print axioms AKLT.W.REC089.pattern_slots_mixture

-- Template.lean: def
#check AKLT.W.REC089.tipPoint

-- Template.lean: def
#check AKLT.W.REC089.tipNeighbour

-- Template.lean: theorem
#check AKLT.W.REC089.tipPoint_mem
#print axioms AKLT.W.REC089.tipPoint_mem

-- Template.lean: theorem
#check AKLT.W.REC089.tipNeighbour_mem
#print axioms AKLT.W.REC089.tipNeighbour_mem

-- Template.lean: def
#check AKLT.W.REC089.cornerIndex

-- Template.lean: def
#check AKLT.W.REC089.tipIndex

-- Template.lean: def
#check AKLT.W.REC089.packFields

-- Template.lean: theorem
#check AKLT.W.REC089.packFields_corner
#print axioms AKLT.W.REC089.packFields_corner

-- Template.lean: theorem
#check AKLT.W.REC089.packFields_tip
#print axioms AKLT.W.REC089.packFields_tip

-- Template.lean: theorem
#check AKLT.W.REC089.packFields_ball
#print axioms AKLT.W.REC089.packFields_ball

-- Template.lean: def
#check AKLT.W.REC089.coreSites

-- Template.lean: def
#check AKLT.W.REC089.coreBonds

-- Template.lean: def
#check AKLT.W.REC089.coreKernel

-- Template.lean: def
#check AKLT.W.REC089.cornerKernel

-- Template.lean: def
#check AKLT.W.REC089.coverTipBond

-- Template.lean: def
#check AKLT.W.REC089.actualTipStatus

-- Template.lean: def
#check AKLT.W.REC089.actualTipBond

-- Template.lean: def
#check AKLT.W.REC089.actualReduced

-- Template.lean: def
#check AKLT.W.REC089.coveredReduced

-- Template.lean: theorem
#check AKLT.W.REC089.reduced_tip_mixture
#print axioms AKLT.W.REC089.reduced_tip_mixture

-- Template.lean: def
#check AKLT.W.REC089.Matches

-- Template.lean: theorem
#check AKLT.W.REC089.matches_exists
#print axioms AKLT.W.REC089.matches_exists

-- Template.lean: theorem
#check AKLT.W.REC089.matches_tip_kept
#print axioms AKLT.W.REC089.matches_tip_kept

-- Template.lean: theorem
#check AKLT.W.REC089.actual_tip_live
#print axioms AKLT.W.REC089.actual_tip_live

-- Template.lean: theorem
#check AKLT.W.REC089.rotation_straight
#print axioms AKLT.W.REC089.rotation_straight

-- TemplateGeometry.lean: def
#check AKLT.W.REC089.tipEdge

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipPoint_injective
#print axioms AKLT.W.REC089.tipPoint_injective

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipEdge_injective
#print axioms AKLT.W.REC089.tipEdge_injective

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipPoint_surjective
#print axioms AKLT.W.REC089.tipPoint_surjective

-- TemplateGeometry.lean: def
#check AKLT.W.REC089.tipEquiv

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipEquiv_val
#print axioms AKLT.W.REC089.tipEquiv_val

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipEdge_endpoints
#print axioms AKLT.W.REC089.tipEdge_endpoints

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipEdge_internal
#print axioms AKLT.W.REC089.tipEdge_internal

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipEdge_not_core
#print axioms AKLT.W.REC089.tipEdge_not_core

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.internal_tip_classification
#print axioms AKLT.W.REC089.internal_tip_classification

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.coverTipBond_iff
#print axioms AKLT.W.REC089.coverTipBond_iff

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.pattern_bonds_split
#print axioms AKLT.W.REC089.pattern_bonds_split

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.pattern_bonds_disjoint
#print axioms AKLT.W.REC089.pattern_bonds_disjoint

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.pattern_bond_active
#print axioms AKLT.W.REC089.pattern_bond_active

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.pattern_tip_active
#print axioms AKLT.W.REC089.pattern_tip_active

-- TemplateGeometry.lean: def
#check AKLT.W.REC089.patternSiteEquiv

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.patternSiteEquiv_inl
#print axioms AKLT.W.REC089.patternSiteEquiv_inl

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.patternSiteEquiv_inr
#print axioms AKLT.W.REC089.patternSiteEquiv_inr

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.slot_index_equiv
#print axioms AKLT.W.REC089.slot_index_equiv

-- TemplateGeometry.lean: def
#check AKLT.W.REC089.slotEquiv

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.prod_slots
#print axioms AKLT.W.REC089.prod_slots

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tip_slot_site
#print axioms AKLT.W.REC089.tip_slot_site

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.corner_slot_core
#print axioms AKLT.W.REC089.corner_slot_core

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tip_not_centre
#print axioms AKLT.W.REC089.tip_not_centre

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tip_not_outgoing
#print axioms AKLT.W.REC089.tip_not_outgoing

-- TemplateGeometry.lean: theorem
#check AKLT.W.REC089.tipEdge_not_dropped
#print axioms AKLT.W.REC089.tipEdge_not_dropped

-- Tips.lean: def
#check AKLT.W.REC089.tipExternal

-- Tips.lean: def
#check AKLT.W.REC089.tipValue

-- Tips.lean: def
#check AKLT.W.REC089.coveredTipValue

-- Tips.lean: theorem
#check AKLT.W.REC089.neutral_tip
#print axioms AKLT.W.REC089.neutral_tip

-- Tips.lean: theorem
#check AKLT.W.REC089.tip_normalizer_nonneg
#print axioms AKLT.W.REC089.tip_normalizer_nonneg

-- Tips.lean: theorem
#check AKLT.W.REC089.tip_ball_mixture
#print axioms AKLT.W.REC089.tip_ball_mixture
