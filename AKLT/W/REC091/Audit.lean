import AKLT.W.REC091.Main

-- Types and kernel axioms for every exported declaration in this directory.

-- Departure.lean
#check AKLT.W.REC091.originalLeg_outside
#print axioms AKLT.W.REC091.originalLeg_outside
#check AKLT.W.REC091.neighbour_distance
#print axioms AKLT.W.REC091.neighbour_distance
#check AKLT.W.REC091.no_original_leg_of_unprotected
#print axioms AKLT.W.REC091.no_original_leg_of_unprotected
#check AKLT.W.REC091.trace_active
#print axioms AKLT.W.REC091.trace_active
#check AKLT.W.REC091.trace_neighbours
#print axioms AKLT.W.REC091.trace_neighbours
#check AKLT.W.REC091.remove_trace_status
#print axioms AKLT.W.REC091.remove_trace_status
#check AKLT.W.REC091.remove_trace_bonds
#print axioms AKLT.W.REC091.remove_trace_bonds
#check AKLT.W.REC091.partition_congr
#print axioms AKLT.W.REC091.partition_congr
#check AKLT.W.REC091.remove_trace_partition
#print axioms AKLT.W.REC091.remove_trace_partition
#check AKLT.W.REC091.departure_disintegration
#print axioms AKLT.W.REC091.departure_disintegration

-- Factorizations.lean
#check AKLT.W.REC091.partition_affine_one
#print axioms AKLT.W.REC091.partition_affine_one
#check AKLT.W.REC091.partition_affine_three
#print axioms AKLT.W.REC091.partition_affine_three
#check AKLT.W.REC091.twoFactorization
#print axioms AKLT.W.REC091.twoFactorization
#check AKLT.W.REC091.threeFactorization
#print axioms AKLT.W.REC091.threeFactorization
#check AKLT.W.REC091.stepRatio_two
#print axioms AKLT.W.REC091.stepRatio_two
#check AKLT.W.REC091.stepRatio_three
#print axioms AKLT.W.REC091.stepRatio_three

-- Graph.lean
#check AKLT.W.REC091.adjacent_symm
#print axioms AKLT.W.REC091.adjacent_symm
#check AKLT.W.REC091.present_symm
#print axioms AKLT.W.REC091.present_symm
#check AKLT.W.REC091.mem_internalBonds
#print axioms AKLT.W.REC091.mem_internalBonds
#check AKLT.W.REC091.internalBonds_asymm
#print axioms AKLT.W.REC091.internalBonds_asymm
#check AKLT.W.REC091.positive_neighbour_ne
#print axioms AKLT.W.REC091.positive_neighbour_ne
#check AKLT.W.REC091.positive_mem_neighbours
#print axioms AKLT.W.REC091.positive_mem_neighbours
#check AKLT.W.REC091.present_edge
#print axioms AKLT.W.REC091.present_edge
#check AKLT.W.REC091.otherEndpoint
#check AKLT.W.REC091.incident_image
#print axioms AKLT.W.REC091.incident_image
#check AKLT.W.REC091.incident_injective
#print axioms AKLT.W.REC091.incident_injective

-- Integrals.lean
#check AKLT.W.REC091.siteFunctional_D
#print axioms AKLT.W.REC091.siteFunctional_D
#check AKLT.W.REC091.integrate_U_three
#print axioms AKLT.W.REC091.integrate_U_three
#check AKLT.W.REC091.integrate_U_two
#print axioms AKLT.W.REC091.integrate_U_two
#check AKLT.W.REC091.integrate_U_one
#print axioms AKLT.W.REC091.integrate_U_one
#check AKLT.W.REC091.integrate_D_two
#print axioms AKLT.W.REC091.integrate_D_two
#check AKLT.W.REC091.integrate_D_one
#print axioms AKLT.W.REC091.integrate_D_one

-- Main.lean
#check (AKLT.W.REC091.main : AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2)
#print axioms AKLT.W.REC091.main
#check AKLT.W.REC091.Residual_SharedCoverMixture
#check AKLT.W.REC091.Residual_StepFactorizations
#check AKLT.W.REC091.Residual_RemovedPartitionPositive
#check AKLT.W.REC091.stepFactorizations
#print axioms AKLT.W.REC091.stepFactorizations
#check AKLT.W.REC091.removedPartitionPositive
#print axioms AKLT.W.REC091.removedPartitionPositive
#check AKLT.W.REC091.Residual_PartitionLower
#check AKLT.W.REC091.partitionLower_of_sharedCoverMixture
#print axioms AKLT.W.REC091.partitionLower_of_sharedCoverMixture
#check AKLT.W.REC091.main_of_residuals
#print axioms AKLT.W.REC091.main_of_residuals
#check AKLT.W.REC091.main_from_core_residuals
#print axioms AKLT.W.REC091.main_from_core_residuals
#check AKLT.W.REC091.main_of_partitionLower
#print axioms AKLT.W.REC091.main_of_partitionLower
#check AKLT.W.REC091.main_of_sharedCoverMixture
#print axioms AKLT.W.REC091.main_of_sharedCoverMixture

-- OneSite.lean
#check AKLT.W.REC091.bondWeights_insert
#print axioms AKLT.W.REC091.bondWeights_insert
#check AKLT.W.REC091.legWeights_insert
#print axioms AKLT.W.REC091.legWeights_insert
#check AKLT.W.REC091.networkWeight_insert
#print axioms AKLT.W.REC091.networkWeight_insert
#check AKLT.W.REC091.partition_integrate_site
#print axioms AKLT.W.REC091.partition_integrate_site

-- Positive.lean
#check AKLT.W.REC091.hemisphere_avoid
#print axioms AKLT.W.REC091.hemisphere_avoid
#check AKLT.W.REC091.originalLeg_neighbour
#print axioms AKLT.W.REC091.originalLeg_neighbour
#check AKLT.W.REC091.originalLegs_at_card
#print axioms AKLT.W.REC091.originalLegs_at_card
#check AKLT.W.REC091.network_spins_ball
#print axioms AKLT.W.REC091.network_spins_ball
#check AKLT.W.REC091.networkWeight
#check AKLT.W.REC091.partition_eq_sum_weight
#print axioms AKLT.W.REC091.partition_eq_sum_weight
#check AKLT.W.REC091.networkWeight_nonneg
#print axioms AKLT.W.REC091.networkWeight_nonneg
#check AKLT.W.REC091.network_partition_nonneg
#print axioms AKLT.W.REC091.network_partition_nonneg
#check AKLT.W.REC091.network_partition_pos
#print axioms AKLT.W.REC091.network_partition_pos
#check AKLT.W.REC091.removedPairMean_bounds
#print axioms AKLT.W.REC091.removedPairMean_bounds
#check AKLT.W.REC091.responseJ_pos
#print axioms AKLT.W.REC091.responseJ_pos

-- Remove.lean
#check AKLT.W.REC091.remove_active
#print axioms AKLT.W.REC091.remove_active
#check AKLT.W.REC091.mem_remove_active
#print axioms AKLT.W.REC091.mem_remove_active
#check AKLT.W.REC091.remove_bonds
#print axioms AKLT.W.REC091.remove_bonds
#check AKLT.W.REC091.removalSiteEquiv
#check AKLT.W.REC091.insertSpin
#check AKLT.W.REC091.removalConfigEquiv
#check AKLT.W.REC091.removalConfigEquiv_symm
#print axioms AKLT.W.REC091.removalConfigEquiv_symm
#check AKLT.W.REC091.insertSpin_y
#print axioms AKLT.W.REC091.insertSpin_y
#check AKLT.W.REC091.insertSpin_ne
#print axioms AKLT.W.REC091.insertSpin_ne
#check AKLT.W.REC091.spins_insert_y
#print axioms AKLT.W.REC091.spins_insert_y
#check AKLT.W.REC091.spins_insert_ne
#print axioms AKLT.W.REC091.spins_insert_ne
#check AKLT.W.REC091.siteWeights_insert
#print axioms AKLT.W.REC091.siteWeights_insert

-- Spin.lean
#check AKLT.W.REC091.normSq_nonneg
#print axioms AKLT.W.REC091.normSq_nonneg
#check AKLT.W.REC091.dot_comm
#print axioms AKLT.W.REC091.dot_comm
#check AKLT.W.REC091.normSq_add
#print axioms AKLT.W.REC091.normSq_add
#check AKLT.W.REC091.normSq_sub
#print axioms AKLT.W.REC091.normSq_sub
#check AKLT.W.REC091.dot_bounds
#print axioms AKLT.W.REC091.dot_bounds
#check AKLT.W.REC091.eq_neg_of_dot_eq_neg_one
#print axioms AKLT.W.REC091.eq_neg_of_dot_eq_neg_one
#check AKLT.W.REC091.goldenRatio_pos
#print axioms AKLT.W.REC091.goldenRatio_pos
#check AKLT.W.REC091.goldenRatio_gt_one
#print axioms AKLT.W.REC091.goldenRatio_gt_one
#check AKLT.W.REC091.goldenRatio_sq
#print axioms AKLT.W.REC091.goldenRatio_sq
#check AKLT.W.REC091.icoRadius_pos
#print axioms AKLT.W.REC091.icoRadius_pos
#check AKLT.W.REC091.icoRadius_sq
#print axioms AKLT.W.REC091.icoRadius_sq
#check AKLT.W.REC091.ico_unit
#print axioms AKLT.W.REC091.ico_unit
#check AKLT.W.REC091.spin_ball
#print axioms AKLT.W.REC091.spin_ball
#check AKLT.W.REC091.spinWeight_nonneg
#print axioms AKLT.W.REC091.spinWeight_nonneg
#check AKLT.W.REC091.spinWeight_some_pos
#print axioms AKLT.W.REC091.spinWeight_some_pos
#check AKLT.W.REC091.hemisphereLetter
#check AKLT.W.REC091.coordinateSum
#check AKLT.W.REC091.hemisphere_positive
#print axioms AKLT.W.REC091.hemisphere_positive
#check AKLT.W.REC091.hemisphere_injective
#print axioms AKLT.W.REC091.hemisphere_injective
#check AKLT.W.REC091.hemisphere_bond_pos
#print axioms AKLT.W.REC091.hemisphere_bond_pos

example (h : AKLT.W.REC091.Residual_SharedCoverMixture) :
    AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 :=
  AKLT.W.REC091.main_of_sharedCoverMixture h

example (h : AKLT.W.REC091.Residual_PartitionLower) :
    AKLT.Blueprint.Rec.CoveredIntegratedLowerStatementV2 :=
  AKLT.W.REC091.main_of_partitionLower h

example : AKLT.Blueprint.Rec.TwoFactorizationStatement :=
  AKLT.W.REC091.twoFactorization

example : AKLT.Blueprint.Rec.ThreeFactorizationStatement :=
  AKLT.W.REC091.threeFactorization
