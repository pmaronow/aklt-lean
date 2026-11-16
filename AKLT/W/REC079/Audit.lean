import AKLT.W.REC079.Main

/-! Kernel-checked types and axiom audits for every manually exported declaration. -/

#check AKLT.W.REC079.LatticeChart
#check AKLT.W.REC079.LatticeChart.trans
#check AKLT.W.REC079.LatticeChart.translate
#check AKLT.W.REC079.LatticeChart.flip
#check AKLT.W.REC079.LatticeChart.swap
#check AKLT.W.REC079.LatticeChart.orient
#check AKLT.W.REC079.LatticeChart.orient_zero
#print axioms AKLT.W.REC079.LatticeChart.orient_zero
#check AKLT.W.REC079.adjacent_direction
#print axioms AKLT.W.REC079.adjacent_direction
#check AKLT.W.REC079.pair_chart
#print axioms AKLT.W.REC079.pair_chart
#check AKLT.W.REC079.canonicalChart
#check AKLT.W.REC079.canonicalChart_centre
#print axioms AKLT.W.REC079.canonicalChart_centre
#check AKLT.W.REC079.canonicalChart_start
#print axioms AKLT.W.REC079.canonicalChart_start
#check AKLT.W.REC079.canonicalChart_target
#print axioms AKLT.W.REC079.canonicalChart_target
#check AKLT.W.REC079.canonicalWord
#check AKLT.W.REC079.canonicalWord_injective
#print axioms AKLT.W.REC079.canonicalWord_injective
#check AKLT.W.REC079.canonicalWord_vertex
#print axioms AKLT.W.REC079.canonicalWord_vertex
#check AKLT.W.REC079.canonicalWord_baseWeight
#print axioms AKLT.W.REC079.canonicalWord_baseWeight
#check AKLT.W.REC079.responsePair_endpoints_ne
#print axioms AKLT.W.REC079.responsePair_endpoints_ne
#check AKLT.W.REC079.target_trail_avoids_centre
#print axioms AKLT.W.REC079.target_trail_avoids_centre
#check AKLT.W.REC079.target_trail_closed
#print axioms AKLT.W.REC079.target_trail_closed
#check AKLT.W.REC079.realExposure
#check AKLT.W.REC079.realExposure_cast
#print axioms AKLT.W.REC079.realExposure_cast
#check AKLT.W.REC079.realExposure_sum
#print axioms AKLT.W.REC079.realExposure_sum
#check AKLT.W.REC079.realExposure_mul
#print axioms AKLT.W.REC079.realExposure_mul
#check AKLT.W.REC079.realExposure_nonneg
#print axioms AKLT.W.REC079.realExposure_nonneg
#check AKLT.W.REC079.realExposure_mono
#print axioms AKLT.W.REC079.realExposure_mono
#check AKLT.W.REC079.realExposure_filter_le
#print axioms AKLT.W.REC079.realExposure_filter_le
#check AKLT.W.REC079.indexedReward
#check AKLT.W.REC079.canonicalBudget
#check AKLT.W.REC079.kernel_bound_eq_sum
#print axioms AKLT.W.REC079.kernel_bound_eq_sum
#check AKLT.W.REC079.latticeDist_triangle
#print axioms AKLT.W.REC079.latticeDist_triangle
#check AKLT.W.REC079.latticeDist_symm
#print axioms AKLT.W.REC079.latticeDist_symm
#check AKLT.W.REC079.latticeDist_step
#print axioms AKLT.W.REC079.latticeDist_step
#check AKLT.W.REC079.vertex_distance_le
#print axioms AKLT.W.REC079.vertex_distance_le
#check AKLT.W.REC079.responsePair_shift_le
#print axioms AKLT.W.REC079.responsePair_shift_le
#check AKLT.W.REC079.responseEnvelope_nonneg
#print axioms AKLT.W.REC079.responseEnvelope_nonneg
#check AKLT.W.REC079.pairCoefficient_nonneg
#print axioms AKLT.W.REC079.pairCoefficient_nonneg
#check AKLT.W.REC079.trailBaseWeight_nonneg
#print axioms AKLT.W.REC079.trailBaseWeight_nonneg
#check AKLT.W.REC079.pairReward
#check AKLT.W.REC079.indexedReward_eq_pairReward
#print axioms AKLT.W.REC079.indexedReward_eq_pairReward
#check AKLT.W.REC079.indexedReward_nonneg
#print axioms AKLT.W.REC079.indexedReward_nonneg
#check AKLT.W.REC079.canonicalBudget_nonneg
#print axioms AKLT.W.REC079.canonicalBudget_nonneg
#check AKLT.W.REC079.advanceStatus
#check AKLT.W.REC079.advanceStatus_ne_U
#print axioms AKLT.W.REC079.advanceStatus_ne_U
#check AKLT.W.REC079.advanceStatus_twice
#print axioms AKLT.W.REC079.advanceStatus_twice
#check AKLT.W.REC079.iterate_advance_X
#print axioms AKLT.W.REC079.iterate_advance_X
#check AKLT.W.REC079.iterate_advance_ne_U
#print axioms AKLT.W.REC079.iterate_advance_ne_U
#check AKLT.W.REC079.iterate_advance_removed
#print axioms AKLT.W.REC079.iterate_advance_removed
#check AKLT.W.REC079.traceNetwork_status
#print axioms AKLT.W.REC079.traceNetwork_status
#check AKLT.W.REC079.wordVertices_departures
#print axioms AKLT.W.REC079.wordVertices_departures
#check AKLT.W.REC079.prefixNetwork_status
#print axioms AKLT.W.REC079.prefixNetwork_status
#check AKLT.W.REC079.U_departure_first_visit
#print axioms AKLT.W.REC079.U_departure_first_visit
#check AKLT.W.REC079.twice_departed_removed
#print axioms AKLT.W.REC079.twice_departed_removed
#check AKLT.W.REC079.target_status_unchanged
#print axioms AKLT.W.REC079.target_status_unchanged
#check AKLT.W.REC079.canonicalWord_departureCount
#print axioms AKLT.W.REC079.canonicalWord_departureCount
#check AKLT.W.REC079.U_departure_canonical_first_visit
#print axioms AKLT.W.REC079.U_departure_canonical_first_visit
#check AKLT.W.REC079.kernel_dead_removed
#print axioms AKLT.W.REC079.kernel_dead_removed
#check AKLT.W.REC079.traceCoefficient_concat
#print axioms AKLT.W.REC079.traceCoefficient_concat
#check AKLT.W.REC079.traceCoefficient_nonneg
#print axioms AKLT.W.REC079.traceCoefficient_nonneg
#check AKLT.W.REC079.traceCoefficient_snoc
#print axioms AKLT.W.REC079.traceCoefficient_snoc
#check AKLT.W.REC079.trailBaseWeight_snoc
#print axioms AKLT.W.REC079.trailBaseWeight_snoc
#check AKLT.W.REC079.traceCoefficient_le_baseWeight
#print axioms AKLT.W.REC079.traceCoefficient_le_baseWeight
#check AKLT.W.REC079.kernelOrdering_perm
#print axioms AKLT.W.REC079.kernelOrdering_perm
#check AKLT.W.REC079.firstVisitList_nodup
#print axioms AKLT.W.REC079.firstVisitList_nodup
#check AKLT.W.REC079.kernelOrdering_nodup
#print axioms AKLT.W.REC079.kernelOrdering_nodup
#check AKLT.W.REC079.kernelOrdering_mem_iff
#print axioms AKLT.W.REC079.kernelOrdering_mem_iff
#check AKLT.W.REC079.U_departure_mem_ordering
#print axioms AKLT.W.REC079.U_departure_mem_ordering
#check AKLT.W.REC079.long_filters_path_order
#print axioms AKLT.W.REC079.long_filters_path_order
#check AKLT.W.REC079.kernelOrdering_scopes
#print axioms AKLT.W.REC079.kernelOrdering_scopes
#check AKLT.W.REC079.pairSignal
#check AKLT.W.REC079.pairSignal_nonneg
#print axioms AKLT.W.REC079.pairSignal_nonneg
#check AKLT.W.REC079.localResponseReward
#check AKLT.W.REC079.Residual_OrderedExposureV2
#check AKLT.W.REC079.Residual_LocalEnvelopeV2
#check AKLT.W.REC079.localResponseReward_nonneg
#print axioms AKLT.W.REC079.localResponseReward_nonneg
#check AKLT.W.REC079.localResponseReward_le
#print axioms AKLT.W.REC079.localResponseReward_le
#check AKLT.W.REC079.targetFactor_bounds
#print axioms AKLT.W.REC079.targetFactor_bounds
#check AKLT.W.REC079.targetSummand
#check AKLT.W.REC079.targetSummand_le_budget
#print axioms AKLT.W.REC079.targetSummand_le_budget
#check AKLT.W.REC079.main_from_residuals
#print axioms AKLT.W.REC079.main_from_residuals
#check AKLT.W.REC079.firstLength_eq_zero_of_no_closedTrail
#print axioms AKLT.W.REC079.firstLength_eq_zero_of_no_closedTrail
#check AKLT.W.REC079.traceKernelLength_small
#print axioms AKLT.W.REC079.traceKernelLength_small

/-! Additional comparisons and the completed frozen theorem. -/
#check AKLT.W.REC079.remove_active
#print axioms AKLT.W.REC079.remove_active
#check AKLT.W.REC079.remove_present
#print axioms AKLT.W.REC079.remove_present
#check AKLT.W.REC079.remove_auxiliary
#print axioms AKLT.W.REC079.remove_auxiliary
#check AKLT.W.REC079.invariant_remove_consistent
#print axioms AKLT.W.REC079.invariant_remove_consistent
#check AKLT.W.REC079.invariant_nonarrival_present
#print axioms AKLT.W.REC079.invariant_nonarrival_present
#check AKLT.W.REC079.neighbours_pair_distance
#print axioms AKLT.W.REC079.neighbours_pair_distance
#check AKLT.W.REC079.pair_type_pair
#print axioms AKLT.W.REC079.pair_type_pair
#check AKLT.W.REC079.invariant_pair_closure
#print axioms AKLT.W.REC079.invariant_pair_closure
#check AKLT.W.REC079.prefixDeparture
#print axioms AKLT.W.REC079.prefixDeparture
#check AKLT.W.REC079.pair_closure
#print axioms AKLT.W.REC079.pair_closure
#check AKLT.W.REC079.covered_partition_bound
#print axioms AKLT.W.REC079.covered_partition_bound
#check AKLT.W.REC079.covered_ratio
#print axioms AKLT.W.REC079.covered_ratio
#check AKLT.W.REC079.covered_integrated_lower
#print axioms AKLT.W.REC079.covered_integrated_lower
#check AKLT.W.REC079.response_typed
#print axioms AKLT.W.REC079.response_typed
#check AKLT.W.REC079.pairSetup
#print axioms AKLT.W.REC079.pairSetup
#check AKLT.W.REC079.canonical_initial_direction
#print axioms AKLT.W.REC079.canonical_initial_direction
#check AKLT.W.REC079.canonical_word_incoming
#print axioms AKLT.W.REC079.canonical_word_incoming
#check AKLT.W.REC079.canonical_word_straight
#print axioms AKLT.W.REC079.canonical_word_straight
#check AKLT.W.REC079.chart_sub_step
#print axioms AKLT.W.REC079.chart_sub_step
#check AKLT.W.REC079.canonical_arrival
#print axioms AKLT.W.REC079.canonical_arrival
#check AKLT.W.REC079.chart_neighbours
#print axioms AKLT.W.REC079.chart_neighbours
#check AKLT.W.REC079.dot_comm_rec
#print axioms AKLT.W.REC079.dot_comm_rec
#check AKLT.W.REC079.pairSignal_pair
#print axioms AKLT.W.REC079.pairSignal_pair
#check AKLT.W.REC079.pairSignal_zero_of_inactive
#print axioms AKLT.W.REC079.pairSignal_zero_of_inactive
#check AKLT.W.REC079.present_kernel_mem
#print axioms AKLT.W.REC079.present_kernel_mem
#check AKLT.W.REC079.kernel_member_nonarrival
#print axioms AKLT.W.REC079.kernel_member_nonarrival
#check AKLT.W.REC079.neighbour_pair_type_formula
#print axioms AKLT.W.REC079.neighbour_pair_type_formula
#check AKLT.W.REC079.chart_pair_type
#print axioms AKLT.W.REC079.chart_pair_type
#check AKLT.W.REC079.local_envelope
#print axioms AKLT.W.REC079.local_envelope
#check AKLT.W.REC079.passageFactor_one_le
#print axioms AKLT.W.REC079.passageFactor_one_le
#check AKLT.W.REC079.list_product_unit_bounds
#print axioms AKLT.W.REC079.list_product_unit_bounds
#check AKLT.W.REC079.products_le_realExposure
#print axioms AKLT.W.REC079.products_le_realExposure
#check AKLT.W.REC079.fullOrdering
#print axioms AKLT.W.REC079.fullOrdering
#check AKLT.W.REC079.fullOrdering_perm
#print axioms AKLT.W.REC079.fullOrdering_perm
#check AKLT.W.REC079.realExposure_append
#print axioms AKLT.W.REC079.realExposure_append
#check AKLT.W.REC079.realExposure_zero
#print axioms AKLT.W.REC079.realExposure_zero
#check AKLT.W.REC079.pair_kernel_mem
#print axioms AKLT.W.REC079.pair_kernel_mem
#check AKLT.W.REC079.kernel_pair_signal
#print axioms AKLT.W.REC079.kernel_pair_signal
#check AKLT.W.REC079.pair_sets_ne
#print axioms AKLT.W.REC079.pair_sets_ne
#check AKLT.W.REC079.reward_single_le
#print axioms AKLT.W.REC079.reward_single_le
#check AKLT.W.REC079.reward_three_le
#print axioms AKLT.W.REC079.reward_three_le
#check AKLT.W.REC079.present_neighbour_cases
#print axioms AKLT.W.REC079.present_neighbour_cases
#check AKLT.W.REC079.coefficient_outgoing_lower
#print axioms AKLT.W.REC079.coefficient_outgoing_lower
#check AKLT.W.REC079.prefix_coefficients
#print axioms AKLT.W.REC079.prefix_coefficients
#check AKLT.W.REC079.local_log_bound
#print axioms AKLT.W.REC079.local_log_bound
#check AKLT.W.REC079.prefix_ratio_le
#print axioms AKLT.W.REC079.prefix_ratio_le
#check AKLT.W.REC079.ordered_exposure
#print axioms AKLT.W.REC079.ordered_exposure
#check AKLT.W.REC079.main
#print axioms AKLT.W.REC079.main
