import AKLT.W.REC098.Main

/-! Exact target-type check, signatures, and axiom audit for every named theorem
in this leaf's four proof modules. -/

example : AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2 :=
  AKLT.W.REC098.main

-- Geometry.lean
#check AKLT.W.REC098.adjacent_iff
#check AKLT.W.REC098.adjacent_symm
#check AKLT.W.REC098.adjacent_ne
#check AKLT.W.REC098.step_injective
#check AKLT.W.REC098.neighbours_card
#check AKLT.W.REC098.interior_ball
#check AKLT.W.REC098.interior_neighbours
#check AKLT.W.REC098.wordVertex_zero
#check AKLT.W.REC098.wordVertex_succ
#check AKLT.W.REC098.wordVertex_adjacent

-- Trace.lean
#check AKLT.W.REC098.TraceState
#check AKLT.W.REC098.present_symm
#check AKLT.W.REC098.present_neighbour
#check AKLT.W.REC098.traceStep_active_subset
#check AKLT.W.REC098.traceStep_kept_subset
#check AKLT.W.REC098.traceStep_present_subset
#check AKLT.W.REC098.preserve_present
#check AKLT.W.REC098.presentNeighbours_card_le_kept
#check AKLT.W.REC098.TraceState.step
#check AKLT.W.REC098.traceNetwork_append_step
#check AKLT.W.REC098.prefixNetwork_eq_range
#check AKLT.W.REC098.prefixNetwork_zero
#check AKLT.W.REC098.prefixNetwork_succ
#check AKLT.W.REC098.prefix_state
#check AKLT.W.REC098.normalizeStart_of_not_U
#check AKLT.W.REC098.normalizeStart_present_subset
#check AKLT.W.REC098.normalizeStart_mutual
#check AKLT.W.REC098.initial_state
#check AKLT.W.REC098.traceNetwork_present_subset
#check AKLT.W.REC098.traceNetwork_status_X
#check AKLT.W.REC098.prefix_status_unvisited
#check AKLT.W.REC098.TraceState.restart
#check AKLT.W.REC098.word_arrival
#check AKLT.W.REC098.second_state

-- Local.lean
#check AKLT.W.REC098.rotateDir
#check AKLT.W.REC098.chart
#check AKLT.W.REC098.chart_injective
#check AKLT.W.REC098.rotateDir_surjective
#check AKLT.W.REC098.chart_zero
#check AKLT.W.REC098.chart_add_step
#check AKLT.W.REC098.chart_south
#check AKLT.W.REC098.chart_mem_neighbours
#check AKLT.W.REC098.chart_adjacent
#check AKLT.W.REC098.chart_dist
#check AKLT.W.REC098.templateSites_explicit
#check AKLT.W.REC098.chart_ball
#check AKLT.W.REC098.internalBonds_mem
#check AKLT.W.REC098.positive_either
#check AKLT.W.REC098.internalPresent_iff
#check AKLT.W.REC098.localFlags
#check AKLT.W.REC098.localFlags_match
#check AKLT.W.REC098.localFlags_image
#check AKLT.W.REC098.localFlags_card
#check AKLT.W.REC098.localPattern
#check AKLT.W.REC098.localPattern_status
#check AKLT.W.REC098.localPattern_tip
#check AKLT.W.REC098.localPattern_center_kept
#check AKLT.W.REC098.localPattern_kept_U
#check AKLT.W.REC098.localPattern_kept_notU
#check AKLT.W.REC098.localPattern_kept_match
#check AKLT.W.REC098.localPattern_D_card
#check AKLT.W.REC098.normalizeRotation_step
#check AKLT.W.REC098.state_covered

-- Main.lean
#check AKLT.W.REC098.far_departure_covered
#check AKLT.W.REC098.secondDeparture_distance_pos
#check AKLT.W.REC098.main

-- Geometry.lean
#print axioms AKLT.W.REC098.adjacent_iff
#print axioms AKLT.W.REC098.adjacent_symm
#print axioms AKLT.W.REC098.adjacent_ne
#print axioms AKLT.W.REC098.step_injective
#print axioms AKLT.W.REC098.neighbours_card
#print axioms AKLT.W.REC098.interior_ball
#print axioms AKLT.W.REC098.interior_neighbours
#print axioms AKLT.W.REC098.wordVertex_zero
#print axioms AKLT.W.REC098.wordVertex_succ
#print axioms AKLT.W.REC098.wordVertex_adjacent

-- Trace.lean
#print axioms AKLT.W.REC098.present_symm
#print axioms AKLT.W.REC098.present_neighbour
#print axioms AKLT.W.REC098.traceStep_active_subset
#print axioms AKLT.W.REC098.traceStep_kept_subset
#print axioms AKLT.W.REC098.traceStep_present_subset
#print axioms AKLT.W.REC098.preserve_present
#print axioms AKLT.W.REC098.presentNeighbours_card_le_kept
#print axioms AKLT.W.REC098.TraceState.step
#print axioms AKLT.W.REC098.traceNetwork_append_step
#print axioms AKLT.W.REC098.prefixNetwork_eq_range
#print axioms AKLT.W.REC098.prefixNetwork_zero
#print axioms AKLT.W.REC098.prefixNetwork_succ
#print axioms AKLT.W.REC098.prefix_state
#print axioms AKLT.W.REC098.normalizeStart_of_not_U
#print axioms AKLT.W.REC098.normalizeStart_present_subset
#print axioms AKLT.W.REC098.normalizeStart_mutual
#print axioms AKLT.W.REC098.initial_state
#print axioms AKLT.W.REC098.traceNetwork_present_subset
#print axioms AKLT.W.REC098.traceNetwork_status_X
#print axioms AKLT.W.REC098.prefix_status_unvisited
#print axioms AKLT.W.REC098.TraceState.restart
#print axioms AKLT.W.REC098.word_arrival
#print axioms AKLT.W.REC098.second_state

-- Local.lean
#print axioms AKLT.W.REC098.chart_injective
#print axioms AKLT.W.REC098.rotateDir_surjective
#print axioms AKLT.W.REC098.chart_zero
#print axioms AKLT.W.REC098.chart_add_step
#print axioms AKLT.W.REC098.chart_south
#print axioms AKLT.W.REC098.chart_mem_neighbours
#print axioms AKLT.W.REC098.chart_adjacent
#print axioms AKLT.W.REC098.chart_dist
#print axioms AKLT.W.REC098.templateSites_explicit
#print axioms AKLT.W.REC098.chart_ball
#print axioms AKLT.W.REC098.internalBonds_mem
#print axioms AKLT.W.REC098.positive_either
#print axioms AKLT.W.REC098.internalPresent_iff
#print axioms AKLT.W.REC098.localFlags_match
#print axioms AKLT.W.REC098.localFlags_image
#print axioms AKLT.W.REC098.localFlags_card
#print axioms AKLT.W.REC098.localPattern_status
#print axioms AKLT.W.REC098.localPattern_tip
#print axioms AKLT.W.REC098.localPattern_center_kept
#print axioms AKLT.W.REC098.localPattern_kept_U
#print axioms AKLT.W.REC098.localPattern_kept_notU
#print axioms AKLT.W.REC098.localPattern_kept_match
#print axioms AKLT.W.REC098.localPattern_D_card
#print axioms AKLT.W.REC098.normalizeRotation_step
#print axioms AKLT.W.REC098.state_covered

-- Main.lean
#print axioms AKLT.W.REC098.far_departure_covered
#print axioms AKLT.W.REC098.secondDeparture_distance_pos
#print axioms AKLT.W.REC098.main
