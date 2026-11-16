import AKLT.W.REC096.Main

open AKLT.Defs AKLT.Blueprint.Rec
open AKLT.W.REC096

example : AKLT.Blueprint.Rec.CoveredClosureStatementV2 := AKLT.W.REC096.main

-- Geometry.lean
#check AKLT.W.REC096.natAbs_sub_comm
#check AKLT.W.REC096.natAbs_neg_add
#check AKLT.W.REC096.step_injective
#check AKLT.W.REC096.neighbours_card
#check AKLT.W.REC096.adjacent_iff
#check AKLT.W.REC096.adjacent_symm
#check AKLT.W.REC096.adjacent_ne
#check AKLT.W.REC096.step_adjacent
#check AKLT.W.REC096.chart
#check AKLT.W.REC096.chart_apply
#check AKLT.W.REC096.chart_zero
#check AKLT.W.REC096.chart_south
#check AKLT.W.REC096.chart_dist
#check AKLT.W.REC096.chart_adjacent
#check AKLT.W.REC096.chart_neighbours
#check AKLT.W.REC096.interior_ball
#check AKLT.W.REC096.template_dist
#check AKLT.W.REC096.template_interior

-- Trace.lean
#check AKLT.W.REC096.present_symm
#check AKLT.W.REC096.present_mem_neighbours
#check AKLT.W.REC096.step_status_ne
#check AKLT.W.REC096.step_active_subset
#check AKLT.W.REC096.step_kept_iff
#check AKLT.W.REC096.PrefixInvariant
#check AKLT.W.REC096.invariant_step
#check AKLT.W.REC096.step_preserves_unused

-- Prefix.lean
#check AKLT.W.REC096.initial_invariant
#check AKLT.W.REC096.word_vertex_zero
#check AKLT.W.REC096.word_vertex_succ
#check AKLT.W.REC096.trace_concat
#check AKLT.W.REC096.prefix_zero
#check AKLT.W.REC096.prefix_step
#check AKLT.W.REC096.arrivalSite
#check AKLT.W.REC096.prefix_invariant
#check AKLT.W.REC096.arrival_eq

-- Template.lean
#check AKLT.W.REC096.template_sites_eq
#check AKLT.W.REC096.neighbours_zero
#check AKLT.W.REC096.canonicalOutgoing
#check AKLT.W.REC096.canonical_outgoing_step
#check AKLT.W.REC096.canonical_south
#check AKLT.W.REC096.pullKept
#check AKLT.W.REC096.mem_pullKept
#check AKLT.W.REC096.pullKept_sub
#check AKLT.W.REC096.completedKept
#check AKLT.W.REC096.completedKept_sub
#check AKLT.W.REC096.extractedPattern
#check AKLT.W.REC096.extracted_status
#check AKLT.W.REC096.extracted_kept
#check AKLT.W.REC096.completed_mem_internal
#check AKLT.W.REC096.completed_D_card
#check AKLT.W.REC096.completed_center
#check AKLT.W.REC096.internalBonds_iff
#check AKLT.W.REC096.unoriented_internalBonds
#check AKLT.W.REC096.internal_present_iff
#check AKLT.W.REC096.template_step
#check AKLT.W.REC096.template_tips_sub
#check AKLT.W.REC096.template_corner_facts
#check AKLT.W.REC096.invariant_covered

-- Main.lean
#check AKLT.W.REC096.main

-- Kernel dependency audit for every explicitly declared theorem.
#print axioms AKLT.W.REC096.natAbs_sub_comm
#print axioms AKLT.W.REC096.natAbs_neg_add
#print axioms AKLT.W.REC096.step_injective
#print axioms AKLT.W.REC096.neighbours_card
#print axioms AKLT.W.REC096.adjacent_iff
#print axioms AKLT.W.REC096.adjacent_symm
#print axioms AKLT.W.REC096.adjacent_ne
#print axioms AKLT.W.REC096.step_adjacent
#print axioms AKLT.W.REC096.chart_apply
#print axioms AKLT.W.REC096.chart_zero
#print axioms AKLT.W.REC096.chart_south
#print axioms AKLT.W.REC096.chart_dist
#print axioms AKLT.W.REC096.chart_adjacent
#print axioms AKLT.W.REC096.chart_neighbours
#print axioms AKLT.W.REC096.interior_ball
#print axioms AKLT.W.REC096.template_dist
#print axioms AKLT.W.REC096.template_interior
#print axioms AKLT.W.REC096.present_symm
#print axioms AKLT.W.REC096.present_mem_neighbours
#print axioms AKLT.W.REC096.step_status_ne
#print axioms AKLT.W.REC096.step_active_subset
#print axioms AKLT.W.REC096.step_kept_iff
#print axioms AKLT.W.REC096.invariant_step
#print axioms AKLT.W.REC096.step_preserves_unused
#print axioms AKLT.W.REC096.initial_invariant
#print axioms AKLT.W.REC096.word_vertex_zero
#print axioms AKLT.W.REC096.word_vertex_succ
#print axioms AKLT.W.REC096.trace_concat
#print axioms AKLT.W.REC096.prefix_zero
#print axioms AKLT.W.REC096.prefix_step
#print axioms AKLT.W.REC096.prefix_invariant
#print axioms AKLT.W.REC096.arrival_eq
#print axioms AKLT.W.REC096.template_sites_eq
#print axioms AKLT.W.REC096.neighbours_zero
#print axioms AKLT.W.REC096.canonical_outgoing_step
#print axioms AKLT.W.REC096.canonical_south
#print axioms AKLT.W.REC096.mem_pullKept
#print axioms AKLT.W.REC096.pullKept_sub
#print axioms AKLT.W.REC096.completedKept_sub
#print axioms AKLT.W.REC096.extracted_status
#print axioms AKLT.W.REC096.extracted_kept
#print axioms AKLT.W.REC096.completed_mem_internal
#print axioms AKLT.W.REC096.completed_D_card
#print axioms AKLT.W.REC096.completed_center
#print axioms AKLT.W.REC096.internalBonds_iff
#print axioms AKLT.W.REC096.unoriented_internalBonds
#print axioms AKLT.W.REC096.internal_present_iff
#print axioms AKLT.W.REC096.template_step
#print axioms AKLT.W.REC096.template_tips_sub
#print axioms AKLT.W.REC096.template_corner_facts
#print axioms AKLT.W.REC096.invariant_covered
#print axioms AKLT.W.REC096.main
