import AKLT.W.H1M006.Main

-- Check the requested closed type, including its exact declaration name.
example : AKLT.Blueprint.H1.PassageFubiniStatement := AKLT.W.H1M006.main

-- All public task declarations.
#check AKLT.W.H1M006.passageComplement
#check AKLT.W.H1M006.originalSummand
#check AKLT.W.H1M006.erasedSummand
#check AKLT.W.H1M006.splitAssignments
#check AKLT.W.H1M006.origin_mem_template
#check AKLT.W.H1M006.origin_active
#check AKLT.W.H1M006.passageSites
#check AKLT.W.H1M006.passageEdges
#check AKLT.W.H1M006.mem_active_iff
#check AKLT.W.H1M006.passage_sites_geometry
#check AKLT.W.H1M006.origin_not_tip
#check AKLT.W.H1M006.passage_kept
#check AKLT.W.H1M006.template_incident_edges
#check AKLT.W.H1M006.passage_edge_internal
#check AKLT.W.H1M006.covered_incident_subset
#check AKLT.W.H1M006.passage_edge_mem_iff
#check AKLT.W.H1M006.covered_incident_edges
#check AKLT.W.H1M006.external_not_origin
#check AKLT.W.H1M006.split_spins
#check AKLT.W.H1M006.prod_subtype_erase
#check AKLT.W.H1M006.split_weights
#check AKLT.W.H1M006.dot_symm
#check AKLT.W.H1M006.dot_zero_right
#check AKLT.W.H1M006.dot_zero_left
#check AKLT.W.H1M006.bondFactor
#check AKLT.W.H1M006.bondProduct
#check AKLT.W.H1M006.remainingBondProduct
#check AKLT.W.H1M006.slotProduct
#check AKLT.W.H1M006.localPassageFactor
#check AKLT.W.H1M006.out_edge_incident
#check AKLT.W.H1M006.split_bond_product
#check AKLT.W.H1M006.origin_pair_eq
#check AKLT.W.H1M006.passage_edges_product
#check AKLT.W.H1M006.factor_bonds
#check AKLT.W.H1M006.complementWeight
#check AKLT.W.H1M006.erasedSummand_eq
#check AKLT.W.H1M006.spins_removed
#check AKLT.W.H1M006.split_remaining_bonds
#check AKLT.W.H1M006.split_slots
#check AKLT.W.H1M006.neighbours_not_origin
#check AKLT.W.H1M006.originalSummand_factorized
#check AKLT.W.H1M006.local_fubini
#check AKLT.W.H1M006.main

-- Axiom audit for every public theorem and the assignment equivalence.
#print axioms AKLT.W.H1M006.splitAssignments
#print axioms AKLT.W.H1M006.origin_mem_template
#print axioms AKLT.W.H1M006.origin_active
#print axioms AKLT.W.H1M006.mem_active_iff
#print axioms AKLT.W.H1M006.passage_sites_geometry
#print axioms AKLT.W.H1M006.origin_not_tip
#print axioms AKLT.W.H1M006.passage_kept
#print axioms AKLT.W.H1M006.template_incident_edges
#print axioms AKLT.W.H1M006.passage_edge_internal
#print axioms AKLT.W.H1M006.covered_incident_subset
#print axioms AKLT.W.H1M006.passage_edge_mem_iff
#print axioms AKLT.W.H1M006.covered_incident_edges
#print axioms AKLT.W.H1M006.external_not_origin
#print axioms AKLT.W.H1M006.split_spins
#print axioms AKLT.W.H1M006.prod_subtype_erase
#print axioms AKLT.W.H1M006.split_weights
#print axioms AKLT.W.H1M006.dot_symm
#print axioms AKLT.W.H1M006.dot_zero_right
#print axioms AKLT.W.H1M006.dot_zero_left
#print axioms AKLT.W.H1M006.out_edge_incident
#print axioms AKLT.W.H1M006.split_bond_product
#print axioms AKLT.W.H1M006.origin_pair_eq
#print axioms AKLT.W.H1M006.passage_edges_product
#print axioms AKLT.W.H1M006.factor_bonds
#print axioms AKLT.W.H1M006.erasedSummand_eq
#print axioms AKLT.W.H1M006.spins_removed
#print axioms AKLT.W.H1M006.split_remaining_bonds
#print axioms AKLT.W.H1M006.split_slots
#print axioms AKLT.W.H1M006.neighbours_not_origin
#print axioms AKLT.W.H1M006.originalSummand_factorized
#print axioms AKLT.W.H1M006.local_fubini
#print axioms AKLT.W.H1M006.main
