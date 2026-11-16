import AKLT.W.GAP014.Main

-- The expected closed type, checked after importing only the deliverable.
#check (AKLT.W.GAP014.main : AKLT.Blueprint.Gap.SignedFrameBlockStatement)

#check AKLT.W.GAP014.ce_sub
#check AKLT.W.GAP014.ce_energy_le
#check AKLT.W.GAP014.ce_variance_identity
#check AKLT.W.GAP014.density_comparison
#check AKLT.W.GAP014.productWeight_probability
#check AKLT.W.GAP014.product_gap

#print axioms AKLT.W.GAP014.ce_sub
#print axioms AKLT.W.GAP014.ce_energy_le
#print axioms AKLT.W.GAP014.ce_variance_identity
#print axioms AKLT.W.GAP014.density_comparison
#print axioms AKLT.W.GAP014.productWeight_probability
#print axioms AKLT.W.GAP014.product_gap
#print axioms AKLT.W.GAP014.main
