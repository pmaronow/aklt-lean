import AKLT.Blueprint.H1.NodesPauli

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option pp.universes true

#print AKLT.Blueprint.H1.BlochPositivityStatement
#print AKLT.Blueprint.H1.PauliExpansionStatement
#print AKLT.Blueprint.H1.PauliProductTraceStatement
#print AKLT.Blueprint.H1.InversionPolynomialStatement
#print AKLT.Blueprint.H1.ProductDensityPositiveStatement
#print AKLT.Blueprint.H1.TraceProductPositiveStatement
#print AKLT.Blueprint.H1.ReducedDegreeStatement
#print AKLT.Blueprint.H1.ReducedFactorStructureStatement

#check (AKLT.Blueprint.H1.BlochPositivityStatement : Prop)
#check (AKLT.Blueprint.H1.PauliExpansionStatement : Prop)
#check (AKLT.Blueprint.H1.PauliProductTraceStatement : Prop)
#check (AKLT.Blueprint.H1.InversionPolynomialStatement : Prop)
#check (AKLT.Blueprint.H1.ProductDensityPositiveStatement : Prop)
#check (AKLT.Blueprint.H1.TraceProductPositiveStatement : Prop)
#check (AKLT.Blueprint.H1.ReducedDegreeStatement : Prop)
#check (AKLT.Blueprint.H1.ReducedFactorStructureStatement : Prop)

#print AKLT.Defs.pauliExponent
#print AKLT.Blueprint.H1.pauliCoordinate
#check Matrix.PosSemidef.kronecker
#check Matrix.PosSemidef.submatrix
#check Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg
#check Matrix.PosSemidef.conjTranspose_mul_mul_same
#check Matrix.PosSemidef.trace_nonneg
#check Matrix.trace_mul_cycle
#print Matrix.PosSemidef
#print Matrix.IsHermitian
