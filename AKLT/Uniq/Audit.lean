import AKLT.Uniq.Main

/-! Complete declaration and dependency audit for the delivered uniqueness proof. -/

#check AKLT.Uniq.basisScale
#check AKLT.Uniq.basisScale_ne_zero
#print axioms AKLT.Uniq.basisScale_ne_zero
#check AKLT.Uniq.siteWeight
#check AKLT.Uniq.HasSiteDegrees
#check AKLT.Uniq.IsPhysical
#check AKLT.Uniq.encode
#check AKLT.Uniq.decode
#check AKLT.Uniq.monomialDegree_apply
#print axioms AKLT.Uniq.monomialDegree_apply
#check AKLT.Uniq.monomialDegree_injective
#print axioms AKLT.Uniq.monomialDegree_injective
#check AKLT.Uniq.siteWeight_degree
#print axioms AKLT.Uniq.siteWeight_degree
#check AKLT.Uniq.monomialDegree_siteWeight
#print axioms AKLT.Uniq.monomialDegree_siteWeight
#check AKLT.Uniq.degree_four_exists_configuration
#print axioms AKLT.Uniq.degree_four_exists_configuration
#check AKLT.Uniq.coeff_encode
#print axioms AKLT.Uniq.coeff_encode
#check AKLT.Uniq.encode_physical
#print axioms AKLT.Uniq.encode_physical
#check AKLT.Uniq.decode_encode
#print axioms AKLT.Uniq.decode_encode
#check AKLT.Uniq.encode_injective
#print axioms AKLT.Uniq.encode_injective
#check AKLT.Uniq.encode_decode
#print axioms AKLT.Uniq.encode_decode
#check AKLT.Uniq.PolynomialCoordinatesStatement
#check AKLT.Uniq.polynomialCoordinates
#print axioms AKLT.Uniq.polynomialCoordinates
#check AKLT.Uniq.decode_vbs
#print axioms AKLT.Uniq.decode_vbs
#check AKLT.Uniq.physical_homogeneous
#print axioms AKLT.Uniq.physical_homogeneous
#check AKLT.Uniq.physical_totalDegree_le
#print axioms AKLT.Uniq.physical_totalDegree_le
#check AKLT.Uniq.ScalarQuotientStatement
#check AKLT.Uniq.scalarQuotient
#print axioms AKLT.Uniq.scalarQuotient
#check AKLT.Uniq.previousSite
#check AKLT.Uniq.nextSiteEquiv
#check AKLT.Uniq.nextSite_eq_iff
#print axioms AKLT.Uniq.nextSite_eq_iff
#check AKLT.Uniq.bondDegree
#check AKLT.Uniq.sum_bondDegree
#print axioms AKLT.Uniq.sum_bondDegree
#check AKLT.Uniq.TorusGeometryStatement
#check AKLT.Uniq.torusGeometry
#print axioms AKLT.Uniq.torusGeometry
#check AKLT.Uniq.singlet_siteDegrees
#print axioms AKLT.Uniq.singlet_siteDegrees
#check AKLT.Uniq.VBSHomogeneousStatement
#check AKLT.Uniq.vbsHomogeneous
#print axioms AKLT.Uniq.vbsHomogeneous
#check AKLT.Uniq.encode_B
#print axioms AKLT.Uniq.encode_B
#check AKLT.Uniq.singlet_irreducible
#print axioms AKLT.Uniq.singlet_irreducible
#check AKLT.Uniq.SingletPrimeStatement
#check AKLT.Uniq.singletPrime
#print axioms AKLT.Uniq.singletPrime
#check AKLT.Uniq.vbsPolynomial_ne_zero
#print axioms AKLT.Uniq.vbsPolynomial_ne_zero
#check AKLT.Uniq.VBSDegreeStatement
#check AKLT.Uniq.vbsDegree
#print axioms AKLT.Uniq.vbsDegree
#check AKLT.Uniq.B_ne_zero
#print axioms AKLT.Uniq.B_ne_zero
#check AKLT.Uniq.bondDegree_pos_iff
#print axioms AKLT.Uniq.bondDegree_pos_iff
#check AKLT.Uniq.SingletNonassociateStatement
#check AKLT.Uniq.singletNonassociate
#print axioms AKLT.Uniq.singletNonassociate
#check AKLT.Uniq.singlet_pairwise_relPrime
#print axioms AKLT.Uniq.singlet_pairwise_relPrime
#check AKLT.Uniq.ProductDivisibilityStatement
#check AKLT.Uniq.productDivisibility
#print axioms AKLT.Uniq.productDivisibility
#check AKLT.Uniq.vbsPolynomial_dvd
#print axioms AKLT.Uniq.vbsPolynomial_dvd
#check AKLT.Uniq.homogeneous_quotient
#print axioms AKLT.Uniq.homogeneous_quotient
#check AKLT.Uniq.residualDegree
#check AKLT.Uniq.subset_bondDegree_le_four
#print axioms AKLT.Uniq.subset_bondDegree_le_four
#check AKLT.Uniq.product_siteDegrees
#print axioms AKLT.Uniq.product_siteDegrees
#check AKLT.Uniq.product_singlet_ne_zero
#print axioms AKLT.Uniq.product_singlet_ne_zero
#check AKLT.Uniq.QuotientDegreesStatement
#check AKLT.Uniq.quotientDegrees
#print axioms AKLT.Uniq.quotientDegrees
#check AKLT.Uniq.PolynomialDivisibilityStatement
#check AKLT.Uniq.polynomialDivisibility
#print axioms AKLT.Uniq.polynomialDivisibility
#check AKLT.Uniq.incidentBonds
#check AKLT.Uniq.IndependentOn
#check AKLT.Uniq.incident_degree
#print axioms AKLT.Uniq.incident_degree
#check AKLT.Uniq.independentOn_of_degrees
#print axioms AKLT.Uniq.independentOn_of_degrees
#check AKLT.Uniq.PolynomialLocalDivisibilityStatement
#check AKLT.Uniq.polynomialLocalDivisibility
#print axioms AKLT.Uniq.polynomialLocalDivisibility
#check AKLT.Uniq.h_energy
#print axioms AKLT.Uniq.h_energy
#check AKLT.Uniq.HamiltonianKernelStatement
#check AKLT.Uniq.hamiltonianKernel
#print axioms AKLT.Uniq.hamiltonianKernel
#check AKLT.Uniq.atSite_adjoint
#print axioms AKLT.Uniq.atSite_adjoint
#check AKLT.Uniq.onBond_adjoint
#print axioms AKLT.Uniq.onBond_adjoint
#check AKLT.Uniq.spinZ_hermitian
#print axioms AKLT.Uniq.spinZ_hermitian
#check AKLT.Uniq.onBond_Z_symmetric
#print axioms AKLT.Uniq.onBond_Z_symmetric
#check AKLT.Uniq.CasimirSymmetricStatement
#check AKLT.Uniq.casimirSymmetric
#print axioms AKLT.Uniq.casimirSymmetric
#check AKLT.Uniq.casimirDefect
#check AKLT.Uniq.casimirDefect_symmetric
#print axioms AKLT.Uniq.casimirDefect_symmetric
#check AKLT.Uniq.ker_casimirDefect
#print axioms AKLT.Uniq.ker_casimirDefect
#check AKLT.Uniq.ProjectionRangeStatement
#check AKLT.Uniq.projectionRange
#print axioms AKLT.Uniq.projectionRange
#check AKLT.Uniq.projection_eq_zero_iff_range
#print axioms AKLT.Uniq.projection_eq_zero_iff_range
#check AKLT.Uniq.transvectant
#check AKLT.Uniq.transvectant_add
#print axioms AKLT.Uniq.transvectant_add
#check AKLT.Uniq.transvectant_sub
#print axioms AKLT.Uniq.transvectant_sub
#check AKLT.Uniq.transvectant_smul
#print axioms AKLT.Uniq.transvectant_smul
#check AKLT.Uniq.siteEuler
#print axioms AKLT.Uniq.siteEuler
#check AKLT.Uniq.pderiv_zero_of_site_degree_zero
#print axioms AKLT.Uniq.pderiv_zero_of_site_degree_zero
#check AKLT.Uniq.edgeResidual
#check AKLT.Uniq.bondDegree_le_one
#print axioms AKLT.Uniq.bondDegree_le_one
#check AKLT.Uniq.edgeResidual_deriv_arithmetic
#print axioms AKLT.Uniq.edgeResidual_deriv_arithmetic
#check AKLT.Uniq.transvectant_degrees
#print axioms AKLT.Uniq.transvectant_degrees
#check AKLT.Uniq.singlet_pow_mul_physical
#print axioms AKLT.Uniq.singlet_pow_mul_physical
#check AKLT.Uniq.edgeResidual_endpoint
#print axioms AKLT.Uniq.edgeResidual_endpoint
#check AKLT.Uniq.transvectant_degree_four_zero
#print axioms AKLT.Uniq.transvectant_degree_four_zero
#check AKLT.Uniq.singlet_endpoint_degrees
#print axioms AKLT.Uniq.singlet_endpoint_degrees
#check AKLT.Uniq.transvectant_singlet_mul
#print axioms AKLT.Uniq.transvectant_singlet_mul
#check AKLT.Uniq.transvectant_singlet_pow_mul
#print axioms AKLT.Uniq.transvectant_singlet_pow_mul
#check AKLT.Uniq.transvectantRightInverse
#check AKLT.Uniq.transvectantRightInverse_physical
#print axioms AKLT.Uniq.transvectantRightInverse_physical
#check AKLT.Uniq.transvectant_rightInverse
#print axioms AKLT.Uniq.transvectant_rightInverse
#check AKLT.Uniq.TransvectantSurjectiveStatement
#check AKLT.Uniq.transvectantSurjective
#print axioms AKLT.Uniq.transvectantSurjective
#check AKLT.Uniq.atSite_apply
#print axioms AKLT.Uniq.atSite_apply
#check AKLT.Uniq.singleScale
#check AKLT.Uniq.plus_normalization
#print axioms AKLT.Uniq.plus_normalization
#check AKLT.Uniq.minus_normalization
#print axioms AKLT.Uniq.minus_normalization
#check AKLT.Uniq.spectatorScale
#check AKLT.Uniq.basisScale_factor
#print axioms AKLT.Uniq.basisScale_factor
#check AKLT.Uniq.basisScale_update
#print axioms AKLT.Uniq.basisScale_update
#check AKLT.Uniq.scaled_spinPlus
#print axioms AKLT.Uniq.scaled_spinPlus
#check AKLT.Uniq.scaled_spinMinus
#print axioms AKLT.Uniq.scaled_spinMinus
#check AKLT.Uniq.physical_ext
#print axioms AKLT.Uniq.physical_ext
#check AKLT.Uniq.X_pderiv_physical
#print axioms AKLT.Uniq.X_pderiv_physical
#check AKLT.Uniq.coeff_X_pderiv_self
#print axioms AKLT.Uniq.coeff_X_pderiv_self
#check AKLT.Uniq.monomialDegree_step_up
#print axioms AKLT.Uniq.monomialDegree_step_up
#check AKLT.Uniq.monomialDegree_step_down
#print axioms AKLT.Uniq.monomialDegree_step_down
#check AKLT.Uniq.coeff_encode_spinPlus
#print axioms AKLT.Uniq.coeff_encode_spinPlus
#check AKLT.Uniq.coeff_encode_spinMinus
#print axioms AKLT.Uniq.coeff_encode_spinMinus
#check AKLT.Uniq.encode_spinZ
#print axioms AKLT.Uniq.encode_spinZ
#check AKLT.Uniq.encode_spinPlus
#print axioms AKLT.Uniq.encode_spinPlus
#check AKLT.Uniq.encode_spinMinus
#print axioms AKLT.Uniq.encode_spinMinus
#check AKLT.Uniq.SingleSiteActionStatement
#check AKLT.Uniq.singleSiteAction
#print axioms AKLT.Uniq.singleSiteAction
#check AKLT.Uniq.pderiv_commute
#print axioms AKLT.Uniq.pderiv_commute
#check AKLT.Uniq.polyZ
#check AKLT.Uniq.polyPlus
#check AKLT.Uniq.polyMinus
#check AKLT.Uniq.encode_onBond_Z
#print axioms AKLT.Uniq.encode_onBond_Z
#check AKLT.Uniq.encode_onBond_plus
#print axioms AKLT.Uniq.encode_onBond_plus
#check AKLT.Uniq.encode_onBond_minus
#print axioms AKLT.Uniq.encode_onBond_minus
#check AKLT.Uniq.PolynomialCasimirStatement
#check AKLT.Uniq.polynomialCasimir
#print axioms AKLT.Uniq.polynomialCasimir
#check AKLT.Uniq.CasimirActionStatement
#check AKLT.Uniq.casimirAction
#print axioms AKLT.Uniq.casimirAction
#check AKLT.Uniq.EdgeKernelStatement
#check AKLT.Uniq.edgeKernel_of_nodes
#print axioms AKLT.Uniq.edgeKernel_of_nodes
#check AKLT.Uniq.edgeKernel_of_action
#print axioms AKLT.Uniq.edgeKernel_of_action
#check AKLT.Uniq.edgeKernel
#print axioms AKLT.Uniq.edgeKernel
#check AKLT.Uniq.EdgeFactorizationStatement
#check AKLT.Uniq.edgeFactorization
#print axioms AKLT.Uniq.edgeFactorization
#check AKLT.Uniq.UniquenessStatement
#check AKLT.Uniq.uniqueness_of_edge
#print axioms AKLT.Uniq.uniqueness_of_edge
#check AKLT.Uniq.LocalDivisibilityStatement
#check AKLT.Uniq.localDivisibility_of_edge
#print axioms AKLT.Uniq.localDivisibility_of_edge
#check AKLT.Uniq.uniqueness_of_polynomial_nodes
#print axioms AKLT.Uniq.uniqueness_of_polynomial_nodes
#check AKLT.Uniq.uniqueness_of_nodes
#print axioms AKLT.Uniq.uniqueness_of_nodes
#check AKLT.Uniq.localDivisibility
#print axioms AKLT.Uniq.localDivisibility
#check AKLT.Uniq.uniqueness
#print axioms AKLT.Uniq.uniqueness
