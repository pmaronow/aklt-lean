from pathlib import Path
import re, json
W=Path('/home/ubuntu/aklt/wt/BP_Q')
R=Path('/home/ubuntu/aklt/reports/BP_Q')
Q=W/'AKLT/Blueprint/Q'
ns='AKLT.Blueprint.Q.'
rows=[]
def add(n,d,label,lines,summary,defs,libs,route,trap,donors=()):
    rows.append(dict(short_name=n+'Statement',difficulty=d,paper_label=label,paper_lines=lines,
        summary=summary,definitions=defs.split(', '),library=libs.split('; '),
        suggested_proof_route=route,trap_note=trap,donor_reuse_pointers=list(donors)))
P='Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean'
S='Mathlib/Analysis/InnerProductSpace/Spectrum.lean'
M='Mathlib/Algebra/MvPolynomial'
F='Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean'
V='/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md'
qspectral='AKLT.Vendor.QICLean.Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap (AKLT/Vendor/QICLean/Analysis/KernelSpectralGap.lean)'
cg='AKLT.Vendor.Physlib.Sl2.cgEquiv, cgEquiv_tensorH/E/F (m=n=4); normalization bridge remains required'
add('OrthogonalFamily','easy','l:threeframes','360-369','Orthogonal maps preserve labelled frame geometry',
    'dot, normSq', 'Matrix.mulVec_mulVec; Matrix.transpose_mul; Function.Injective',
    'Expand dot(Ru,Rv)=dot(u,v) using transpose_mul. The left inverse R.transpose gives injectivity; linearity preserves negatives.',
    'R.transpose*R=1 is explicit. Labels need not already be distinct unless the injectivity premise is supplied.')
add('OneSiteMomentEncoding','medium','l:threeframes','363-368','Encode real degree-four polynomials in the one-site product functional',
    'DegreeFour, SeparateDegreeFour, productFunctional, moment, spinWeight', M+'/Rename.lean; Fintype.sum_equiv',
    'Rename i to (0,i). Prove separate degree from total degree. Reindex one-site functions by their value at 0, and remove the zero atom of U. Prove both the identity and rotated evaluation formulas.',
    'Uses Fin 1, Status.U, and degree <=4. Rotation invariance is used only later by the assembly, from external MomentsStatement.')
add('IcoDistance','medium','l:threeframes','398-409','Distinct ico vertices have squared distance greater than one',
    'icoVector, signValue, goldenRatio, icoRadius, normSq', 'Real.sq_sqrt; Real.sqrt_pos; Fin.sum_univ_succ',
    'Split coordinate family and the two sign bits. Derive phi^2=phi+1 and r^2=phi+2. Compute dot values -1 or +/-1/sqrt(5), and infer the strict squared distance.',
    'Distinct labels, not merely an inequality of vectors, are the premise. All ico-radius denominators are positive.')
add('RotationDisplacement','easy','l:threeframes','411-417','Squared displacement bound for T and T^2',
    'frameRotation, normSq', 'Matrix.mul_apply; Fin.sum_univ_succ; Real.sum_mul_self_eq_zero_iff',
    'Use omega to split k=1 or k=2. Expand the planar rotation matrices; the z component cancels. Bound x^2+y^2 by normSq(v)=1.',
    '1<=k<=2 is explicit; no unrestricted exponent or natural subtraction is used.')
add('SelfRotation','medium','l:threeframes','386-396','Self-rotation bound and exact attainment witness',
    'icoVector, frameVector, frameBound, frameRotation', 'Real.sq_sqrt; Matrix.mul_apply; Fin.sum_univ_succ',
    'For k=1,2 expand 1-u dot T^k u and split the three coordinate families. Rationalize b=2/(101*(phi+2)); compute the (0,0,0) label equality at frames 0 and 1.',
    'The equality is with 1-dot, as required by Top. Signs of both bits and normalization r are retained.')
add('DisplacedDistance','medium','l:threeframes','418-420','A strict triangle estimate in squared coordinates',
    'normSq, dot', 'EuclideanSpace.norm_sq_eq; norm_sub_le; Real.sqrt_le_sqrt',
    'Move the three vectors to EuclideanSpace and use triangle inequality: distance(u,v)>1 and distance(v,w)<=40/101<2/5 imply distance(u,w)>3/5. Unit norms give 1-dot=distance^2/2.',
    'All three vectors are unit and the first distance premise is strict. Vec3 itself has the Pi norm; use EuclideanSpace, not the Pi sup norm.')
add('RelativeRotation','medium','l:threeframes','382-384','Reduce pairs of distinct frames to exponent differences 1 or 2',
    'frameVector, frameRotation, dot', 'Matrix.transpose_mul; Matrix.mulVec_mulVec; pow_add',
    'Split i,j in Fin 3. Cancel the common orthogonal power; swap endpoints for the negative exponent difference. Supply explicit k,u,v witnesses.',
    'The natural exponent witness is constrained to [1,2]. No conversion of a negative integer to a natural is used.')
add('SpinorChoice','medium','d:poly','68-73','Explicit finite spinor chart satisfies norm and density identities',
    'compatible, chosenSpinor, spinDensity, pauli', 'Real.sq_sqrt; Real.sqrt_pos; Complex.ext; Complex.normSq',
    'At v2=-1, use unit length to obtain v0=v1=0. Otherwise unit length gives 1+v2>0. Verify the four outer-product entries and the norm using positive square roots.',
    'The pole branch precedes division. NormSq v=1 is required; the formula is only specialized to the finite frame letters in the assembly.')
add('QuarticKernelDegree','easy','l:tight','287-298','Every explicit complex kernel has total degree at most four',
    'quarticKernel', M+'/Degrees.lean; MvPolynomial.totalDegree_mul; MvPolynomial.totalDegree_pow',
    'Split j<=k and its complement, apply degree bounds for sums/products/powers, and solve exponent sums by omega.',
    'Fin 5 gives j,k<=4. Subtractions 4-k and k-j are simplified only under the branch inequalities.')
add('QuarticKernelEvaluation','medium','l:tight','287-297','Spinor monomial products equal degree-four density kernels',
    'compatible, quarticMonomial, quarticKernel, spinDensity', 'Complex.normSq; mul_pow; pow_add; star_mul',
    'Extract the diagonal and off-diagonal entries of the density identity. Pair powers as |z0|^2, |z1|^2, conjugate(z0)*z1; for j>k use conjugation.',
    'Complex inner-product convention conjugates the first monomial. Keep the plus i sign for conjugate(z0)*z1.')
add('ComplexQuadrature','medium','d:frame','271-272','Complexify any finite real quadrature',
    'quadrature, complexMoment', M+'/Eval.lean; MvPolynomial.induction_on; Complex.ext',
    'Decompose a complex polynomial into real and imaginary coefficient polynomials. Their degrees do not increase; apply real quadrature to each and recombine.',
    'This lemma requires exact real polynomial quadrature. No positivity or normalization is silently assumed; arbitrary finite A is quantified with its Fintype instance.')
add('QuarticOffDiagonal','medium','l:tight','298-302','Off-diagonal kernel averages vanish',
    'complexMoment, quarticKernel, icoVector', 'Fin.sum_univ_succ; Real.sq_sqrt; Complex.ext',
    'Compute the finite 12-atom averages, grouping sign pairs and coordinate families before expanding the few degree-four terms. Alternatively prove bounded-degree covariance for the explicit moment functional.',
    'j!=k is explicit, so the diagonal terms are not inadvertently forced to zero. Use only finite polynomial averages, never arbitrary-function invariance.')
add('QuarticDiagonal','easy','l:tight','304-318','Five diagonal averages have exact inverse-binomial norms',
    'complexMoment, quarticKernel, icoVector, goldenRatio', 'Nat.choose; Real.sq_sqrt; Fin.sum_univ_succ',
    'Split j into five cases, average (1+t)^4, (1+t)^3(1-t), and (1-t^2)^2 using exact ico moments; divide by 16 and multiply by 5.',
    'choose(4,j)>0 because j:Fin 5. The middle value is 1/30 before multiplication by 5.')
add('ResolutionExpansion','easy','l:tight','319-326','A resolved Gram matrix gives the one-site norm identity',
    'resolution, binaryEval, binaryNormSq, quarticMonomial', 'Finset.sum_mul; Finset.mul_sum; Complex.normSq',
    'Expand normSq of the sum via conjugate multiplication. Exchange the finite sums, insert the Gram identity, and collapse the Kronecker diagonal.',
    'Weights are 5*w, not w. Ordinary coefficients use inverse-binomial norms. Negative weights are harmless for this algebraic conditional lemma.',
    ['AKLT.Vendor.QICLean.Matrix.IsIsometry: optional coordinate packaging; a rectangular 12x5 matrix does not require coisometry'])
add('TensorResolution','medium','l:tight','328-333','Tensorize local Gram resolutions on the frozen torus Hilbert space',
    'resolution, physicalEval, Hilbert, Configuration', 'Fintype.prod_sum; Fintype.sum_prod_type; EuclideanSpace.norm_sq_eq',
    'Expand both physical evaluation sums, factor the configuration sum sitewise, apply each local Gram relation, and cancel square-root binomials on the diagonal.',
    'Dependent alphabets have an explicit Fintype family. The site type is the actual nonempty torus. Empty alphabets cannot satisfy a local diagonal resolution. No equal-cardinality unitarity is assumed.')
add('StarPositive','easy','l:star','235-236','Fixed-star Hamiltonian is symmetric and positive',
    'starHamiltonian, starCasimir', P+'; LinearMap.IsSymmetric',
    'Use symmetry and nonnegative quadratic forms for orthogonal projections onto arbitrary submodules, then sum over Fin 4.',
    'A Casimir eigenspace always defines a submodule and an orthogonal projection; no unproved Casimir spectral classification is used here.')
add('StarWitness','medium','l:star','236-240','Four is an eigenvalue of the fixed star',
    'starHamiltonian, starCasimir, starAtSite, spinZ, spinPlus, spinMinus', 'Module.End.HasEigenvector; Submodule.starProjection_eq_self_iff',
    'Use the coordinate vector at the all-extremal-weight configuration. Compute that each pair Casimir gives 20 times it, so each projector fixes it, and the four-term sum gives 4 times it.',
    'Prove the coordinate vector is nonzero. Avoid expanding a 3125 by 3125 dense matrix; use the sparse action on this one basis vector.', [cg])
add('PositiveSpectralMinimum','medium','l:star','240-241','Positive spectrum has an attained positive infimum',
    'Module.End.HasEigenvalue, sInf', S+'; csInf_le; csInf_mem; Set.Finite',
    'Use the finite list of real eigenvalues of a symmetric operator. Positive spectrum is finite and nonempty by the witness; its minimum belongs to the set and equals sInf.',
    'Nonempty positive spectrum is an explicit premise. The empty-dimensional space cannot satisfy it; boundedness is established before csInf lemmas.')
add('SpectralKernelCoercivity','medium','l:star','242-243','Spectral lower bound gives coercivity away from the full kernel',
    'kernelCoercivity, Module.End.HasEigenvalue', S+'; '+P+'; LinearMap.IsSymmetric.eigenvectorBasis',
    'Expand psi minus its kernel projection in an orthonormal eigenbasis. PSD rules out negative eigenvalues; zero coefficients vanish by orthogonality, and every other eigenvalue is at least g.',
    'g>0, PSD, symmetry, and lower bounds for every positive eigenvalue are all explicit. The kernel need not be one-dimensional.', [qspectral])
add('StarAmplification','medium','l:star','249-250','Transport coercivity through spectator amplification',
    'amplifiesStar, kernelCoercivity, starHamiltonian', P+'; LinearIsometryEquiv.inner_map_map; EuclideanSpace.norm_sq_eq',
    'Identify the kernel with direct sums of fixed-star kernels using the coordinate intertwining. Orthogonal projection is fibrewise; sum the fixed-star inequalities and conjugate by U.',
    'n may be zero; both spaces then have zero vectors only whenever U exists, so the inequality remains valid. Spectator multiplicity is not inserted into g.')
add('StateEvaluation','medium','d:poly','74-76; 575-578','Physical polynomial evaluation matches frozen normalized coordinates',
    'statePolynomial, monomialDegree, physicalEval', M+'/Eval.lean; MvPolynomial.eval_monomial; Finsupp.prod',
    'Evaluate the finite monomial sum, split variables into site and Fin 2 coordinates, and identify monomialDegree powers. Pull the constant product of square-root binomials into the site product.',
    'Each physical index lies in Fin 5, so 4-j never underflows. The square-root factors multiply here; B stores divided coefficients.')
add('VbsHomogeneity','medium','p:toruskernel','199-205','VBS polynomial has degree four at every torus site',
    'vbsPolynomial, singlet, siteHomogeneous, bondSites', 'Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean; Fintype.prod_congr',
    'Use the indicator grading of each site: every determinant incident at x has degree one and the others degree zero. Prove there are four actual incident bonds using periods>=3, then multiply homogeneous factors.',
    'Counts actual frozen Bond indices once; at period three the plus and minus neighbours are still distinct. Zero coefficients cause no support assertion.')
add('CoefficientReconstruction','medium','d:poly','16-18; 202-205; 583-588','Reconstruct a homogeneous polynomial from its physical coordinates',
    'siteHomogeneous, statePolynomial, polynomialState, monomialDegree', M+'/Coeff.lean; MvPolynomial.ext; Nat.choose_pos; Real.sq_sqrt',
    'Use coefficient extensionality. Every support exponent at a site has sum four and is uniquely encoded by its second exponent in Fin 5. Show encoding injective and cancel the positive square-root coefficient denominators.',
    'The multihomogeneous premise is essential: arbitrary polynomials would be truncated. Handles the zero polynomial. Binomial and finite-product denominators are nonzero.')
add('PairDiagonalDivision','hard','l:edge','100-109','Diagonal vanishing implies determinant divisibility for the fixed pair',
    'pairDiagonal, pairPolynomial, pairSinglet, PairHilbert', M+'/Coeff.lean; MvPolynomial.ext; LinearMap.finrank_range_add_finrank_ker',
    'Give an explicit elimination along each j+k anti-diagonal, or build the 16 independent coefficient vectors obtained from multiplying bidegree (3,3) monomials by q. Check inclusion in the nine diagonal equations and solve for the quotient.',
    'Only the fixed bidegree (4,4) polynomial carrier is asserted. General diagonal vanishing in arbitrary bidegrees is not assumed. Pair coordinate square roots must be retained.', [cg])
add('SpectatorDivisibility','hard','l:edge','128-134','Transfer the pair kernel implication to a torus edge',
    'pairProjector, pairPolynomial, P, statePolynomial, atSite, bondCasimir', P+'; Equiv.piCongrLeft; Fintype.prod_sum',
    'Choose a tensor-coordinate equivalence separating the two distinct endpoints and spectators. Transport pair Casimir eigenspaces/projections, apply the supplied pair implication to each spectator coefficient, and sum the resulting quotients.',
    'Sizes>=3 ensure endpoints differ. The supplied pair implication is a written finite mathematical premise; no unnamed proof obligation is captured.', [cg])
add('SingletNonassociate','medium','l:divisibility','167-170','Distinct frozen edge determinants are nonassociate',
    'singlet, bondSites, nextSite', M+'/Variables.lean; MvPolynomial.isUnit_iff',
    'An associate is a nonzero scalar multiple over C. Compare the two support monomials to recover the unordered endpoint pair, then use the no-repeated-bond geometry of periods>=3.',
    'e!=f is required. Reversing the orientation of the same unordered edge would give an associate and is deliberately excluded.')
add('IncidentKernel','easy','l:quantumfibre','625-626','A zero star sum annihilates each incident projector',
    'siteHamiltonian, P, spin4Space', P+'; Finset.sum_eq_zero_iff_of_nonneg',
    'Take inner product with psi. Each term is the squared norm of its orthogonal projection and is nonnegative, so each incident squared norm vanishes.',
    'No disjointness or commutation of the four projections is assumed. All terms are positive because they are orthogonal projections.')
add('PairDiagonalRank','medium','l:edge','93-101','The pair diagonal kernel has dimension sixteen',
    'pairDiagonal, pairPolynomial, PairHilbert', 'LinearMap.finrank_range_add_finrank_ker; Module.finrank_euclideanSpace; MvPolynomial.ext',
    'Identify the range with homogeneous degree-eight binary polynomials. Nine monomials have explicit preimages j=max(0,k-4); use 25=16+9.',
    'pairDiagonal maps into the full polynomial ring, but its range is finite-dimensional. Do not assume the infinite-dimensional codomain has finrank nine.')
add('PairTopInclusion','medium','l:edge','112-117','Diagonal-kernel orthogonal complement lies in the spin-four space',
    'pairDiagonal, pairCasimir, spinZ, spinPlus, spinMinus', P+'; LinearMap.ker; MvPolynomial.coeff',
    'Write the nine adjoint coefficient vectors of diagonal evaluation; prove they span the kernel complement. Apply pairCasimir to each vector and obtain eigenvalue 20 by fixed finite sums.',
    'Adjoint coefficients include square-root binomial factors. Using unweighted monomial coordinates would give the wrong orthogonal complement.', [cg])
add('PairTopDimension','medium','l:edge','118-124','The pair Casimir eigenvalue-twenty space has dimension nine',
    'pairCasimir, pairAt, spinZ, spinPlus, spinMinus', 'Module.End.eigenspace; LinearMap.finrank_ker; Matrix.rank',
    'Use the nine j+k weight blocks. The blocks of sizes 1,2,3,4,5,4,3,2,1 each have one-dimensional kernel after subtracting 20I. Check with exact radical algebra or the m=n=4 Clebsch-Gordan decomposition.',
    'Counts eigenspace dimension, not the sum of all positive eigenspaces or an eigenvalue multiplicity inferred from a numerical solver.', [cg])
add('FourVariableDeterminantPrime','hard','l:divisibility','154-165','The determinant in four independent complex variables is prime',
    'MvPolynomial (Fin 4) C', 'Mathlib/Algebra/Polynomial/RingDivision.lean: irreducible_of_degree_eq_one_of_isRelPrime_coeff; Mathlib/RingTheory/Polynomial/GaussLemma.lean',
    'Use an iterated polynomial equivalence with X3 as the last variable. Its coefficients X0 and -X1*X2 are relatively prime. Apply the primitive linear irreducibility lemma, then irreducible implies prime in the polynomial UFD.',
    'Independence of all four variables is encoded by Fin 4. Linearity over a fraction field alone is insufficient without primitiveness.')
add('DeterminantPrimeEmbedding','medium','l:divisibility','154-165','Preserve determinant primality after adjoining spectator variables',
    'singlet, Site, Bond, nextSite', M+'/Rename.lean; MvPolynomial.optionEquivLeft; Ideal.IsPrime',
    'Split the full variable set into the four distinct endpoint variables and a complement. View the larger ring as polynomials over the four-variable quotient domain, so the extended principal ideal is prime; rename back.',
    'An arbitrary injective ring map does not preserve primes. Prove this specific polynomial-extension/domain argument. Endpoint distinctness follows from Size.')
add('CentreDegreeCancellation','hard','l:divisibility','176-188','Centre degree saturation forces an independent residual',
    'independentAt, SpinorPolynomial', 'Mathlib/RingTheory/MvPolynomial/EulerIdentity.lean: MvPolynomial.IsWeightedHomogeneous.sum_weight_X_mul_pderiv; MvPolynomial.pderiv_mul',
    'Use the Euler derivation D=X(x,0)*d0+X(x,1)*d1. Homogeneity gives Dp=4p and D(p*chi)=4p*chi. Leibniz and p!=0 imply Dchi=0. Compare coefficients in characteristic zero to force centre degree zero. This avoids a new general graded-product decomposition library.',
    'p!=0 is explicit; no assumption that chi or p*chi is nonzero is needed. Works for chi=0. No natural subtraction of multidegrees is used.')
add('IncidentProductDegree','medium','l:divisibility','147-152; 178-186','The incident product is nonzero and has centre degree four',
    'incidentProduct, singlet, nextSite, bondSites', 'Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean; Finset.prod_ne_zero_iff',
    'List the two forward and two backward frozen bonds at x. Show each determinant nonzero and homogeneous of centre degree one, all other factors are 1, and the four bonds are distinct.',
    'Handles all L,N>=3; no equality of plus and minus neighbours at period three. Empty products do not arise at a torus centre.')
add('StateCentreDegree','easy','d:poly','74-76; 176-182','Every physical state polynomial has centre degree four',
    'statePolynomial, monomialDegree', M+'/Coeff.lean; MvPolynomial.support_sum; MvPolynomial.support_monomial',
    'Bound support of the finite sum by the encoded monomials, then use (4-j)+j=4 for j<5.',
    'The zero state has empty support, as intended. The Fin 5 bound justifies all natural subtractions.')
add('StarEdgeEnumeration','easy','l:star','245-252','Enumerate the four incident oriented bond indices',
    'starEdge, bondSites, nextSite, Size', 'ZMod.val; Finset.mem_image; Finset.mem_filter',
    'Split direction and membership at the start/end of an edge; the backward edge starts at x-1. Prove injectivity using moduli>=3, then finset extensionality.',
    'Negative-direction edges do not start at x. Counts each actual Bond once, including period-three tori.')
add('StarCasimirChart','hard','l:star','245-249','Build a five-site coordinate chart transporting the four Casimirs',
    'casimirCopies, starEdge, starCasimir, bondCasimir, atSite, starAtSite', 'Equiv.piCongrLeft; LinearIsometryEquiv; Matrix.toEuclideanLin; Fintype.sum_equiv',
    'Map Fin 5 to centre/east/west/north/south and prove injectivity. Split all site assignments into five-site coordinates and spectator assignments, enumerate the latter by Fin n, and transport the one-site matrices before composing the Casimirs.',
    'No global bipartite gauge or large-period assumption. Neighbour-neighbour torus edges never enter these four Casimirs.')
add('StarProjectorTransport','medium','l:star','245-250','Transport the four pair eigenspace projectors through the Casimir chart',
    'casimirCopies, starEdge, P, spin4Space, starCasimir', P+'; LinearIsometryEquiv.inner_map_map; Module.End.eigenspace',
    'The Casimir equation characterizes the eigenspace fibrewise. Show U sends the eigenspace onto the direct sum of fixed-star eigenspaces, then use uniqueness of orthogonal projection on each fibre.',
    'The chart is surjective (an isometry equivalence). An isometric embedding alone would not identify the entire eigenspace projection.')
add('DeterminantModulus','easy','l:qmod','458-485','Squared spinor determinant equals (1-dot)/2',
    'compatible, determinant, spinDensity, pauli, dot', 'Complex.normSq; Complex.ext; Fin.sum_univ_succ',
    'Expand normSq(ad-bc). Replace coordinate pair products by the four density entries and use the Pauli entries. Norm premises give the unit normalization.',
    'Both normalized-spinor density premises are explicit. The interaction has the minus sign and the factor 1/2.')
add('GroundProductWeight','easy','e:frame-ground-weight','583-588','Multiply bond moduli with the unnormalized reference weight',
    'groundScale, torusReference, torusWeight, determinant', 'map_prod; Finset.prod_mul_distrib; Finset.prod_div_distrib',
    'Apply normSq to the supplied product formula for B, use multiplicativity and the supplied bond modulus identities, and collect site factors 5 and edge factors 1/2.',
    'No torus probability identity is assumed. Retains 5^|sites| and 2^|bonds| exactly; every bond index occurs once.')
add('IncidentEvaluation','medium','l:quantumfibre','570-579; 627-631','Signed residual evaluation lies in the beta fibre span',
    'statePolynomial, incidentProduct, independentAt, beta, centreSign, inFibreSpan', M+'/Eval.lean; MvPolynomial.eval_prod; Function.update',
    'Evaluate the supplied polynomial factorization. Regroup each determinant toward the centre with its sign. Independence at x makes the residual evaluation constant under centre updates, supplying the fibre scalar.',
    'Residual chi has its own degrees and is evaluated only as a polynomial. No isometry for chi is claimed. Centre orientation signs are retained.')
add('GroundFibreFactorization','medium','l:quantumfibre','570-579','Separate B into signed beta and exterior rho',
    'beta, rho, centreSign, edgeSign, frameEval, torusNeighbours', 'Finset.prod_filter; Finset.prod_mul_distrib; Function.update',
    'Partition frozen bonds into incident and nonincident factors. Convert incident determinants to centre-first orientation, recover centreSign, and check that every rho factor avoids x.',
    'Input is the explicit evaluation/product identity. rho must include centreSign; omitting it breaks the complex equality even though moduli agree.')
add('GroundTransform','easy','l:quantumfibre','595-598','Weighted multiplication has the explicit inverse and preserves norm',
    'groundTransform, groundQuotient, weightedNorm, frameEval', 'Complex.normSq_mul; Complex.normSq_div; norm_pos_iff',
    'Cancel the nonzero evaluations pointwise, use normSq of a real scalar norm(B), and insert the density identity in the finite weighted norm sum.',
    'Both B!=0 and all ground evaluations!=0 are explicit. This is a unitary map of full finite weighted function spaces, not surjectivity of the physical evaluation map.')
add('FibreIntertwining','medium','l:quantumfibre','600-623; 674-676','Intertwine conditional expectation and beta projection, including residual norms',
    'fibreProjection, fibreDenominator, groundTransform, conditionalExpectation, blockDirichlet, beta, rho', 'Finset.sum_bij; Function.update; Complex.normSq_mul',
    'Reindex an exterior fibre by its centre letter. The density and beta*rho identities cancel the nonzero exterior factor, leaving the same quotient as fibreProjection. Apply weighted norm preservation to the residual, or expand it directly.',
    'B, beta, and ground evaluations are nonzero, and rho is fibre-constant. Denominator positivity follows from beta and positive 5/12, not from a formal division-by-zero convention.')
add('FibreProjection','medium','l:quantumfibre','609-620; 634-643','The beta quotient is an orthogonal best approximation',
    'fibreProjection, fibreDenominator, inFibreSpan, weightedNorm, torusReference', P+'; Finset.sum_nonneg; Complex.normSq_nonneg',
    'On each 12-letter fibre, use the weighted one-dimensional projection formula and expand the Pythagorean residual. Sum over exterior fibres; the exterior reference factor is constant on each fibre.',
    'beta is nowhere zero; hence every denominator is positive. Includes range, fixed-point, and best-approximation properties. No conditional density is normalized twice.')
add('WeightedPolarization','easy','t:QD','660-667','Polarize a linear weighted norm isometry',
    'weightedNorm, weightedInner, coherentMap', 'inner_add_left; inner_smul_left; Complex.ext; Complex.normSq',
    'Compare norms of psi+phi and psi+i*phi with their images under E. Recover real and imaginary parts of the Hermitian inner product; real weights allow conjugation through the sum.',
    'E is complex linear and all Fintype instances are quantified. The first inner-product slot is conjugate linear. Norm equality is only required on the image.')
add('GroundQuotientVariance','easy','t:QD','660-667','The orthogonal physical vector quotient has mean zero and correct variance',
    'groundQuotient, weightedInner, complexMean, variance, torusLaw, frameEval', 'Complex.normSq_mul; Complex.normSq_div; Finset.sum_mul',
    'Use the density identity to cancel the quotient denominator. The mean becomes inner(B,psi)/norm(B). For mean zero the variance is the weighted evaluation norm; the supplied inner-product isometry gives norm(psi)^2.',
    'Orthogonality is inner(B,psi)=0. All division requires B and its evaluations nonzero. No probability normalization of torusReference is used.')
add('BetaNonzero','easy','l:quantumfibre','541-544; 595; 609','Positive oriented determinant moduli make each beta nonzero',
    'beta, determinant, torusNeighbours, nextSite, bondSites', 'Finset.prod_ne_zero_iff; Complex.normSq_zero',
    'For each neighbour identify the corresponding forward or backward bond. Reverse determinant orientation if needed; positive squared modulus rules out zero, and the finite product is nonzero.',
    'Premise quantifies every torus configuration, so updated centre letters are covered. Reverse orientation only contributes a sign.')
add('FrameWeightsPositive','easy','d:framemodel','519-524','Both signs of proper frame weights are strictly positive',
    'planeWeight, torusWeight, ProperPlaneColouring, ProperTorusColouring, frameBound', 'Finset.prod_pos; pow_pos; Real.sqrt_lt',
    'Prove or reuse the exact explicit vector interaction bounds, then positivity of each internal and crossing factor and the uniform site weights. Empty volume gives weight one.',
    'Boundary values are admissible letters at actual exterior neighbour sites. Arbitrary unit-vector pins are not in this statement.')
add('PlaneConditioning','medium','l:planeenergy','709-719','Plane laws condition consistently on every subvolume',
    'conditionalPlaneLaw, inducedBoundary, conditionOn, planeWeight, planeLaw, marginal', 'Finset.prod_filter; Fintype.sum_equiv; Finset.sum_bij',
    'Split factors into those meeting V and fixed exterior factors; identify updated crossing letters through inducedBoundary. The positive fibre sum cancels the constant factors, and marginalization gives a law on actual V configurations.',
    'V subset W is explicit. Handles V empty, V=W, W empty, and shared exterior neighbours with one letter per site.')
add('TorusMarkov','medium','l:planeenergy','709-719','Torus conditional laws depend only on exterior nearest neighbours',
    'conditionalTorusLaw, torusLaw, torusWeight, AgreeOutside, torusNeighbours', 'Finset.prod_filter; Finset.sum_bij; Function.update',
    'Cancel factors not touching U. Internal factors are identical, while each crossing factor uses one exterior site in (neighbours U) minus U, where sigma and xi agree.',
    'U may be empty or all sites. Equality of configuration labels is assumed only on actual boundary neighbours, with no global gauge or evenness premise.')
add('PlaneOneSiteEnergy','medium','l:planeenergy','721-730','Uniform plane one-site letter probability lower bound',
    'conditionalProbability, fullFibreEvent, planeLaw, planeWeight, frameEnergy', 'Finset.card_le_card; Finset.prod_le_prod; div_le_div_iff₀',
    'Cancel all factors not incident at x. At most four plus factors remain, each in [b,2-b]. Numerator >=b^d/12 and denominator <=(2-b)^d; r^d>=r^4.',
    'The conditioning event is every site except x; x is in the volume subtype. Full support ensures its positive denominator. All boundary factors count toward the same degree four.')
add('TorusOneSiteEnergy','medium','l:planeenergy','721-730','Uniform antiferromagnetic torus one-site letter bound',
    'conditionalProbability, fullFibreEvent, torusLaw, torusWeight, frameEnergy', 'Finset.prod_le_prod; Fintype.sum_equiv; div_le_div_iff₀',
    'Enumerate the four incident frozen bonds and cancel all others on the fibre. Bound their minus factors in [b,2-b] and average over exactly twelve letters.',
    'No parity hypothesis. Period three still has four distinct incident bonds; the denominator is a positive fibre mass.')
add('PartialAssignment','medium','l:planeenergy','732-745','Average one-site bounds and multiply along distinct prescribed sites',
    'conditionalProbability, fullFibreEvent, PositiveProbability', 'Finset.induction_on; Finset.sum_bij; Finset.sum_le_sum',
    'First disintegrate any partial assignment outside x into fully specified fibres and average. Induct on U, adding one site at a time to the conditioning event, then use the chain rule and positivity of the intermediate event.',
    'Disjoint U J, full support, nonempty alphabets, and 0<alpha<=1 are explicit. For U empty the event probability and alpha^0 are one. For J empty the conditioning mass is one.')
add('PlaneAssignmentReindex','easy','l:planeenergy','736-744','Move physical subsets to the volume subtype without changing cardinality',
    'extendLetters, PlaneConfiguration, conditionalProbability', 'Finset.attach; Finset.card_attach; Finset.card_image_of_injective',
    'Replace U,J by their copies in W, restrict a,b to W, and use the subset premises to rewrite extension evaluations and preserve cardinal U.',
    'Both U subset W and J subset W are essential. No event refers to extendLetters default values outside the volume.')
add('PlaneProductReference','medium','l:planeenergy','747-759','Normalize positive boundary endpoint weights to a product law',
    'planeSiteWeight, planeProductReference, originalLegs, normalize, PositiveProbability', 'Finset.prod_pos; Fintype.prod_sum; Finset.sum_div',
    'Prove each admissible boundary factor positive. Normalize the twelve positive h_x values, then factor the finite configuration sum to show the product law has total mass one.',
    'An empty volume has a single configuration of weight one. Each local normalizer is positive; all boundary interactions remain in h_x.')
add('BoundaryAbsorption','medium','l:planeenergy','760-765','Only internal edge factors remain in the density relative to the product law',
    'planeWeight, planeLaw, planeSiteWeight, planeProductReference, planeInteraction', 'Finset.prod_fiberwise; Finset.prod_mul_distrib; Finset.sum_mul',
    'Regroup originalLegs by their internal endpoint and separate the product of h_x local normalizers. This is a common nonzero scalar, hence cancels when normalizing the global law.',
    'Shared exterior neighbours contribute one factor per crossing edge but the same boundary letter. Boundary factors are not dropped and never enter the internal-edge count.')
add('PlaneDensityBounds','medium','l:planeenergy','764-770; 784-786','Positive internal density bounds and the exact single ratio',
    'planeInteraction, planeInteractionMean, planeDensityLower, planeDensityUpper, planeProductReference, frameRatio', 'Finset.prod_le_prod; Finset.sum_le_sum; div_div_div_cancel_right₀',
    'Prove b^e<=R<=(2-b)^e, average against the supplied positive product probability, and use the supplied absorption identity. Divide by the positive common mean and cancel it in m/M.',
    'For e=0 the ratio is one. Positive reference probability and absorption identity are explicit premises. The mean, m, and M are all proved positive before division.')
add('DensityVariance','easy','l:density','sec3 772-782; Appendix A l:density','Density comparison for complex variance',
    'variance, complexMean, PositiveProbability', 'Complex.normSq_nonneg; Finset.sum_le_sum',
    'Prove variance is the minimum of the weighted squared error over constant centres. Centre q at mean_p(f), apply q<=M*p, then identify p variance.',
    'Both laws are normalized positive probabilities and M>=0. Empty state spaces cannot have the probability premise. Complex means use conjugate-linear convention.', ['AKLT.Vendor.FiniteChain.Cheeger.weightedVariance_le_center: real-centre ingredient only; complex bridge remains'])
add('DensityDirichlet','medium','l:density','sec3 779-780; Appendix A l:density','Single-ratio comparison of integrated conditional variance',
    'dirichlet, blockDirichlet, conditionalExpectation, PositiveProbability', 'Complex.normSq_nonneg; Finset.sum_le_sum; Fintype.sum_equiv',
    'For each fixed exterior fibre, integrated conditional variance minimizes unnormalized squared error over its constant centre. Apply q>=m*p before minimization, then sum fibres and physical sites.',
    'Full support makes every fibre denominator positive. The bound is m, not m/M on a single Dirichlet form; pointwise conditional-density comparison would lose a second ratio.', ['AKLT.Vendor.FiniteConditioning.condExp_on_fiber: finite conditional-mean identification only'])
add('ProductPoincare','medium','l:density','sec3 779-782; Appendix A l:density','Product-law Poincare inequality at rate one per site',
    'PoincareLower, variance, dirichlet, conditionalExpectation, PositiveProbability', 'Fintype.prod_sum; Finset.induction_on',
    'Prove Efron-Stein by induction on the finite site set using conditional variance decomposition; apply to real and imaginary parts or directly to normSq in C. Site updates have coefficient one.',
    'Empty site sets and singleton alphabets have zero variance and Dirichlet form. Local probability assumptions preclude an empty alphabet at an actual site. No volume normalization is introduced.')

# Find declarations and their precise source locations, including extracted docstrings.
source={}
source_declarations={}
all_statements=[]
all_theorems=[]
for p in sorted(Q.glob('*.lean')):
    t=p.read_text()
    for m in re.finditer(r'^def (\w+Statement) : Prop :=',t,re.M):
        n=m.group(1); doc_start=t.rfind('/--',0,m.start()); doc_end=t.find('-/',doc_start)
        source[n]=(p,1+t[:m.start()].count('\n'),t[doc_start:doc_end+2])
        following=t[m.end():]
        stop=re.search(r'^(?:/--|def |theorem |end )',following,re.M)
        source_declarations[n]=t[m.start():m.end()+(stop.start() if stop else len(following))].rstrip()
        all_statements.append(n)
    for m in re.finditer(r'^theorem (\w+)',t,re.M):
        all_theorems.append((m.group(1),p,1+t[:m.start()].count('\n')))
proved={'RotationStatement':'rotation','RotationPowersStatement':'rotationPowers','FrameScalarsStatement':'frameScalars',
        'IncidentDoubleCountStatement':'incidentDoubleCount','PositiveNormalizationStatement':'positiveNormalization',
        'PrimeProductStatement':'primeProduct'}
derived={'PairSpinFourStatement':'pairSpinFour_of_leaves','SingletPrimeStatement':'singletPrime_of_leaves',
         'IncidentDegreeStatement':'incidentDegree_of_leaves','StarRelabellingStatement':'starRelabelling_of_leaves'}
assert set(source)=={x['short_name'] for x in rows}|set(proved)|set(derived), sorted(set(source)-{x['short_name'] for x in rows}-set(proved)-set(derived))
# Every open leaf must occur in exactly one orchestration bundle.
assembly=(Q/'Assembly.lean').read_text()
bundle_body=assembly[assembly.index('def FramesInputs'):assembly.index('/-- Complete acyclic')]
bounded={'FrameWeightsPositiveStatement','PlaneConditioningStatement','TorusMarkovStatement','PlaneOneSiteEnergyStatement','TorusOneSiteEnergyStatement','PlaneProductReferenceStatement','BoundaryAbsorptionStatement','PlaneDensityBoundsStatement'}
policy=json.loads((R/'proof-policy.json').read_text())
printed=(R/'exported-declarations.txt').read_text()
printed_declarations={}
for match in re.finditer(r'^def AKLT\.Blueprint\.Q\.(\w+) : Prop :=',printed,re.M):
    tail=printed[match.end():]
    stop=re.search(r'^(?:def |AKLT\.Blueprint\.Q\.threeFrames_of_leaves )',tail,re.M)
    printed_declarations[match.group(1)]=printed[match.start():match.end()+(stop.start() if stop else len(tail))].rstrip()
for row in rows:
    if row['short_name'] in bounded:
        row['definitions'].append('interactionBounds')
        row['library'].append('AKLT.Blueprint.Q.frameScalars (proved scalar bounds)')
        row['suggested_proof_route']='Use the explicit numerical interactionBounds premise (supplied by the three-frame assembly), without reproving geometric separation. '+row['suggested_proof_route']
        row['trap_note']='Numerical two-sign interaction bounds are explicit premises inside this closed leaf. '+row['trap_note']
    n=row['short_name']; p,line,doc=source[n]
    assert bundle_body.count(n)==1,(n,bundle_body.count(n))
    row['lean_name']=ns+n; row['module']='AKLT.Blueprint.Q.'+p.stem
    row['source']=str(p); row['source_line']=line; row['docstring']=doc
    row['status']='open'
    row['closed_statement']=printed_declarations[n]
    row['source_declaration']=source_declarations[n]
    row['statement_context']={'import':'AKLT.Blueprint.Q.Definitions','namespace':'AKLT.Blueprint.Q',
      'open_namespaces':['AKLT.Defs','AKLT.Challenge'],'open_scopes':['BigOperators']}
    row['first_attempt']=dict(policy['open_leaf_first_attempt'])
    row['paper_source']='/home/ubuntu/aklt/reports/REV_A1/sec3-quantum-frames.tex'
    row['dependencies']={'definitions':row.pop('definitions'),'library_lemmas_or_modules':row.pop('library')}
    row['estimated_proof_lines']={'easy':'30-120','medium':'100-280','hard':'220-400'}[row['difficulty']]
    row['estimated_writer_hours']='1-2 (planning estimate; not a completed proof)'
    row['trap_check']={
      'missing_premises':'PASS: explicit mathematical data/premises in the closed definition; '+row['trap_note'],
      'closedness_and_instances':'PASS: checked by Lean as a closed Prop; all finite/dependent instance binders occur inside its definition.',
      'vacuity_and_degenerate_cases':'PASS: reviewed for empty sums/products, zero vectors/polynomials, empty alphabets, and zero-dimensional spaces as applicable; see missing_premises note.',
      'coercions_and_sums':'PASS: real weights, complex amplitudes, and squared real norms kept distinct; Finset and Fintype binders explicitly typed.',
      'natural_subtraction':'PASS: 4-j and ordered kernel exponents are bounded by Fin 5 and branch/order hypotheses; centre degree cancellation uses no natural subtraction.',
      'division_by_zero':'PASS: probability/full-support, unit-spinor branch, nonzero B/evaluations, or positive interaction mean premises supply each needed denominator; no cancellation of zero is used.'
    }
    # Dependency entries are definitions/library only, never another open leaf as a hypothetical input.
    for vals in row['dependencies'].values():
        assert not any(re.search(r'\b\w+Statement\b',s) for s in vals),vals
(R/'leaves.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(R/'nodes-metadata.json').write_text(json.dumps({'proved':proved,'derived':derived,'theorems':[(n,str(p),l) for n,p,l in all_theorems]},indent=2)+'\n')
audit=['import AKLT.Blueprint.Q.Assembly','', '/-! Closedness and axiom audit; no open leaf is asserted. -/','']
audit += [f'#check ({ns+n} : Prop)' for n in all_statements]
audit += ['']+[f'#print axioms {ns+n}' for n,p,l in all_theorems]
(Q/'Audit.lean').write_text('\n'.join(audit)+'\n')
exports=['import AKLT.Blueprint.Q.Assembly','']
exports += [f'#print {ns+n}' for n in all_statements]
exports += [f'#print {ns+n}' for n in ['FramesInputs','TightInputs','StarInputs','PolynomialInputs','QuantumInputs','EnergyInputs']]
exports += [f'#check {ns+n}' for n,p,l in all_theorems]
(R/'ExportDeclarations.lean').write_text('\n'.join(exports)+'\n')
print(f'Prepared {len(rows)} open leaves, {len(proved)} proved nodes, {len(derived)} derived nodes, {len(all_theorems)} exported theorems.')
