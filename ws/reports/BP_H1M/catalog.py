from pathlib import Path
import re, json
root=Path('/home/ubuntu/aklt/wt/BP_H1M'); folder=root/'AKLT/Blueprint/H1'; out=Path('/home/ubuntu/aklt/reports/BP_H1M')
# Each row describes one independent, closed, open mathematical leaf.
rows='''
PassageSiteMomentsStatement|medium|MonomialMoments;siteFunctional;dot;rationalStatusMoment|Expand the product into coordinate monomials of degree at most three, apply the supplied exact U/D moments, and collect the three dot products.
PassageFubiniStatement|hard|PassageNeighbours;patternFunctional;withoutPassageFunctional;supportSpins|Split assignments on active sites into the passage coordinate and its complement. Coveredness identifies the three possible incident bonds. Apply the supplied one-site equations with zero for removed neighbours.
PassageNetworkPositiveStatement|medium|FiniteSpinNetwork.Valid;withoutPassageFunctional;externalSlot|Enumerate the erased active set by Fin n, retain all slots, count at most four factors at each site, and invoke the supplied finite-network partition positivity.
PassageNextLowerBoundStatement|medium|passageJ;spinWeight;supportSpins;UnitVector|From the supplied unit-atom norms show every positive-weight spin is in the ball. Cauchy-Schwarz bounds the dot product below by -1. All weights, bonds and pin factors are nonnegative, so sum the pointwise J >= 4/5 inequality.
OriginalDegreeStatement|medium|InternalAdmissible;originalIntegrand;PatternData.Covered;externalSlot|Count incident bonds and slots separately at passage, other neighbours, tips and corners. Use polynomial support inclusions to pass each factor count to monomial degrees; show omitted sites have zero exponents.
OriginalFactorStructureStatement|medium|LocalVectorAffine;IntegrandInvariant;formalDot;originalIntegrand|Every slot index occurs in exactly one factor. Orthogonal matrices preserve the dot product, so evaluation of each factor is unchanged under simultaneous spin and slot rotation.
OriginalRawEvaluationStatement|easy|rawFunctional;localEvaluation;originalIntegrand;patternFunctional|Push the evaluation ring hom through products and formal dots. Identify supportSpins with PatternData.spins and split the Boolean next branch.
MomentContractionStatement|hard|MonomialMoments;InternalAdmissible;contractSpins;rawFunctional|Expand the finite monomial support and factor the finite spin sum site by site. The support premise accounts for every internal exponent, and degree four licenses exactly the supplied local moments.
MomentCovarianceTransferStatement|hard|MonomialMoments;ProductMomentCovariance;InternalAdmissible;IntegrandInvariant|Specialize external vectors to real coefficients, reindex V by Fin its cardinality, and use the supplied polynomial covariance. Use transpose as inverse rotation to move the transformation from spins to slots. No arbitrary-function invariance is used.
ContractionAffineStatement|medium|LocalVectorAffine;VectorAffine;contractSpins|Use support inclusion for the finite sum of contracted monomials. Projecting exponents along Sum.inr preserves each external token's summed degree; cancellations can only shrink support.
ContractionSupportStatement|easy|LocalSupportedVectors;SupportedVectors;contractSpins|The external exponent is the Sum.inr projection of an input exponent. Finite-sum support inclusion shows that no absent token can be created.
CoveredSlotEnumerationStatement|medium|PatternData.Covered;externalSlot;coveredSiteField;replacementRadius|Enumerate the eight peripheral sites and their two or three assigned slot indices. Read the U tip rule and U/D nonremoved corner alternatives from Covered. Reorder products to localProduct.
CornerMeanBoundsStatement|medium|MonomialMoments;localProduct;localMean;normSq|Compute A and V from the supplied monomial moments. With t=a dot b, prove -1 <= t <= 1 and normSq(a+b)=2+2t. Use the paper's two square factorizations and A>0 before clearing the localMean denominator.
NormalizedMeanFactorStatement|medium|localMean;siteFunctional;localProduct;normSq|Expand the one-bond finite sum as A + V dot v; V/A is localMean. Set u=localMean/rho and use rho>0 and A>0 to clear denominators and obtain normSq u <= 1.
ReducedDegreeStatement|medium|InternalAdmissible;reducedSpinSites;reducedIntegrand;SingleReplacement|Count factors after the chosen deletions. A replaced leaf changes one bond at the surviving endpoint into one linear field. The retained passage has at most three factors, and retained corners have at most four.
ReducedFactorStructureStatement|medium|reductionGroups;reductionVectors;reducedIntegrand;LocalSupportedVectors|Check the eight disjoint token groups, with one or two tokens per group. Each factor is a dot product, each token occurs once, and every used token belongs to the declared union.
PeripheralGeometryStatement|medium|PeripheralGeometry;deletedLeafSites;patternDegree;leafNeighbour|Enumerate the template and the two representation rules. Deleted sites are peripheral, have degree zero or one, are mutually nonadjacent, and every degree-one neighbour survives.
PeripheralFubiniStatement|hard|PeripheralGeometry;separatedLeafFunctional;integratedLeafFactor;retainedOriginalFactors|Use the retained/deleted disjoint union to reindex spin assignments. Each deleted spin appears in only its own slots and possible single bond; factor its sum into integratedLeafFactor. This leaf has no replacement-vector choices.
PeripheralAssignmentStatement|hard|LeafRule;PeripheralGeometry;separatedLeafFunctional;reducedIntegrand|Choose the isolated positive factor or one-bond normalizer and vector at each deleted site. Use atom norms for every surviving spin argument. Multiply normalizers once, fill unused tokens with zero, and compare evaluated retained factors for both next values.
BallChordStatement|easy|UnitChord;normSq;UnitVector|For nonzero v use its Euclidean normalization and its negative with weights (1+norm v)/2 and (1-norm v)/2. At v=0 use an explicit coordinate unit vector. Prove the two weights lie in [0,1].
AffineEvaluationStatement|medium|SeparatelyAffine;VectorAffine;evaluateReduced;Function.update|Expand monomials. The total degree in one vector is at most one, so its contribution is constant or exactly one coordinate. Distribute the update convex combination and sum.
ProductBallNonnegativeStatement|medium|UnitChord;SeparatelyAffine;Finset.univ|Induct over a finite set of ball coordinates to replace each by its two supplied unit endpoints. Separate affineness preserves nonnegativity with nonnegative weights, including zero endpoint weights.
DifferenceStructureStatement|medium|VectorAffine;OrthogonalInvariant;SupportedVectors;MvPolynomial.C|Support of subtraction is contained in the union, and multiplication by a scalar constant introduces no exponents. Evaluation is a ring hom, so covariance is stable under the same scalar combination.
BlochAlgebraStatement|easy|blochMatrix;pauli;normSq|Expand the explicit 2 by 2 matrices, cancel cross terms using I squared = -1, and verify conjugate transpose, square and trace entrywise.
BlochPositivityStatement|medium|Matrix.IsHermitian;Matrix.PosSemidef;Matrix.IsHermitian.eigenvectorBasis|Diagonalize A. The square equation forces each real eigenvalue squared to equal r, hence its magnitude is at most one. The affine density eigenvalues are nonnegative. Avoid division and handle r=0 directly.
PauliExpansionStatement|medium|pauliExponent;pauliCoordinate;VectorAffine;SupportedVectors|Construct the bijection between supported vector-affine monomials and J-to-Fin4 assignments. A zero exponent gives label 0; the unique selected coordinate gives label k+1. Evaluate the monomial expansion.
PauliProductTraceStatement|medium|pauliOperator;productDensity;pauliCoordinate;pauliExponent|Expand trace, matrix multiplication and the Pauli sum. Factor the sum over tensor coordinates into a product of one-slot traces, apply the supplied single-Pauli equation, and combine real casts.
InversionPolynomialStatement|medium|invertPolynomial;invertVectors;VectorAffine;SupportedVectors|Compute sign substitution on monomials. It multiplies coefficients by signs without changing exponents. Evaluation at inverted vectors cancels each sign, including tokens outside J.
ProductDensityPositiveStatement|hard|productDensity;spinDensity;Matrix.PosSemidef.kronecker|Induct over the finite token set, use PSD of a Kronecker product, and transport across the splitting equivalence for function-space indices. The empty token set has a one-dimensional tensor and density 1.
TraceProductPositiveStatement|medium|Matrix.PosSemidef;Matrix.trace;Matrix.PosSemidef.conjTranspose_mul_mul_same|Use a PSD square-root or spectral factorization A=R*R-adjoint. Cyclicity turns trace(AB) into the trace of R-adjoint*B*R, a PSD matrix. Apply trace nonnegativity and take its real part.
PauliHermitianStatement|easy|pauliOperator;pauli;Matrix.IsHermitian|Conjugate and transpose an entry. Each one-slot Pauli factor is Hermitian and rational coefficients are real; conjugation distributes over finite products and sums.
ReflectionParityStatement|hard|OrthogonalInvariant;reflectY;pauliYCount;pauliExponent|Specialize covariance to the explicit Y reflection. Equality of real polynomial functions implies coefficient equality. A Pauli exponent with an odd count of coordinate-1 factors changes sign, forcing its rational coefficient to vanish.
PauliRealityStatement|medium|pauliYCount;pauliOperator;pauli|Conjugation fixes factors 0,1,3 and negates factor 2. An even product is fixed; the coefficient premise removes odd products. Sum and read off zero imaginary parts.
InversionCovarianceStatement|easy|OrthogonalInvariant;invertPolynomial;invertVectors|Prove eval of sign substitution is evaluation at invertVectors. Matrix.mulVec is real linear, so negation commutes with every rotation, yielding covariance after inversion.
AdjointPauliCoordinatesStatement|medium|pauli;Matrix.conjTranspose;Matrix.trace|Conjugation by a unitary preserves Hermitian and traceless matrices. Expand an arbitrary traceless Hermitian 2 by 2 matrix as a real linear combination of the three Pauli matrices, using its entries or half-trace coordinates.
AdjointPauliOrthogonalStatement|medium|pauli;Matrix.trace;Matrix.conjTranspose|Conjugation preserves the half-trace pairing. Insert the supplied Pauli coordinates, use pairwise trace orthogonality, and compare real entries to obtain R-transpose*R=1.
PauliRotationTransferStatement|hard|pauliOperator;tensorPowerMatrix;OrthogonalInvariant;pauliExponent|Expand tensor conjugation with the supplied rotation coordinates. Match polynomial coefficients for the transpose rotation and use covariance. Tensor unitarity cancels the conjugate transpose to give Commute.
CayleyTensorCommutationStatement|medium|tensorPowerMatrix;pauli;Real.sqrt|Show (I-it sigma_j)/sqrt(1+t squared) is unitary of determinant one. Its denominator is strictly positive. Expand the tensor scale as a scalar power and cancel it from commutation.
TensorLinearCoefficientStatement|hard|tensorPowerMatrix;tokenMatrix;Polynomial.coeff|Construct the one-variable matrix polynomials on both sides. Equality at every real t implies coefficient equality over C. In degree one, exactly one token contributes A, giving the token sum, also for J empty.
SpinGeneratorTransferStatement|easy|totalSpinZ;totalSpinPlus;totalSpinMinus;tokenMatrix;Matrix.toEuclideanLin|Use linearity of tokenMatrix to cancel the nonzero scalar -i. Take scalar linear combinations of commuting sums, and transport matrix multiplication to linear-map composition.
MomentPauliInterchangeStatement|hard|MonomialMoments;InternalAdmissible;contractSpins;specializeInternal;rawPauliFunctional|For one input monomial, external exponent selection and inversion signs are fixed. Factor its finite spin sum into exact local moments, then distribute over the polynomial support and matrix entries.
PairExpansionFromRealizationStatement|hard|rawPauliFunctional;realPauliOperator;PairExpansion;GroupInversion|In each real Pauli summand pull out the retained corner's two equal-sign factors. The other factors use disjoint tokens and commute with pair symmetries. Remove zero-weight U atoms, enumerate finite sums by Fin t, and join current and next with the difference coefficient.
UnitPairSupportStatement|medium|pairTerm;symmetricPairProjection;blochMatrix;tokenMatrix|For unit n and eta squared = 1, the 2 by 2 factor is twice a rank-one projection. Its equal tensor square has symmetric range and is fixed by the pair projection on both sides. Reindex the two distinct slots first.
EqualPairExchangeStatement|medium|pairTerm;exchangeOperator;tokenMatrix|Expand matrix entries under Equiv.swap. Swapping two equal one-slot factors leaves their tensor product unchanged. This holds for zero n and coincident j,k as well.
PairExpansionTransferStatement|easy|PairExpansion;Commute;symmetricPairProjection|Distribute multiplication through the finite sum. Local left/right support and auxiliary-factor commutation imply support of each summand; exchange commutation is closed under products, scalar multiples and sums.
SectorSpinStableStatement|hard|SpinStable;exchangeBasisVector;GroupBasis;totalSpinPlus;totalSpinMinus|Check single and pair ladder actions on the four displayed unnormalized pair vectors, then expand the sum of local actions on a tensor basis vector. Extend from generators to exchangeSpace by span induction. Physlib provides optional local sl2 tensor algebra only.
SectorWeightBasisStatement|medium|sectorVector;exchangeWeight;centralWeight;exchangeBasisVector|Compute diagonal token action on each integer tensor basis vector. Pair contributions have integral weights. Count single half-integers and use parity to give the explicit integer offset from centralWeight.
SpanWeightLatticeStatement|medium|Submodule.span;Module.End.eigenspace;Module.End.eigenspace|Group the finite spanning family by equal weights. Distinct eigenspaces are independent, so a nonzero eigenvector in their sum has one of those weights. Normalization and independence of the original spanning family are unnecessary.
SpinAdjointStatement|easy|totalSpinZ;totalSpinPlus;totalSpinMinus;tokenMatrix|Compute the adjoints of the explicit single-spin matrices, lift them to each token, and sum. Transport to the inherited Euclidean inner product.
SpinCommutatorStatement|medium|totalSpinZ;totalSpinPlus;totalSpinMinus;tokenMatrix|Verify the three single-token commutators directly. Terms on distinct tokens commute and cancel in the double sums; collect the same-token terms.
WeightLadderTransferStatement|medium|WeightLadder;inner;norm;totalSpinZ|Use the supplied adjoint and commutator identities to derive shifted weights and the norm-square difference 2m times norm-square v. Nonzero v makes its squared norm positive; the required ladder cannot vanish for the indicated sign.
CommonWeightEigenvectorStatement|hard|eigenvaluesOn;Module.End.eigenspace;Submodule;IsSymmetric|Restrict Z to the intersection of S with the nonzero O eigenspace. Commutation gives invariance and the inherited inner product gives self-adjointness. Apply the finite-dimensional spectral theorem to obtain a nonzero real-weight eigenvector.
LadderWalkStatement|hard|SpinStable;WeightLadder;Module.End;Int|Induct separately on positive and negative integer offsets m-kappa. Repeated lowering or raising stays in S, preserves the O eigenvalue, and is nonzero at every step. Use integer arithmetic; convert to natural iteration counts only after selecting the sign.
PositiveSpectrumStatement|hard|PositiveOn;eigenvaluesOn;Submodule;IsSymmetric|Restrict O to S with the inherited Hilbert structure. Use its orthonormal eigenbasis to identify strict quadratic positivity with strictly positive real eigenvalues. Transport subspace eigenvectors to the ambient definition.
H1FiniteDataStatementV2|hard|SectorWitnesses;GroupInversion;ClearsDenominator;h1Numerator;h1Denominator|EXTERNAL HANDOFF: supply complete covered-pattern and orbit coverage, exact representations/inversions/denominators, and all integer Gram factors. Prove regeneration/checker soundness and kernel-check independent data shards. The soundness Top statements do not imply this existence contract.
'''.strip().splitlines()
meta={}
for row in rows:
 name,diff,deps,route=row.split('|')
 meta[name]={'difficulty':diff,'dependencies':deps.split(';'),'suggested_proof_route':route}
proved={'ActiveStatusesStatement':'activeStatuses','PassageSubtractionStatement':'passageSubtraction','DifferenceEvaluationStatement':'differenceEvaluation','SinglePauliTraceStatement':'singlePauliTrace','InversionBallStatement':'inversionBall','PairTokensDistinctStatement':'pairTokensDistinct','CentralWeightHalfStatement':'centralWeightHalf'}
derived={'ReducedStructureStatement':'reducedStructure_of_nodes','SimultaneousLeafReconstructionStatement':'simultaneousLeafReconstruction_of_nodes','RetainedPairExpansionStatement':'retainedPairExpansion_of_nodes','ThresholdSymmetryStatement':'thresholdSymmetry_of_integerCheck'}
labels={'NodesPassage':'l:Iw','NodesLeaf':'l:leaf','NodesReduction':'c:reduce','NodesPauli':'l:inversion','NodesStructure':'l:Ostruct','NodesSector':'l:sector','NodesCertificate':'t:H1 / p:certificate'}
lib={
'NodesPassage':['Mathlib/Algebra/MvPolynomial/Eval.lean','Mathlib/Data/Fintype/BigOperators.lean'],
'NodesLeaf':['Mathlib/Data/Fintype/BigOperators.lean','Mathlib/Analysis/InnerProductSpace/Basic.lean'],
'NodesReduction':['Mathlib/Algebra/MvPolynomial/Eval.lean','Mathlib/Data/Fintype/BigOperators.lean'],
'NodesPauli':['Mathlib/Analysis/Matrix/PosDef.lean','Mathlib/Analysis/Matrix/Order.lean'],
'NodesStructure':['Mathlib/LinearAlgebra/Matrix/ToLin.lean','Mathlib/Algebra/MvPolynomial/Eval.lean'],
'NodesSector':['Mathlib/LinearAlgebra/Eigenspace/Basic.lean','Mathlib/Analysis/InnerProductSpace/Spectrum.lean'],
'NodesCertificate':['AKLT.Gen.Gram.int_gram_residual_posDef','AKLT/Gen/Gram/Checker.lean']}
basechecks={
 'premises':'All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.',
 'vacuity_and_degenerate':'Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.',
 'coercions':'Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.',
 'finite_sums':'Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.',
 'nat_subtraction':'No unguarded natural subtraction in this statement.',
 'division_by_zero':'Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.',
 'instances':'No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.'}
checks={
'PassageFubiniStatement':{'premises':'Coveredness, exact neighbour set equality and all three distinctness conditions are explicit. Removed-site vectors are zero, never additional spin variables.'},
'PassageNetworkPositiveStatement':{'premises':'The supplied generic network result includes Valid; the proof must build a valid erased network retaining every original slot.', 'vacuity_and_degenerate':'The template has a passage site, but its erased network can have isolated sites; finite-network input covers n=0 as well.'},
'PassageNextLowerBoundStatement':{'premises':'Unit norms of the concrete atoms are explicit; zero-weight atoms are allowed. Dot-product lower bounds are needed only where the spin weights are nonzero.'},
'MomentContractionStatement':{'premises':'Both absent-spin support and separate degree <=4 are mandatory. rationalMoment is not exact for arbitrary higher-degree monomials.'},
'MomentCovarianceTransferStatement':{'premises':'Uses the supplied degree-four polynomial covariance, support, status and integrand invariance; does not rotate the finite atom set as a set.'},
'CoveredSlotEnumerationStatement':{'premises':'Nonremovedness is required for corners. All tips are U by Covered. Both corner slots are retained regardless of kept external half-bonds.'},
'CornerMeanBoundsStatement':{'division_by_zero':'Normalizer positivity is part of the conclusion and must be established before any division in localMean is cleared.'},
'NormalizedMeanFactorStatement':{'division_by_zero':'A=siteFunctional s(localProduct a)>0 and rho>0 are explicit premises. The zero-mean case gives u=0 and causes no division by its norm.'},
'PeripheralGeometryStatement':{'premises':'Requires Covered and both exact deletion rules; degree and neighbour statements refer to the original current internal bonds.'},
'PeripheralFubiniStatement':{'premises':'Requires PeripheralGeometry. Deleted spins are mutually nonadjacent; next changes no deleted leaf law or bond, since none is a passage neighbour.'},
'PeripheralAssignmentStatement':{'premises':'Concrete atom unit norms, LeafRule and PeripheralGeometry are explicit. A single choice of K and u precedes the next quantifier.', 'vacuity_and_degenerate':'If no leaf is deleted, K=1. Isolated leaves supply a positive factor; unused tokens are zero.'},
'BallChordStatement':{'division_by_zero':'Branch on v=0. Only the nonzero branch divides by norm v; the zero branch uses an explicit unit coordinate vector.'},
'ProductBallNonnegativeStatement':{'vacuity_and_degenerate':'Zero convex weights are valid. The ambient 20-token function also represents constants and polynomials with no used tokens.'},
'BlochPositivityStatement':{'vacuity_and_degenerate':'r=0 is included; no invertibility or nonzero A is assumed.', 'division_by_zero':'The eigenvalue-square argument uses no division by r or sqrt r.'},
'PauliExpansionStatement':{'premises':'VectorAffine bounds the sum of the three coordinate exponents per token; scalar-coordinate multiaffineness would be insufficient. SupportedVectors excludes unrepresented tokens.', 'nat_subtraction':'pauliCoordinate uses a.val-1 only under a.val != 0; the Fin 4 bound proves this index is <3.', 'vacuity_and_degenerate':'For J empty the function type J->Fin4 is a singleton, yielding the constant term.'},
'ProductDensityPositiveStatement':{'vacuity_and_degenerate':'For J empty there is one tensor basis function, not zero basis functions; the resulting matrix is [1].'},
'TraceProductPositiveStatement':{'premises':'Both factors are PSD; no commutation or positive-definiteness premise is assumed.', 'instances':'The arbitrary index type explicitly binds [Fintype n] and [DecidableEq n]; the conclusion uses those instances.'},
'AdjointPauliOrthogonalStatement':{'premises':'The Pauli-coordinate equation and g-adjoint*g=1 are explicit. Square finite dimension supplies g*g-adjoint=1 when needed.'},
'CayleyTensorCommutationStatement':{'division_by_zero':'sqrt(1+t squared)>0 for all real t; its finite tensor scalar power is nonzero, including exponent zero.'},
'TensorLinearCoefficientStatement':{'vacuity_and_degenerate':'For J empty the tensor polynomial is constant and its linear coefficient and token sum are both zero.'},
'MomentPauliInterchangeStatement':{'premises':'Requires exact monomial moments, U/D statuses on V, internal support and degree four. External affineness is unnecessary because both sides select the same Pauli exponents.'},
'PairExpansionFromRealizationStatement':{'premises':'GroupInversion forces equal signs on the two retained slots. Unit atom norms are explicit; zero-weight U atoms must be omitted.', 'vacuity_and_degenerate':'The finite expansion may be empty only for the zero operator; D allows n=0.'},
'UnitPairSupportStatement':{'premises':'j != k, normSq n=1 and eta squared=1 are explicit. Rank-one support would be false for a zero Bloch vector.'},
'EqualPairExchangeStatement':{'vacuity_and_degenerate':'n=0 and even j=k are included: equal-factor exchange still commutes.'},
'PairExpansionTransferStatement':{'premises':'The remainder commutes with both exchange and the projection as explicit parts of PairExpansion. No positivity of complex coefficients is assumed.'},
'SectorSpinStableStatement':{'premises':'No Covered assumption is needed: coordinate groups are always disjoint. Unused signs may repeat the same subspace; this does not claim an orthogonal sum over all signs.'},
'SectorWeightBasisStatement':{'coercions':'exchangeWeight and centralWeight are rational; the Z eigenvalue is complex and the integer-offset equality is real. The central half depends on the number of single groups.'},
'SpanWeightLatticeStatement':{'vacuity_and_degenerate':'For an empty spanning family the span is zero, so the nonzero eigenvector premise is impossible. No linear independence is assumed.', 'instances':'The arbitrary basis-index type explicitly binds [Fintype beta].'},
'CommonWeightEigenvectorStatement':{'premises':'O and Z preserve S; both restricted symmetry conditions and O/Z commutation on S are explicit. The O eigenspace is nonzero by eigenvaluesOn membership.'},
'LadderWalkStatement':{'premises':'kappa is exactly 0 or 1/2, spin stability and nonvanishing/shift facts are explicit. O commutes with both ladders on S. No multiplicity claim is made.', 'nat_subtraction':'Distances are integer offsets. Split the sign before converting a distance to Nat; never truncate m-kappa as a natural subtraction.'},
'PositiveSpectrumStatement':{'vacuity_and_degenerate':'S=0 makes PositiveOn and the universal eigenvalue condition both vacuously true.', 'premises':'Restriction invariance and symmetry on S are explicit; the inherited inner product is used, not the unnormalized coordinate dot product.'},
'H1FiniteDataStatementV2':{'premises':'This is an EXTERNAL finite-data existence obligation, not a derived fact. It includes GroupInversion, ClearsDenominator and every sector witness at the selected threshold.', 'division_by_zero':'h1Denominator is 1000 or 200; ClearsDenominator includes D0>0. GramResidualRows includes g,d,S>0.', 'vacuity_and_degenerate':'Repeated unused exchange signs are permitted. Empty central matrices use Fin 0 and still require positive scales.'}}
allnodes=[]; leaves=[]; decl=[]
for f in sorted(folder.glob('Nodes*.lean')):
 text=f.read_text()
 for match in re.finditer(r'^def (\w*Statement\w*) : Prop',text,re.M):
  name=match.group(1);start=match.start();end=text.find('\n\n',start)
  if end<0:end=len(text)
  body=text[start:end]
  before=text[:start];doc=before[before.rfind('/--'):].strip();doc=doc.removeprefix('/--').removesuffix('-/').strip()
  label=labels[f.stem]
  if name in ['MomentContractionStatement','MomentCovarianceTransferStatement','ContractionAffineStatement','ContractionSupportStatement']:label='l:moments / l:Iw / c:reduce'
  if name=='ThresholdSymmetryStatement':label='l:integercheck'
  status='proved' if name in proved else 'assembled' if name in derived else 'package' if name=='CertificateStatementV2' else 'external input' if name=='H1FiniteDataStatementV2' else 'open'
  diff='easy' if status in ['proved','package'] else 'assembly' if status=='assembled' else meta[name]['difficulty']
  node={'lean_name':'AKLT.Blueprint.H1.'+name,'module':'AKLT.Blueprint.H1.'+f.stem,'paper_label':label,'difficulty':diff,'status':status,'file':str(f),'line':text[:start].count('\n')+1}
  allnodes.append(node);decl.append((name,body))
  if name in meta:
   item={**node,**meta[name]};item.pop('status');item['paper_reference']={'file':'/home/ubuntu/aklt/reports/REV_C3/app-local-operator.tex','docstring':doc}
   item['closed_statement']=body
   item['proof_policy']={
    'status':'open',
    'first_attempt_required_from':'a different, cheaper model than the blueprint architect',
    'blueprint_architect_may_prove':False,
    'applies_to_checker_soundness':True,
    'proof_attempts_by_architect_after_rule_update':0}
   item['dependencies']=['AKLT.Blueprint.H1.'+d if d in ['MonomialMoments','ProductMomentCovariance','InternalAdmissible','IntegrandInvariant','LocalVectorAffine','LocalSupportedVectors','OrthogonalInvariant','LocalPolynomial','VectorPolynomial','rawFunctional','localEvaluation','originalIntegrand','nextStatus','PassageNeighbours','passageI','passageJ','LeafRule','PeripheralGeometry','deletedLeafSites','separatedLeafFunctional','integratedLeafFactor','retainedOriginalFactors','UnitChord','SeparatelyAffine','blochMatrix','pauliCoordinate','pauliYCount','reflectY','pairTerm','PairExpansion','realPauliOperator','specializeInternal','rawPauliFunctional','sectorVector','SpinStable','WeightLadder','SectorWitnesses','h1Numerator','h1Denominator'] else 'AKLT.Defs.'+d if not d.startswith(('Mathlib','Matrix.','Module.','MvPolynomial.','Finset.','Function.','Submodule.','Polynomial.')) and d not in ['inner','norm','Int','UnitVector'] else d for d in item['dependencies']]
   item['dependencies']=[d.replace('AKLT.Defs.IsSymmetric','IsSymmetric').replace('AKLT.Defs.Commute','Commute').replace('AKLT.Defs.UnitVector','AKLT.Defs.UnitVector') for d in item['dependencies']]
   item['dependencies']+=lib[f.stem]
   item['trap_check']={**basechecks,**checks.get(name,{})}
   item['ownership']='external certificate-data owner; interface gap' if name=='H1FiniteDataStatementV2' else 'H1 proof writer'
   item['estimated_proof_lines']=None if name=='H1FiniteDataStatementV2' else {'easy':[15,100],'medium':[60,240],'hard':[150,380]}[item['difficulty']]
   item['reuse_pointers']=lib[f.stem].copy()
   if name in ['SectorSpinStableStatement','SectorWeightBasisStatement','SpinCommutatorStatement']:
    item['reuse_pointers']+=['AKLT/Vendor/Physlib/Mathematics/RepresentationTheory/Sl2/TensorDecomposition.lean: Physlib.Sl2.tensorStringBasis and cgEquiv_tensorH/E/F; bridge to these exact coordinates is still required.']
   if name in ['CommonWeightEigenvectorStatement','PositiveSpectrumStatement']:
    item['reuse_pointers']+=['AKLT/Vendor/QICLean/Analysis/EuclideanEigenvectorBasis.lean: AKLT.Vendor.QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis']
   if name=='H1FiniteDataStatementV2':item['reuse_pointers']+=['REV-PLAN/PLAN.md lines 2296-2323: 12173 external sector blocks; full factor export remains required.','AKLT.Gen.Gram.checker_sound_complex (generic checker only; does not supply data).']
   leaves.append(item)
assert set(meta)=={x['lean_name'].split('.')[-1] for x in leaves},set(meta)-{x['lean_name'].split('.')[-1] for x in leaves}
(out/'leaves.json').write_text(json.dumps(leaves,indent=2)+'\n')
(out/'nodes.json').write_text(json.dumps(allnodes,indent=2)+'\n')
# The complete human-readable declaration catalog includes all exact node bodies,
# all assembly signatures, and the auxiliary immediate proof signatures.
exports=['# H1 declaration catalog','','Namespace: `AKLT.Blueprint.H1`. Imports and open scopes are in the source files.','']
for name,body in decl:exports+=['```lean',body,'```','']
ths=[]
for f in sorted(folder.glob('*.lean')):
 if f.stem=='Audit':continue
 text=f.read_text()
 for m in re.finditer(r'^theorem (\w+)',text,re.M):
  e=text.index(':= by',m.start());sig=text[m.start():e].rstrip();name=m.group(1)
  ths.append((name,sig,str(f),text[:m.start()].count('\n')+1))
  exports+=['```lean',sig,'```','']
(out/'declarations.md').write_text('\n'.join(exports))
traps=['# Per-node trap audit','','All 67 statement definitions are checked as closed `Prop`s in `AKLT.Blueprint.H1.Audit`.',
'Every open node has the seven detailed trap categories in `leaves.json`; this file also records immediate and assembled nodes.','']
for node in allnodes:
 name=node['lean_name'].split('.')[-1];traps+=['## '+name,'',f"Status: {node['status']}. Paper: `{node['paper_label']}`.",'']
 ck={**basechecks,**checks.get(name,{})}
 if name in proved:ck['premises']='Kernel-checked theorem `'+proved[name]+'` proves this closed node; see axioms.txt.'
 if name in derived:ck['premises']='Kernel-checked implication `'+derived[name]+'` assembles this intermediate from closed inputs. It is not another independent open obligation.'
 if name=='CertificateStatementV2':ck['premises']='A definition packaging soundness AND finite data coverage. No theorem asserts either conjunct without its explicit input.'
 if name=='PairTokensDistinctStatement':ck['nat_subtraction']='No subtraction: groupLeader<=17 and groupSecond=min 19 (leader+1); omega proves equality is impossible, so the min does not identify slots.'
 if name=='InversionBallStatement':ck['vacuity_and_degenerate']='Negation preserves normSq even at zero; membership in I is split explicitly.'
 for k,v in ck.items():traps+=['- **'+k+'**: '+v]
 traps+=['']
(out/'trap-check.md').write_text('\n'.join(traps))
(out/'catalog-state.json').write_text(json.dumps({'open_count':len(leaves),'all_count':len(allnodes),'proved':proved,'derived':derived,'theorems':ths},indent=2)+'\n')
print(f'{len(allnodes)} nodes; {len(leaves)} open ({len(leaves)-1} mathematical leaves + 1 external data handoff); {len(ths)} theorems')
