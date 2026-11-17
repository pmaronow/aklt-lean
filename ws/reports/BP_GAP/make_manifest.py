import json,re,pathlib
base=pathlib.Path('/home/ubuntu/aklt/wt/BP_GAP')
root=base/'AKLT/Blueprint/Gap'
report=pathlib.Path('/home/ubuntu/aklt/reports/BP_GAP')
proved={
 'GroundOrthogonalityStatement':'groundOrthogonality', 'RayleighBoundStatement':'rayleighBound',
 'PositiveToProbabilityStatement':'positiveToProbability', 'IndependentPairsStatement':'independentPairsProbability',
 'DiagonalCouplingStatement':'diagonalCoupling', 'DeltaBoundsStatement':'deltaBounds',
 'PowerCountStatement':'powerCount', 'PoincareMonotoneStatement':'poincareMonotone',
 'PeriodicBudgetStatement':'periodicBudget'}
assembled={'ReversibleSpectralStatement','StoppedCouplingStatement','HammingAtScaleStatement',
 'FiniteContractionStatement','BlockComparisonStatement','PeriodicCriterionStatement'}
hard={'ConditionalPatchCouplingStatement','ProductTensorizationStatement','ReversibleEigenvalueGapStatement',
 'ShellRowStatement','BoxGaugeLawStatement','BoxCoordinatesStatement'}
easy={'CommonMinorizationStatement','HammingLocalizationStatement','MultiplicityEstimateStatement',
 'TraceDisagreementStatement','TrialCountStatement','HammingBudgetStatement','BlockVolumeBoundStatement',
 'PullbackColourStatement','ThresholdSpacingStatement','FrameInteractionBoundsStatement',
 'NormalizedInteractionStatement','FarBoundaryEqualityStatement'}
notes={
'FibreNormalizationStatement':'The full-state fibre law has zero atoms outside its fibre and is only Probability; the restricted block law is PositiveProbability. Its denominator contains the given input configuration with positive mass.',
'ConditionalProjectionStatement':'Use complex conjugation in self-adjointness. Constants, means, and the two endpoint blocks are included; no real-only scalar-product convention is substituted.',
'ConditionalVarianceStatement':'conditionalVariance is pointwise E_U|f-E_Uf|², whereas blockDirichlet is its integrated form. The equality of these finite sums is part of this leaf.',
'MaximalCouplingStatement':'Probability forces a nonempty state space even without a separate Nonempty instance. Overlap 0 and 1 are included; branch at overlap=1 before residual division.',
'CouplingMarginalTVStatement':'The disagreement lower bound holds for every coupling, and marginalization is by an arbitrary deterministic map. Neither statement asserts Hamming contraction from TV.',
'MarginalCompletionStatement':'Zero marginal fibres are never sampled. Choose arbitrary residual laws only on zero fibres, after deriving that the full state space is nonempty from normalization.',
'HammingLocalizationStatement':'The same full-law coupling is used on both sides. Empty Q and Q=univ, and a zero-site product, satisfy the pointwise inequality.',
'CommonMinorizationStatement':'The common law is an actual probability, and 0≤t≤1 is explicit. The endpoints t=0 and t=1 require no normalized residual law.',
'SurgeryPreservationStatement':'The selected coupling may depend on both input configurations. Its first row marginal depends only on the first configuration, and its second only on the second.',
'ConditionalPatchCouplingStatement':'A and B are disjoint. Resample A after completing B and the remaining coordinates, conditioning separately on each full complement; then use the common prescribed A assignment. Empty A/B and t=0/1 are valid.',
'FrameProductReferenceStatement':'Only admissible frame letters are used. Every fixed boundary factor is absorbed into its incident site weight. The empty volume has Z=1 and the empty product reference.',
'FrameInteractionBoundsStatement':'Proper colouring supplies distinct frames on every internal edge; positive lower bounds justify multiplying inequalities. The edge set is counted once by internalBonds.',
'NormalizedInteractionStatement':'Z is explicitly positive and equal to the product-law expectation. lo and hi are positive. No division is performed at a zero site normalizer or zero Z.',
'SignedFrameBlockStatement':'The per-edge bounds cover both signs, h_x is strictly positive, and properness is required on each counted edge. Boundary factors do not enter the exponent. This covers arbitrary finite blocks and the empty product.',
'VariationalCenteringStatement':'An admissible h must be constant on each complement fibre. The constant centering bound and the conditional centering bound are separate quantified conclusions.',
'ProductTensorizationStatement':'Every site law is a positive normalized probability, and each alphabet is nonempty. Empty site sets give a one-point law, not an empty configuration type.',
'DensityComparisonStatement':'Both density constants are positive. The conclusion loses one ratio m/M; a second ratio is not introduced. The displayed reference is a normalized product law.',
'ConditionalBlockComparisonStatement':'Nested one-site conditioning inside a block must fix exactly the original complement of that site. Repeated labels contribute separately, including identical or empty blocks.',
'MultiplicityEstimateStatement':'t may be zero, as no division is used. Nonnegative one-site Dirichlet forms justify the multiplicity estimate; sums are over labels.',
'HammingPathStatement':'Insert zero into the finite edge-value set. This defines lipschitz=0 on singleton products, even if no Hamming-one pairs exist. Nonempty alphabets give a nonempty product.',
'LipschitzCouplingStatement':'Each kernel row is a probability; r≥0 is explicit. The singleton case has no neighbour pairs and zero Lipschitz seminorm.',
'LipschitzEigenvalueStatement':'A nonzero mean-zero real function is nonconstant because p sums to one. The eigenvalue bound uses the positive edge seminorm; constant eigenvectors are excluded by local premises.',
'ReversibleEigenvalueGapStatement':'Positive p makes diag(sqrt p) invertible. Restrict to mean-zero real functions before diagonalization, then split complex functions into real and imaginary parts. The zero-dimensional restriction is allowed.',
'BlockAverageFormStatement':'The label type is nonempty, so its cardinal denominator is positive. All sums count labels with multiplicity and preserve the rate-one convention.',
'ProductPoincareTransportStatement':'The same site and configuration equivalences transport the variance and every singleton conditional form. Site and alphabet instances are explicit, so the finite-product enumerations agree.',
'ProductCouplingTransportStatement':'Use the inverse of the same configuration bijection in both components. coordinate_eq proves exact equality of Hamming counts, not merely a bound.',
'ShellNestingStatement':'The floor error is at most one and s≥16 is explicit. Negative integer indices yield either the same inequality or an empty shell; no implicit Nat subtraction is used.',
'FiniteEnergyChainStatement':'Full support and nonempty alphabets make every prescribed partial conditioning event attainable. The exponent counts prescribed sites, not conditioning sites.',
'ShellRowStatement':'h≥4 and h≤s, geometric threshold, local separator facts, full support, consistency, energy, and all-boundary W are explicit. Skipped rows are identity; index h+1 receives no W success bound. Empty A/B/F and delta=1 are included.',
'TraceMarginalsStatement':'The initial pair law is the product of two normalized positive laws. A skipped row is a point mass; every other row has the two full conditional marginals. Pair dependence is unrestricted.',
'TrialCountStatement':'Fin h times correspond to shell indices 2 through h+1. Trials stop at h, and exclude both i and i+1 if exceptional. h≥4 controls h-3.',
'ShellAbsorptionStatement':'Only positive-mass traces are used. A trial includes an unskipped successor. Later supports preserve agreement on the whole earlier far set, not only on the current shell.',
'FiniteTrialFailureStatement':'No independence is assumed. Order the finite trial set and condition on the complete past. Empty trials give exponent zero; delta=0 or 1 is included without reciprocal 1-delta.',
'TraceDisagreementStatement':'The endpoint coupling is required to be precisely the pushforward of the trace law. The success implication is required on positive-mass paths; zero paths contribute nothing.',
'TerminalRadiusStatement':'This leaf takes the local stopped estimate, an assembled result, not another closed leaf as an assumption. s≥16 follows from the geometry threshold, so floor(s)≥4 and s-4>0. The zero-base real-power branch is explicit in the proof route.',
'ScaleExistenceStatement':'d>0 is explicit. The integer is chosen before colouring, translate, boundary, and torus periods. No finite-dimensional compactness or effective numerical cutoff is asserted.',
'BinomialTailStatement':'0<d≤1/2 makes d^20*n^20 positive and 1-d positive. n≥44 makes all twenty falling factors positive, with n-3 and n-22 interpreted correctly.',
'ScaleGeometryStatement':'All powers n^8 and n^2 in size conditions are natural powers. The spacing equalities are real equalities, using nonnegative square roots. n≥44 prevents a zero-scale corner case.',
'HammingCardinalityStatement':'The near region is counted inside the full square subtype; it is bounded by the entire integer sup-ball, regardless of placement or exterior seed. n≥1 controls both polynomial bounds.',
'HammingBudgetStatement':'The tail inequality is an explicit numerical input for this one n,d. Positive d and n≥44 justify all denominators. Each budget term is at most n^8/2000.',
'FarBoundaryEqualityStatement':'y is explicitly outside the nonempty square. Distance zero is impossible there, so distance≠1 really means beyond range one. The full laws, not just marginals, are equal.',
'StoppedHammingConversionStatement':'0≤d≤delta≤1 and n≥4 control both bases and natural exponents. The local stopped estimate supplies a full-law coupling and localization is applied to that same coupling.',
'ContainingBlockCountStatement':'M≥1 and L,N≥2M+3 imply injectivity of the inner offset square. Count centre labels, not distinct sets or measure symmetries.',
'ExteriorBlockCountStatement':'The halo includes corner offsets. At equality L=2M+3 its width is one full period and coordinate differences are still strictly smaller than that period.',
'BlockVolumeBoundStatement':'The target is the cardinality of Site L N (A=LN), not a normalized update rate. Its upper bound is obtained from an actual injection.',
'PeriodicNeighbourCouplingStatement':'The original one-site disagreement survives for non-containing blocks. Adjacent labels cost 1+K, far labels cost 1, and containing labels cost 0. Counts and K≥0 are explicit.',
'TorusColourStatement':'Size supplies periods at least three. The odd last-site branch is checked at both incident edges, including wrap edges of period three.',
'PullbackColourStatement':'Plane adjacency is unoriented; identify a positive torus bond or its reverse. Size excludes a plane unit edge reducing to a loop.',
'HaloInjectionStatement':'The expanded coordinate interval has width 2M+3; any two elements differ by at most 2M+2, strictly below each period. Equality in the period bound is allowed.',
'LiftBondStatement':'Separate internal bonds from crossing bonds. The halo injection rules out an exterior point reducing to an internal one. Unordered endpoint sets prevent orientation sign mistakes.',
'BoxCoordinatesStatement':'The parity sign is a function on the lifted integers only. Sitewise antipodal permutations preserve the actual finite alphabets. The same change works for both exterior fibres, with at most one changed lifted site.',
'BoxGaugeLawStatement':'The coordinate data, exact lifted bond data, proper colouring, and positive signed interactions are explicit. Exterior-only factors are nonzero before cancellation. No global odd-torus bipartition is assumed.',
'TorusRangeTransferStatement':'The input uses the original four torus neighbours, while the conclusion allows the larger physical sup-distance halo. Extra corner sites cause no interaction and do not invalidate the implication.',
'SquareInternalEdgesStatement':'internalBonds is an oriented-once Finset of pairs. The formula also holds at M=0; no unsigned subtraction is used in the edge count.',
'FrameSpecRegularityStatement':'Positivity and conditioning consistency for the actual finite boundary law are explicit local inputs. Range one is proved from the four-neighbour product, without adding a missing Top hypothesis.',
'FrameSpecEnergyStatement':'conditionalProbability takes the conditioning event first. J is fixed in that argument and U is the prescribed event; the exponent is U.card. Map subtype sites injectively into W before changing cardinalities.',
'FrameWindowTransferStatement':'Allowed i satisfy i≥2 and i≤s, so the actual window is contained in the far volume even before using the large-threshold shell export. Total-boundary extensions therefore do not affect its marginal.',
'ThresholdSpacingStatement':'geometryThreshold is at least 16^4 for every l, including l=0. Monotonicity of nonnegative square roots gives s≥16 and excludes u=0.'}
assert len(notes)==58,(len(notes),set(notes))
core=set()
for p in [root/'NodesMain.lean']:
 s=p.read_text()
 for b in ['FiniteAssemblyLeaves','ShellAssemblyLeaves','PeriodicAssemblyLeaves']:
  tail=s.split('def '+b+' : Prop :=',1)[1]
  body=re.split(r'\n\n',tail,1)[0]
  core.update(re.findall(r'\b\w+Statement\b',body))

def group(n):
 if n in ['ProductPoincareTransportStatement','ProductCouplingTransportStatement']:return 'transport'
 if n in ['ConditionalProjectionStatement','FibreNormalizationStatement','ConditionalVarianceStatement','VariationalCenteringStatement','SurgeryPreservationStatement','ConditionalBlockComparisonStatement','BlockAverageFormStatement']:return 'fibre'
 if any(x in n for x in ['Lipschitz','Reversible','HammingPath']):return 'spectral'
 if n in ['MaximalCouplingStatement','CouplingMarginalTVStatement','MarginalCompletionStatement','CommonMinorizationStatement','HammingLocalizationStatement','ConditionalPatchCouplingStatement']:return 'coupling'
 if any(x in n for x in ['Density','ProductTensorization','FrameProductReference','FrameInteractionBounds','NormalizedInteraction','SignedFrameBlock']):return 'density'
 if n in ['BinomialTailStatement','ScaleExistenceStatement','ScaleGeometryStatement','HammingBudgetStatement','ThresholdSpacingStatement']:return 'arithmetic'
 if any(x in n for x in ['Colour','Injection','Bond','Box','InternalEdges','Count','VolumeBound','RangeTransfer','FrameSpec','FrameWindow']):return 'geometry'
 return 'shell'
deps={
'fibre':['AKLT.Defs.conditionalExpectation','AKLT.Defs.conditionalVariance','AKLT.Defs.blockDirichlet','AKLT.Blueprint.Gap.fibre','AKLT.Blueprint.Gap.blockLaw','Finset.sum_comm','Finset.sum_equiv','AKLT.Vendor.FiniteConditioning.condExp_on_fiber','AKLT.Vendor.FiniteConditioning.condExp_eq_of_fiber_integrals'],
'coupling':['AKLT.Defs.Coupling','AKLT.Defs.totalVariation','AKLT.Defs.marginal','AKLT.Defs.eventMass','AKLT.Blueprint.Gap.disagreement','AKLT.Blueprint.Gap.couplingCost','Finset.sum_comm','AKLT.Vendor.FiniteChain.finiteTotalVariation_contraction','AKLT.Vendor.FiniteChain.finiteTotalVariation_le_one'],
'density':['AKLT.Defs.normalize','AKLT.Defs.PoincareLower','AKLT.Defs.dirichlet','AKLT.Defs.variance','AKLT.Blueprint.Gap.planeInteraction','Finset.prod_le_prod','AKLT.Vendor.FiniteChain.Cheeger.weightedVariance_le_center'],
'spectral':['AKLT.Blueprint.Gap.lipschitz','AKLT.Blueprint.Gap.Reversible','AKLT.Blueprint.Gap.kernelMean','AKLT.Blueprint.Gap.kernelForm','AKLT.Vendor.QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis','AKLT.Vendor.QICLean.OrthonormalBasis.re_inner_apply_eq_sum_of_eigen','AKLT.Vendor.QICLean.Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap'],
'geometry':['AKLT.Defs.square','AKLT.Defs.internalBonds','AKLT.Defs.planeLaw','AKLT.Defs.conditionalTorusLaw','AKLT.Blueprint.Gap.reduction','AKLT.Blueprint.Gap.torusSquare','AKLT.Blueprint.Gap.torusHalo','AKLT.Blueprint.Gap.BoxCoordinates','AKLT.Blueprint.Gap.frameSpec','Finset.card_image_of_injective','ZMod.intCast_zmod_eq_zero_iff_dvd'],
'arithmetic':['AKLT.Defs.shellSpacing','AKLT.Defs.geometryThreshold','AKLT.Blueprint.Gap.ScaleConditions','add_pow','Nat.choose','Nat.factorial','Real.sqrt_sq','Real.sq_sqrt','pow_le_pow_of_le_one'],
'shell':['AKLT.Blueprint.Gap.PlaneSpec','AKLT.Blueprint.Gap.RegularSpec','AKLT.Blueprint.Gap.SpecEnergy','AKLT.Blueprint.Gap.SpecWindow','AKLT.Blueprint.Gap.RowConditions','AKLT.Blueprint.Gap.SurgeryKernels','AKLT.Blueprint.Gap.traceLaw','AKLT.Blueprint.Gap.trialTimes','AKLT.Blueprint.Gap.StoppedEstimate','AKLT.Defs.farVolume','AKLT.Defs.shell','AKLT.Defs.exceptionalIndices','Int.floor_le','Int.lt_floor_add_one'],
 'transport':['AKLT.Blueprint.Gap.ProductChange','AKLT.Blueprint.Gap.Carries','AKLT.Defs.hamming','AKLT.Defs.PoincareLower','AKLT.Defs.Coupling','Finset.sum_equiv','Fintype.sum_equiv']}
reuse={
'fibre':['AKLT/Vendor/FiniteConditioning/P015/P015_FiniteConditioning.lean (fibre identification; a finite/complex bridge remains)','/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:77-82'],
'coupling':['AKLT/Vendor/FiniteChain/FiniteChainMixing.lean (half-L1 only; no donated maximal/Hamming coupling theorem)','/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:78-79'],
'density':['AKLT/Vendor/FiniteChain/FiniteChainCheeger.lean (variational centering ingredient only)','/home/ubuntu/aklt/reports/REV_A2/app-finite.tex:163-251'],
'spectral':['AKLT/Vendor/QICLean/Analysis/EuclideanEigenvectorBasis.lean','AKLT/Vendor/QICLean/Analysis/KernelSpectralGap.lean','/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:82 (weighted conjugation, Lipschitz and singleton bridges are new)'],
'geometry':['/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:339-489','/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md:664-689,863-901 (l:colour and l:boxlift are internal, without Top exports)','No audited whole-result donor; use finite interval, ZMod and Finset primitives'],
'arithmetic':['/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:248-310','Mathlib finite binomial, floor and real square-root lemmas; no numerical certificate or asymptotic mixing donor'],
'shell':['/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:73-226','/home/ubuntu/aklt/reports/REV_A2/app-finite.tex:68-161','No audited whole-result donor; use finite sums, conditional laws and finite induction'],
'transport':['/home/ubuntu/aklt/reports/REV_A2/sec4-periodic-gap.tex:451-489','Mathlib Equiv/Finset/Fintype change of variables; no whole-result donor']}
allnodes=[]
for p in sorted(root.glob('Nodes*.lean')):
 s=p.read_text()
 for m in re.finditer(r'^def (\w+Statement) : Prop :=',s,re.M):
  n=m.group(1)
  before=s[:m.start()]
  dc=before.rfind('/--');de=before.rfind('-/')
  doc=before[dc+3:de].strip() if dc>=0 and de>=dc else ''
  # Rayleigh has a theorem before its next def; stop before that theorem as well.
  end=len(s)
  for marker in ['\n/--','\ntheorem ','\n#print ','\nend ']:
   j=s.find(marker,m.end())
   if j>=0:end=min(end,j)
  statement=s[m.start():end].strip()
  label=(re.search(r'`([^`]+)`',doc).group(1) if '`' in doc else ('l:CE' if n=='PositiveToProbabilityStatement' else 'elementary'))
  status='proved' if n in proved else 'assembled' if n in assembled else 'open'
  g=group(n)
  x={'lean_name':'AKLT.Blueprint.Gap.'+n,'module':'.'.join(p.relative_to(base).with_suffix('').parts),
     'file':str(p.relative_to(base)),'line':s.count('\n',0,m.start())+1,
     'paper_label':label,'paper_locator':doc.split('. ')[0],
     'difficulty':('hard' if n in hard else 'easy' if n in easy or status=='proved' else 'medium'),
     'status':status,'in_minimal_mainW_assembly':n in core,
     'statement':statement,'dependencies':deps[g],
     'suggested_proof_route':re.sub(r'\s+',' ',doc)+' '+notes.get(n,''),
     'reuse_pointers':reuse[g]}
  if status=='open':
   assert n in notes,n
   x['proof_assignment']={'first_attempt_required':'different_cheaper_model','architect_status':'no_written_proof_attempt','includes_checker_soundness':True}
   x['estimated_proof_lines']=350 if n in hard else 80 if n in easy else 200
   x['estimated_hours']=2 if n in hard else 0.5 if n in easy else 1
   x['trap_check']={
    'missing_premises':notes[n],
    'vacuity':'The conclusion is not a premise. Finite alphabet nonemptiness is explicit or stored in PlaneSpec. Probability on a bare finite state space forces that space nonempty. Local mathematical conditions are not named closed-leaf assumptions.',
    'empty_degenerate_cases':'Empty volumes are one-point products; singleton alphabets are allowed. Support restrictions and success/failure endpoints are handled as described in missing_premises.',
    'coercions':'Natural cardinalities are explicitly cast to real numbers in bounds; shell radii and indices use integers; spacing and real powers use real numbers. No equality of letters at distinct sites is required.',
    'finset_vs_fintype_sums':'Unqualified sums are Fintype sums on the displayed type. Subsets and geometry use Finset.card; block sums count all labels, including repetitions. Product alphabets retain their site index.',
    'natural_subtraction':'h-3 is used only with h≥4; n-3 in the tail only with n≥44; cycle m-1 is used on Size periods at least three. Other occurrences have no uncontrolled truncated subtraction.',
    'division_by_zero':'Conditioning uses PositiveProbability and an attainable fibre. Product/overlap completions branch on zero fibres or overlap=1. Scale denominators use d>0,n≥44; block denominators use nonempty labels and positive volume; real powers handle delta=1 separately.',
    'instances':'All quantifiable Fintype/DecidableEq/Nonempty instances occur inside the closed Prop. Generic finite-product interfaces explicitly retain DecidableEq of the site type. Audit.lean checks every ...Statement : Prop.'}
  if status=='proved':
   x['proved_by']='AKLT.Blueprint.Gap.'+proved[n]
   x['proof_provenance']={'written_before_new_author_rule':True,'retained_under_explicit_exception':True}
  allnodes.append(x)
opens=[x for x in allnodes if x['status']=='open']
assert len(opens)==58,len(opens)
assert len([x for x in opens if x['in_minimal_mainW_assembly']])==37
report.joinpath('leaves.json').write_text(json.dumps(opens,indent=2,ensure_ascii=False)+'\n')
report.joinpath('nodes.json').write_text(json.dumps(allnodes,indent=2,ensure_ascii=False)+'\n')
print('Open:',len(opens),'Proved:',sum(x['status']=='proved' for x in allnodes),'Assembled:',sum(x['status']=='assembled' for x in allnodes),'Main assembly open:',sum(x['in_minimal_mainW_assembly'] for x in opens))
