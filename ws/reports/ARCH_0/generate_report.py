from pathlib import Path
from collections import defaultdict
import re, json, hashlib

ROOT=Path('/home/ubuntu/aklt/wt/ARCH_0')
OUT=Path('/home/ubuntu/aklt/reports/ARCH_0')
PLAN=Path('/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md')
IT=PLAN.with_name('interfaces.tex')
plan=PLAN.read_text()
env=re.compile(r'\\begin\{(definition|theorem|lemma|proposition|corollary|hypothesis)\}(?:\[[^\]]*\])?\\label\{([^}]+)\}.*?\\end\{\1\}', re.S)
blocks={m.group(2):m.group(0) for m in env.finditer(plan)}
iblocks={m.group(2):m.group(0) for m in env.finditer(IT.read_text())}
assert len(iblocks)==65 and all(v==blocks[k] for k,v in iblocks.items())

# All hand-written mathematical declarations, including helper data and predicates.
defaults={
 'Geometry':'d:moment','Moment':'d:moment','Probability':'d:framemodel',
 'Frame':'d:frame','Polynomial':'d:poly','FrameModel':'d:framemodel',
 'PinModel':'d:pinmodel','Domain':'d:domain','Trails':'d:weights',
 'Pattern':'d:pattern','Kernel':'d:kernel','Automaton':'d:memory-automaton',
 'Stationary':'d:stationary-walk','Computational':'l:alm',
 'Operator':'d:reduction','OperatorContracts':'l:integercheck',
 'FiniteNetwork':'l:finitefacts','Quantum':'l:star','Specification':'l:planeenergy',
 'Common':'l:moments','Response':'l:response','Coefficients':'l:response',
 'Windows':'d:W','Assembly':'t:main','MainV2':'t:main'}
overrides={}
def assign(label, names):
 for name in names.split(): overrides[name]=[label]
assign('d:moment','Plane latticeDist supDist Adjacent neighbours Vec3 dot normSq UnitVector BallVector goldenRatio icoRadius IcoLetter signValue icoVector icoSet moment SpinLetter spinVector spinWeight siteFunctional totalVariation hamming')
assign('d:pinmodel','positiveNeighbours internalBonds originalLegs boundaryDepth protectedSites PinAssignment extendIcoSpins pinnedSum freeSum pinnedExpectation freeExpectation partitionRatio')
assign('d:shells','square squareCorners shellSpacing shellRadius lastShellIndex farVolume shell nearShell window exceptionalIndices')
assign('l:shellgeom','geometryThreshold ParallelClearance')
assign('d:domain','Status Network Network.active Network.Present Network.bonds Network.presentNeighbours Network.LocalRules Network.Ordinary Network.Auxiliary Network.Consistent Network.spins Network.partition Network.expectation Network.ratio')
assign('d:trace','Network.AdmissibleStart traceStep traceNetwork traceCoefficient traceRatio StoppedNetworkTrail stoppedNetworkTrails wordVertices')
assign('p:pairwalk','AdmissibleTarget')
assign('d:pairenv','PairType HasPairType Network.ResponsePair responseEnvelope')
assign('l:moments','DegreeFour SeparateDegreeFour productFunctional rationalMoment rationalStatusMoment contractSpins')
assign('l:exact','MomentLaw momentLawFunctional')
assign('l:threeframes','frameRotation frameVector frameBound frameRatio')
assign('l:planeenergy','frameEnergy inducedBoundary conditionalPlaneLaw conditionalTorusLaw sitesInVolume')
assign('d:poly','Spinor frameSpinor BinaryForm binaryNormSq binaryEval binaryPolynomial binaryActionPolynomial physicalEval polynomialState')
assign('d:model','hamiltonian vbs')
assign('d:Pauli','pauli spinDensity VectorAffine invertPolynomial pauliExponent pauliOperator ratComplexMul rationalPauli rationalOperatorEntry productDensity invertVectors tokenMatrix totalSpinZ totalSpinPlus totalSpinMinus tensorPowerMatrix SupportedVectors')
assign('l:tight','torusReference frameEval')
assign('d:W','WindowProperty')
assign('h:P','ResponseProperty decay PStatement')
assign('t:cutMOS','cutCost cutProbability CutMOSStatement')
assign('d:weights','localThreshold passageFactor DirectionWord wordVertex wordBond IsTrail wordIncoming wordStraight departureCount wordRevisit trailWeight trailBaseWeight')
assign('l:log-mean-bounds','alphaBound betaBound betaPrimeBound logarithmicMean reciprocalLogMean logMeanLower logMeanUpper')
assign('h:H2','OpenTrailBound H2Statement')
assign('t:inputs','certifiedRate InputsStatement')
assign('h:H1','LocalPatternBound H1Statement')
assign('t:H1','H1TheoremStatement')
assign('d:kernel-order','kernelWitness kernelRho witnessKappa firstVisitList shortOrderLE kernelOrdering longOrdering')
assign('h:H3','PositiveVectorBound H3Statement')
assign('d:memory-automaton','Compass Compass.step Compass.reverse RawWindow MemoryWindow windowArrival windowSuccessor WindowAdmissible StepKind windowKind')
assign('d:memorygrowth','kindWeight memoryMatrix lastWindowWord memoryTrailMass')
assign('l:automaton-quotient','MemoryQuotient MemoryQuotient.Correct CompatibleProjection rawBackward quotientBackward')
assign('p:automaton10','quotientEdgeCount')
assign('l:H2-dihedral','SquareSymmetry turnLeft reflectDirection symmetryDirection symmetryWord SameWindowOrbit')
assign('l:alm','openTrailTotal memoryWitnessRatio memoryBaseConstant')
assign('d:phaseweights','Phase phaseTerminal phaseInitial phaseDiagonal phaseTransition')
assign('d:stationary-walk','relaxedReward freeCoefficient stationaryCoefficient stationaryApply freeApply stationaryReward')
assign('d:stationary-certificate','certificateRadius certificateValueScale certificateCoefficientScale coefficientCeiling StationaryData StationaryData.extended StationaryData.potential StationaryData.Passes')
assign('d:prefix-bound','prefixPhases FirstDirection SurvivingPrefix firstDirectionPartialRow stationaryPrefixBound')
assign('p:stationary-check','stationaryCases stationaryPrefixCeiling')
assign('l:phase-expansion','finiteOperatorSum appendWords takeWord truePhaseCoefficient truePhaseSuffix')
assign('l:stationary-domination','trueContinuationSum stationaryContinuationSum')
assign('l:Bellman-soundness','listBackward')
assign('d:reduction','Representation patternDegree SingleReplacement reducedSpinSites reductionGroups groupLeader groupSecond groupIsPair reductionVectors replacementRadius leafNeighbour LocalVariable formalDot reducedIntegrand reducedPolynomial reducedDifference GroupInversion evaluateReduced leaderToken secondToken')
assign('d:exchange','ExchangeSigns GroupBasis ExchangeBasis exchangeWeight centralWeight CentralBasis exchangeBasisVector exchangeSpace centralSpace exchangeOperator symmetricPairProjection')
assign('l:sector','PositiveOn eigenvaluesOn')
assign('l:integercheck','rationalSectorEntry ClearsDenominator integerSectorMatrix thresholdSectorMatrix complexSectorMatrix indexedSectorMatrix leadingMinor bareissState bareissPivot')
assign('l:gram-residual','gramResidual GramResidualRows')
assign('l:35','localProduct localMean')
assign('l:Iw','supportSpins withoutPassageFunctional originalPatternPolynomial')
assign('l:leaf','coveredSiteField')
assign('d:ratios','removeSite stepRatio removedPairMean responseI responseJ')
assign('l:response','responseBeta responseAlpha responseBetaPrime')
assign('l:local','normalizeRotation CoveredDeparture')
assign('p:toruskernel','torusNeighbours reorientedB TorusKernelStatement')
assign('l:star','StarHilbert starAtSite starCasimir starHamiltonian starGap siteHamiltonian StarStatement')
assign('t:mainW','EventualMain MainWStatement')
assign('t:rec','renewalAmplitude RecStatement')
assign('l:Mtheta','ShiftedWitness MThetaStatement')
assign('t:main','MainStatementV2 mainV2_of_parts')
assign('l:CE','AgreeOutside conditionalExpectation blockDirichlet conditionOn conditionalProbability eventMass')

files=[ROOT/'AKLT/Challenge/MainV2.lean']+sorted((ROOT/'AKLT/Defs').glob('*.lean'))+sorted((ROOT/'AKLT/Blueprint/Top').glob('*.lean'))
entries=[]
for p in files:
 s=p.read_text()
 ns='AKLT.Challenge' if 'Challenge' in p.parts else ('AKLT.Defs' if 'Defs' in p.parts else 'AKLT.Blueprint.Top')
 ms=list(re.finditer(r'^(?:noncomputable )?(def|abbrev|structure|inductive|theorem)\s+([^\s:(]+)',s,re.M))
 docs=list(re.finditer(r'/--(.*?)\-/',s,re.S))
 for i,m in enumerate(ms):
  name=m.group(2); end=ms[i+1].start() if i+1<len(ms) else len(s)
  for d in docs:
   if m.start()<d.start()<end: end=d.start(); break
  tail=re.search(r'(?m)^(?:end |#print |#check |noncomputable instance |instance )',s[m.end():end])
  if tail: end=m.end()+tail.start()
  text=s[m.start():end].strip()
  doc=''
  for d in docs:
   if d.end()<=m.start() and (i==0 or d.start()>ms[i-1].start()): doc=d.group(1).strip()
  labels=overrides.get(name)
  if labels is None:
   labels=list(dict.fromkeys(re.findall(r'\b[dlhtpc]:[A-Za-z0-9-]+',doc)))
   labels=[x for x in labels if x in blocks] or [defaults[p.stem]]
  assert all(l in blocks for l in labels),(name,labels)
  entries.append(dict(name=ns+'.'+name, short=name,kind=m.group(1),file=str(p.relative_to(ROOT)),line=s[:m.start()].count('\n')+1,labels=labels,doc=doc,source=text))
bylabel=defaultdict(list)
for e in entries:
 for l in e['labels']: bylabel[l].append(e)
missing=set(iblocks)-set(bylabel)
assert not missing,missing
(OUT/'declarations.json').write_text(json.dumps(entries,indent=2,ensure_ascii=False)+'\n')
(OUT/'interfaces.json').write_text(json.dumps({l:dict(latex=blocks[l],declarations=[e['name'] for e in bylabel[l]]) for l in iblocks},indent=2,ensure_ascii=False)+'\n')

differences={
't:cutMOS':'ResponseProperty carries its domain restrictions. CutMOSStatement universally quantifies A and theta, fixes l0=64 and the displayed exp(-2E), and supplies one integer Mstar. Positivity and the upper bound one for p0, plus Mstar>=1, are retained inside WindowProperty.',
'd:model':'The model is reused by definitional aliases to the frozen H and B; no alternate torus physics is introduced. Site and bond types are the frozen Size/ZMod types.',
'd:moment':'R^3 is Fin 3 -> R with an explicit scalar product; the twelve atoms use Fin 3 x Fin 2 x Fin 2. The U functional permits a zero atom of weight zero, while D has weights 1/20 at the twelve vertices and 2/5 at zero. Distances use extended naturals, with decay zero at infinity.',
'l:moments':'The positive-degree D tensor is encoded by rationalStatusMoment. Covariance is stated for an arbitrary finite product Fin n, arbitrary U/D choices and site-dependent orthogonal matrices. This includes the single-site clauses and is slightly more explicit than the prose site-by-site extension.',
'd:pinmodel':'Volumes and removals are Finsets. Original legs are separately indexed subtypes. Partition observables are functions of total coordinate maps extended by zero outside the active support; the zero values are only indexing defaults. The original G and original pins remain parameters after removals.',
'l:finitefacts':'Finite active networks are indexed by Fin n, with ordered distinct-endpoint bonds counted once and a finite list of unrelated unit pins at each vertex. Free positivity is stated for a finite list of scalar-product factors with explicit degree counts. The normalized free-positivity clause follows from the separately stated positive partition sum. Norm bounds use squared norms.',
'l:35':'Norm inequalities and the range ball use squared norms (9/25). The local U/D bound is the primitive statement; the conditional-mean sentence is obtained by substituting the finitely many factors on a positive fibre, using FiniteFactsStatement. It is not a separate literal conjunct.',
'l:exact':'Arbitrary finite positive weighted unit laws use FrameData plus MomentLaw; repeated atom labels are permitted. Mixtures use Option labels and explicit zero weights at U sites. Separate degree includes the whole inserted polynomial.',
'h:P':'ResponseProperty includes A>=2 and 0<theta<1 as conjuncts instead of external binder restrictions. PStatement is its existential closure. Empty-set distance is infinity with decay zero; for an admissible pair the original protected layer is nonempty.',
'd:poly':'Homogeneous forms use ordinary monomial coefficient arrays Fin(d+1)->C. The matrix action is returned as its actual substituted MvPolynomial. Physical evaluation multiplies the frozen orthonormal coefficients by square-root binomial factors. Spinors are chosen explicitly only on the three finite alphabets.',
'd:frame':'A finite set with weights is represented by FrameData n plus injectivity and the IsFrame predicate. Weighted laws for quadrature have a separate predicate that permits repeated labels.',
'l:tight':'Isometry is expressed as the exact norm-square identity (equivalent for the explicitly linear evaluation map). The statement includes arbitrary compatible finite spinor choices, arbitrary site frames on a torus, and the particular frozen three-frame evaluation.',
'l:threeframes':'Frame letters are labels; injection, norm, antipodality and moment properties are explicit conjuncts. Both signs of the interaction bounds and attainment are retained.',
'd:framemodel':'Laws are real finite weight functions divided by their actual partition sums. Strict positivity is a theorem target in PlaneEnergyStatement. Conditional expectations are explicit fibre quotients. The gap has ENNReal codomain to give infinity for a singleton; gap bounds use PoincareLower.',
'l:planeenergy':'Partial conditioning is encoded by finite equality events on a disjoint J, with an arbitrary target assignment on U. The k-site lower bound includes the one-site cases. Conditioning consistency is equality of actual marginal laws. Torus nearest-neighbour Markov dependence is included explicitly; conditional plane block gaps follow via consistency from the arbitrary-volume plane gap clause.',
'd:shells':'The radius u is a natural number, with positivity supplied in consumers. Shell indices and floor radii are integers. sqrt(sqrt(u)) realizes u^(1/4) on its stated domain. All shells, windows and exceptional indices are explicit finite filters of physical sites.',
'd:W':'WindowProperty includes the positivity/size restrictions as conjuncts and universally quantifies every colouring, translate, exterior seed, integer trial, and two independent finite frame boundaries.',
'l:shellgeom':'Parallel clearance is written as the coordinate distance to each exterior lattice half-plane. The side-meets-square hypothesis is explicit. All other clauses use finite subsets and extended-natural distances.',
'd:domain':'Network uses total status/kept maps for easy trace updates; validity forces the original finite support, local half-edge restrictions and degree bound. Ordinary, auxiliary and consistent are separate predicates. All partition sums are over the finite active subset. Protected original legs are retained and there is no mass field.',
'l:response':'A step is represented by its current auxiliary network rather than a path index j. Coefficients are the actual logarithmic-mean formulas. The three-neighbour and two-neighbour identities, the one-neighbour response and D ratio-one cases are explicit. The intermediate crude bound beta-prime<=bar-beta follows arithmetically from 35510/100000<=36751/100000.',
'd:pattern':'Thirteen template sites and all twenty external slots are explicit. Raw status/kept data are separated from Covered. Tip kept sets are deliberately ignored for present bonds. Current and next are finite sums on the same active set, with the passage status/bond change specified.',
'h:H1':'LocalPatternBound is parameterized by the two thresholds and includes their domain restrictions. H1Statement specializes it to the frozen rational thresholds.',
'd:weights':'Words are Fin n -> Compass. Used bonds are unordered two-element Finsets, and revisit means a previous departure, not an arrival. Inverse threshold weights are specialized to the paper\'s two frozen thresholds.',
'h:H2':'OpenTrailBound retains arbitrary C_V and q, starts, incoming directions and lengths. The closed H2Statement specializes only its two constants to the selected numerical theorem.',
'l:log-mean-bounds':'The exact enclosure arithmetic uses Q and the analytic monotonicity uses R, with explicit casts. Nonincreasing in each variable is encoded as the equivalent joint coordinatewise inequality. All amended table entries are preserved.',
'l:response-typed':'CoveredDeparture makes the normalization/matching of non-tip status and kept data explicit, while allowing covering tips. The actual analytic coefficients and all inequalities used to derive the table bounds are retained.',
'd:kernel':'At each fixed length the sum is finite. Infinite nonnegative series use ENNReal instead of real tsum, avoiding its value zero on nonsummable series. Finiteness is an explicit MTheta conclusion. Exposure products are a recursive ordered sum, not a second independent product convention.',
'd:kernel-order':'First visits are Fin n indices; mergeSort uses the exact rational score, an explicit zero-reward infinity branch and path-index ties. The dyadic h_C is not 6/5. The long ordering is straight-first then turning, both in path order.',
'h:H3':'The closed contract uses the stated all-finite-cutoff rational inequality. The full nonnegative M1 row inequality is included separately in StationaryAssemblyStatement, with ENNReal semantics.',
'l:Mtheta':'Shifted entries and the majorant use ENNReal. The statement includes the shift bound, all-entry finiteness, and the same positive vector at an existential theta and rho. Negative integer shifts are exact zpow; the majorant uses real rpow for n/2.',
'l:automaton-quotient':'The statement includes existence of labelled quotient data from a compatible surjective raw map, then equality of every finite stopped iterate. Compatibility makes all admissibility, kind, successor and nonrevisit-arrival checks explicit. Unused nonraw word values are immaterial.',
'p:automaton10':'The supplied finite quotient is expressed existentially, with actual raw-word cardinality, representatives, surjectivity and labelled edge counts. No external data file or hash is assumed correct.',
'l:alm':'The constant uses sSup/sInf on finite ranges, with the zero-memory case excluded by m>=1. W_r is evaluated at a fixed start/incoming direction; the all-start conclusion uses the translation/rotation symmetry of the actual lattice weights. The statement also permits any larger constant.',
'l:H2-dihedral':'The quotient orbit count is expressed by 115 representatives and unique orbit coverage, avoiding an assumed Setoid instance. The raw count is 916. Symmetry and representative-row soundness are explicit predicates.',
'p:H2-test':'The witness is an existential positive integer function on the regenerated raw state type, with attained lower/upper extrema. Its maximum row ratio is expressed by an all-row inequality plus an equality row. The integer row form uses the regenerated matrix entries with the exact common denominator.',
'l:H2-CV':'The finite prefix estimates are uniform. The base-constant bound is stated for every positive vector of max/min ratio at most six, hence applies to the selected witness. The H2 conclusion has the semantic H2-test witness assertion as premise; no growth-lemma theorem is added as a hypothesis.',
'd:memory-automaton':'The raw state type is a subtype of the finite compass-word type. At memory zero, arrival has an unused default; all automaton theorems require m>=1. Absolute labels are preserved.',
'd:memorygrowth':'The matrix is regenerated by a four-direction sum and exact successor equality. True endpoint-window masses use the whole true trail weight. The selected small test is the m=6 instance.',
'd:phaseweights':'Phase transitions are a 4-by-4 coefficient function with explicit diagonal and the two permitted off-diagonal cases. Finite folds sum all phase histories.',
'l:phase-expansion':'The sum over histories is a four-coordinate fold. The statement includes both its exact long-order contribution and its factorization at every prefix length.',
'd:stationary-walk':'States are curried Phase, Fin q and Plane coordinates. The centre/target rows are zero. Centre values/transitions contribute zero. Initial-bond exclusion and known-site rules remain active at every time.',
'l:stationary-domination':'The statement includes pointwise domination of every true suffix phase transition and the resulting finite-horizon continuation sums. Prefixes have L>=12=m+2; no weaker cutoff is substituted.',
'l:Bellman-soundness':'A finitely branching graph is represented by a list of destination/real-weight pairs at each state. A real-valued F is automatically finite-valued. Both finite sums and their ENNReal full sum are bounded. The terminal-equality sufficient condition is the immediate special case of the displayed supersolution hypothesis.',
'd:stationary-certificate':'Arrays use natural numbers (so nonnegativity is structural), a finite square subtype for stored values, and positive caps. Exact coefficient ceilings have scale 2^48, values scale 2^16. Passes contains every free/local row, cap and terminal condition.',
'l:stationary-local-global':'Rational potentials express the displayed inequality exactly. The statement also explicitly bounds all finite continuation sums. It includes coefficient-ceiling soundness as a rational inequality.',
'd:prefix-bound':'Short trails and surviving prefixes are generated as finite direction words. Prefix phases use the actual trail history. J is an exact rational number; a hit at twelve is excluded from the surviving-prefix part.',
'l:prefix-domination':'The full nonnegative sum is represented by its equivalent bound at every finite true-trail cutoff. No prefix-only inequality is substituted for the all-length assertion.',
'l:kernel-reflection':'The statement explicitly preserves raw closedness, first direction, weights, ordering, response pairs, coefficients, pair type and B shift, and gives equality for every cutoff. The B/S potential is never assumed to be reflected data.',
'p:stationary-check':'The five arrays and a correct regenerated quotient are existential data. Prefix ceilings are inequalities after multiplication by 10^9 in Q. Spatial count 19881 and type Fin 3741 are explicit. No files are imported as facts.',
'l:stationary-assembly':'The same five passing arrays and exact prefix ceilings imply the two finite row inequalities, their rational assembly bounds, the full ENNReal M1 row bounds and H3. Proof dependencies such as prefix domination and reflection are not extra premises.',
'l:Iw':'Z_w is an explicit passage-deleted finite functional. A reconstructed rational polynomial is related to each original partition sum by an explicit equality target. Affinity and orthogonal covariance are polynomial statements.',
'l:leaf':'One-bond leaf laws are expressed by equality for every neighbour vector in the closed unit ball, with an existential positive A and ball vector u. This is the factor identity used in the reductions. Zero-bond local positivity is explicit.',
'd:reduction':'The two representations are finite constructors. Surviving vector tokens are a subset of the twenty original slot indices, so inactive variables are ignored rather than renumbered globally. Every replacement and internal moment contraction is reconstructed from the pattern.',
'c:reduce':'The reduced polynomial is rational and evaluated in R. Positivity is tested on twenty unit vectors with unused variables absent, equivalent to the paper\'s k surviving vectors. The common positive K and ball-vector data are explicit.',
'd:Pauli':'Operators and product densities are explicit finite tensor-basis matrices. Rational real/imaginary Pauli entries are available separately for reconstruction. Vector-affinity counts total degree over each triple of coordinates, not coordinatewise multilinearity alone.',
'l:inversion':'The trace identity is stated for any finite active token set J and any supported rational vector-affine polynomial. Complex positive-(semi)definiteness uses Mathlib\'s ComplexOrder scope. The closed-ball conclusion includes unit vectors.',
'l:Ostruct':'Commutation is expressed in finite tensor coordinates, with SU(2) specified by g* g=I and det g=1. U-pair compression and D-pair exchange are actual linear-map identities.',
'd:exchange':'The sector basis is an integer tensor-coordinate function. Symmetric middle vectors and antisymmetric vectors are unnormalized, exactly as in the LaTeX. Signs on singles and U pairs are ignored; this only repeats identical sectors. Central subspaces inherit the ambient Hilbert inner product.',
'l:sector':'An operator on a supported sector is represented by an ambient linear map that preserves the sector; Hermiticity and the three commutation relations are imposed only on that sector. Equality is of eigenvalue sets, with a separate positive-definiteness equivalence. No multiplicity equality is asserted.',
'l:gram-residual':'Matrices use Fin n indices and explicit integer row sums. Positivity of the diagonal is retained. Positive definiteness is asserted for casts to both R and C. The zero-L case is an allowed instance, not a separate required witness.',
'l:integercheck':'The matrices are reconstructed from rational polynomials, inversion, Pauli entries and integer sector vectors. floor only totalizes integer extraction; the statement explicitly requires equality with the unrounded form after denominator clearing. The exact complex scale is 15 D0 q. Optional Bareiss divisibility and principal-minor identities are separate conjuncts.',
'p:certificate':'All supported exchange sign assignments are checked (unused signs repeat sectors). Each certificate supplies an explicit bijection from Fin t to the actual central-sector basis, allowing a concrete verified data order without relying on Fintype.equivFin. The reindexed matrix is still reconstructed from the polynomial. Positive g,d,S and both strict residual conditions are explicit. No matrix, factor generation or pivot data are postulated.',
't:rec':'The existential theta and rho additionally retain ShiftedWitness and the exact displayed renewal amplitude. This makes the plan\'s “one may take” clause an explicit part of the closed proposition.',
't:H1':'This has its own closed H1TheoremStatement, in addition to the parameterized H1 property and fixed H1Statement wrapper.',
't:inputs':'InputsStatement contains the exact semantic H1/H2/H3 conclusions and q_*<2499/2500<1. The prose identifying the three proof routes is represented by separate reconstruction/check Props, rather than a proof-method field in a mathematical proposition. No certificate correctness is asserted by merely importing the module.',
'p:toruskernel':'Simplicity is expressed by two-site bonds and injective bond indexing; degree four is the neighbour-cardinality assertion. Reorientation is a Boolean sign choice in the actual polynomial product, followed by the frozen coordinate conversion.',
'l:star':'The five-site star reuses the frozen spin matrices and projector formula. The infimum definition of g_star is accompanied by explicit positivity, attainment and minimality targets. This is an auxiliary finite star, not a new torus Hamiltonian.',
't:QD':'The operator inequality is expressed as quadratic-form coercivity for every real Poincare lower bound gamma, rather than multiplication by an abstract scalar infimum. The density identity retains pi, squared modulus and the exact frozen norm. The eigenvalue-gap sentence is the corresponding consequence with the separate kernel/positivity facts.',
't:mainW':'The W premise is the existential closure of WindowProperty over l0,p0,Mstar. The conclusion EventualMain includes the eventual ground-line equality and spectral bound, with no parity assumptions.',
't:main':'Size replaces integer periods with natural periods at least three. Nonzero eigenvalues are real values embedded in C, as in the frozen Challenge. All-size nonzero B and kernel equality precede the existential eventual gap. mainV2_of_parts is explicitly an implication from closed interface Props, not an unconditional proof of their inhabitants.'}

# Every represented interface gets an explicit row even where only binder syntax changed.
assert set(iblocks)<=set(differences),set(iblocks)-set(differences)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
props=[e for e in entries if e['short'].endswith('Statement') and ': Prop :=' in e['source']]
assembly=next(e for e in entries if e['short']=='mainV2_of_parts')
challenge=next(e for e in entries if e['short']=='MainStatementV2')
final_seconds=re.findall(r'(?m)^real ([0-9.]+)', (OUT/'final-build.log').read_text())[-1]
lines=[
'STATUS: COMPLETE',
'',
'The statement-layer design is complete and the top assembly implication is proved by the Lean kernel. The mathematical interface propositions remain unproved targets for their assigned lanes. This delivery does not assert an unconditional proof of MainStatementV2.',
'',
'**Files and build surface.**',
'',
'Import `AKLT.Defs.All` for shared definitions and `AKLT.Blueprint.Top.All` for all closed interfaces and assembly. `AKLT.Blueprint.Top.Audit` additionally checks that all 47 interface wrappers have the closed type `Prop` and prints the assembly theorem and its dependencies.',
'',
'| File | Lines | SHA-256 |', '|---|---:|---|']
for p in files:
 lines.append(f'| [{p.relative_to(ROOT)}]({p}) | {len(p.read_text().splitlines())} | `{sha(p)}` |')
lines += ['',f'The frozen `AKLT/Challenge/Main.lean` was not edited. Its SHA-256 is `{sha(ROOT/"AKLT/Challenge/Main.lean")}`.',
 f'`MainV2.lean` has 25 lines and imports exactly Mathlib and AKLT.Challenge.Main. Its ready marker contains `{sha(ROOT/"AKLT/Challenge/MainV2.lean")}`. The marker was written immediately after the first successful 13.21-second build and still passes `sha256sum -c`.',
 '', '**Challenge statement.**', '', '```lean', challenge['source'], '```',
 '', '**Proved export.**', '', '```lean',assembly['source'].split(':= by')[0].rstrip(), '```', '',
 'The proof extracts the selected H1/H2/H3 inputs, obtains the response witnesses from Rec, applies CutMOS with the displayed exp(-2E), applies MainW to the resulting W parameters, and uses the independent TorusKernel proposition for every size. QD is an exported target used inside the eventual lane-A proof of MainW; it is not a redundant extra argument of this assembly.',
 '', '**Kernel dependency audit.**', '', 'There is one hand-written exported theorem in this delivery. Its exact output is:', '',
 '```text', "'AKLT.Blueprint.Top.mainV2_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]", '```',
 '', 'The three dependencies are exactly the permitted logical foundations. All 47 closed interface wrappers elaborate as `: Prop`, with no section hypotheses, mathematical typeclass assumptions or implicit mathematical parameters. The auxiliary definitions and finite enumeration instances contain no postulates or unproved proof terms.',
 '', '**Build commands and timings.**', '', '```bash', 'export PATH="$HOME/.elan/bin:$PATH"', 'lake build AKLT.Challenge.MainV2', '# First successful build: real 13.21 s (Main 3.1 s, MainV2 2.7 s)', 'lake build AKLT.Blueprint.Top.Assembly AKLT.Blueprint.Top.Computation AKLT.Blueprint.Top.Operator', '# Full affected dependency rebuild: real 38.77 s', 'lake build AKLT.Blueprint.Top.All AKLT.Defs.All', '# Import-surface build: real 10.41 s', 'lake build AKLT.Blueprint.Top.Audit', '# Closedness and dependency audit: real 9.27 s', '```',
 '', f'The final source rebuild used `lake build AKLT.Blueprint.Top.Audit AKLT.Defs.All` and passed in {final_seconds} seconds. Logs: [build.log](build.log), [audit.log](audit.log), [final-build.log](final-build.log), and [constants-check.log](constants-check.log). Only project modules were built; Mathlib was already prebuilt. There were no sub-agents, updates, package writes, or unrestricted parallel builds. Independent targets in each Lake invocation number at most three; this stays within the six-process brief.',
 '', '**Modelling choices and Lean traps checked.**', '',
 '- The Hamiltonian and VBS state are the frozen Challenge definitions. All final spectral assertions refer to those constants. Natural Size subtypes encode exactly the periods at least three, with no parity predicates.',
 '- Plane distances are ambient lattice distances, including after removals. Original pin legs remain individually indexed; frame boundaries have one admissible letter per exterior site. These types are never interchanged.',
 '- Every partition sum and every fixed-length path sum is finite, including its empty-product configuration. U has twelve positive atoms; its optional zero label has weight zero. D has the exact 3/5 mixture plus the 2/5 zero atom. No measure, disintegration or arbitrary-function rotational invariance is used.',
 '- Total coordinate maps simplify trace updates; all networks used by the contracts have an explicit finite active volume. Validity, ordinary protection, consistent kept sets and auxiliary defects are separate predicates. Removed sites have no new pin factors or scalar mass.',
 '- The covered pattern has thirteen sites, twenty explicit slots, both corner slots, and covering U tips whose kept sets are not constrained by a global tip rule. The departure coefficient is computed from the evolving status.',
 '- True revisits count previous departures. The initial virtual incoming edge is not marked used; its reversal is explicitly forbidden. All trail bonds are unordered finite sets, so a reversed repeat is still a repeat.',
 '- The kernel uses the amended alpha/beta/beta-prime table, actual dead neighbours and ambient shifts. The short cutoff is twelve; the dyadic h_C differs from 6/5 by -1/22517998136852480. Exposure sums include the x factor at the rewarded position and use theta-independent orderings.',
 '- Infinite nonnegative kernels use ENNReal, avoiding the real tsum convention on divergent series. All-length H3 is an all-cutoff assertion, and finiteness of shifted kernels is a theorem target. No finite prefix is mistaken for H3.',
 '- Stationary certificates keep the initial-bond and known-site rules forever on Z^2, use L>=m+2=12, cap every stored value, and distinguish value scale 2^16 from coefficient scale 2^48. No spatial quotient or parity improvement appears.',
 '- Operator matrices are rebuilt from the pattern, rational moment contractions, leaf replacements, inversion, Pauli entries and unnormalized integer sector vectors. An explicit basis bijection determines the finite certificate order. Complex positivity uses ComplexOrder. Integer sector forms are not confused with orthonormal operator matrices. The positive congruence scale is 15 D0 q, and lower-triangular L need not be invertible.',
 '- Lean sum/product bodies containing addition are parenthesized; otherwise the binder can end before the addition. Dependent Fin prefix embeddings explicitly bind their size proof. The keywords prefix and Pi were avoided as local names. Fintype instances for small enums are explicit because the toolchain deriving plugin produced an incompatible list coercion.',
 '- The only resource adjustment is maxRecDepth 2048 in Stationary.lean for finite-square subtype elaboration. No unbounded heartbeat setting, evaluation effects or untrusted computation is present.',
 '- A source scan found no forbidden proof placeholders or execution mechanisms. The literal #print axioms commands are the required audit. MainV2 imports were checked, its hash verified, and the frozen Main diff is empty.',
 '- Small Python Fraction checks confirmed the transcription of q, the dyadic witness, H2 denominators, C_V majorant and nine-decimal row assembly. Those are fidelity checks only; no native result is claimed as a Lean input proof.',
 '', '**Differences from the LaTeX.**', '',
 'Every interface has a row below, including changes that are only finite indexing, squared norms, explicit domain predicates or equivalent form inequalities. These rows identify the chosen Lean encoding; mathematical equivalence lemmas needed by downstream proofs remain their owners\' proof obligations. No parity, graph-scope, volume threshold or numerical weakening is introduced in the headline statement.',
 '', '| Plan label | Lean form and difference |', '|---|---|']
for label in list(iblocks)+[l for l in ('t:main','p:toruskernel','l:star','t:QD','t:mainW') if l not in iblocks]:
 lines.append(f'| `{label}` | {differences[label]} |')
lines += ['', '**Open proof obligations.**', '',
 'The assigned design work is complete. The 47 closed Props are obligations, not proved facts. In particular H1 pattern coverage/operator certificates, H2 raw-window enumeration and witness checks, H3 quotient reconstruction/Bellman data/prefix checks, response recursion, cut geometry/windows, and the quantum/classical/periodic gap proofs still require inhabitants supplied by their owners. No certificate file, stored matrix, orbit list, gzip hash, or native exit code is trusted. There is no unconditional theorem claiming MainStatementV2 in this delivery.',
 '', 'The notation and contracts are now available for those proofs. The finite computational definitions are mathematical specifications; optimized kernel checkers, balanced lookup structures, sharding and data encodings belong to the certificate lanes. The optional Bareiss fallback is specified but is not required by the primary Gram/residual proposition.',
 '', '**Complete declaration-to-label registry.**', '',
 f'This registry lists {len(entries)} hand-written mathematical definitions, predicates, data types and the proved theorem. Compiler-generated recursors/decidability/repr functions and anonymous typeclass instances are standard representation infrastructure, not additional mathematical assertions. The finite instances are all explicit enum proofs or Fintype.ofFinite on a finite subtype. [declarations.json](declarations.json) contains the same registry with the full Lean source of each declaration.',
 '', '| Lean declaration | Kind | Source | Plan label(s) |', '|---|---|---|---|']
for e in entries:
 links=', '.join(f'[{l}](#latex-{l.replace(":","-")})' for l in e['labels'])
 lines.append(f'| `{e["name"]}` | {e["kind"]} | [{e["file"]}:{e["line"]}]({ROOT/e["file"]}:{e["line"]}) | {links} |')
lines += ['', '**Exported closed propositions, with their complete Lean statements.**', '']
for e in props:
 lines+=['<details>',f'<summary>{e["name"]} — {", ".join(e["labels"])}</summary>','', '```lean',e['source'],'```','','</details>','']
lines += ['**Exact LaTeX source for every represented label.**', '',
 'The following blocks are copied byte-for-byte from the full revision plan, including all amended statements. All 65 exported interface blocks were independently compared against interfaces.tex and match verbatim. Additional internal labels are included whenever a shared definition or the top assembly uses them. [interfaces.json](interfaces.json) records the 65 interface mappings in machine-readable form.', '']
labelorder=[m.group(2) for m in env.finditer(plan) if m.group(2) in bylabel]
for label in labelorder:
 lines += [f'<a id="latex-{label.replace(":","-")}"></a>', f'**{label}.**', '',
  'Lean: '+', '.join('`'+e['name']+'`' for e in bylabel[label])+'.', '', '```latex',blocks[label],'```','']
(OUT/'report.md').write_text('\n'.join(lines)+'\n')
print(f'{len(files)} Lean files; {len(entries)} mathematical declarations; {len(props)} closed interface Props; 65/65 labels covered; report {len(lines)} emitted lines')
