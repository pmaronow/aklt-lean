from pathlib import Path
import json, re
root=Path('/home/ubuntu/aklt/wt/BP_REC/AKLT/Blueprint/Rec')
out=Path('/home/ubuntu/aklt/reports/BP_REC')
if (out/'adaptation-baseline.json').exists():
    import runpy
    runpy.run_path(str(out/'update_adaptation.py'), run_name='__main__')
    raise SystemExit(0)
order=['NodesResponse','NodesLogMean','NodesLocal','NodesWalk','NodesClosure','NodesKernel','NodesRecursion','NodesRenewal']
proved={'CrudeRationalStatement':'crudeRational','LogRationalRowsStatement':'logRationalRows','TypedCrudeRowsStatement':'typedCrudeRows','FirstTermBoundStatement':'firstTermBound_of_leaves'}
hard=set('NetworkPositiveStatement RemovedMeanIntervalsStatement LocalMixtureStatement TraceDynamicsStatement PairExpansionStatement KeptInvariantStatement CoveredClosureStatement TerminalExceptionLocationStatement KernelLengthMajorantStatement WitnessPerturbationStatement TraceKernelLengthStatement RemovalEnvelopeStatement'.split())
easy=set('DStepTrivialStatement OneStepTrivialStatement BetaPrimePositiveStatement AlphaPositiveStatement BetaPositiveStatement NormalizeStartStatement DiamondTwelveStatement UDepartureInjectiveStatement EnvelopeOrderStatement KernelOrderingStatement KernelPositivityStatement KernelSupportStatement CrudeRationalStatement LogRationalRowsStatement TypedCrudeRowsStatement RenewalScalarLimitStatement'.split())
config={
'NodesResponse':(['Network.partition','Network.Auxiliary','FiniteSpinNetwork.Valid','siteFunctional','removedPairMean','stepRatio','responseI','responseJ','logarithmicMean'],['Finset.sum_congr','Finset.sum_mul','Finset.prod_mul_distrib','Real.log_div','AKLT.Vendor.FiniteConditioning.condExp_on_fiber'], 'Reindex finite active spins into the common finite-network model. For conditioning, sum fibres explicitly, discard zero-mass fibres, use the degree-four moments and three-factor mean bound. For the coefficient steps use the displayed integrated I,J formulas, positive denominators and exact rational inequalities.', 'FiniteConditioning/P015/P015_FiniteConditioning.lean supplies fibre identification only; reuse-map.md lists no full response donor. The common moments/finite-facts results must eventually be imported as proved theorems.', 'AdmissibleStart and present outgoing bond are retained in Departure. Auxiliary, rather than ordinary, is the correct premise. Departure y has no original legs; each surviving neighbour is unpinned after y is deleted.', 'G=empty cannot carry a Departure. A one-bond D start is allowed; a two-bond D start is excluded. Equal log-mean arguments use the explicit diagonal definition.', 'All normalizers are positive; the mean arguments have positive rational lower bounds. Crude log enclosure uses 0<s<1, hence 1-s, 1+s and 1-t^2 are nonzero.'),
'NodesLogMean':(['logarithmicMean','reciprocalLogMean','logMeanLower','logMeanUpper','localThreshold','alphaBound','betaBound','betaPrimeBound'],['intervalIntegral.integral_mono_on','Real.hasDerivAt_log','Real.log_div','Finset.sum_range_succ'], 'Use the reciprocal affine-denominator integral, then compare integrands or differentiate on a compact positive rectangle. Derive the exact odd-power remainder by integrating a finite geometric identity. Clear denominators only after proving their positivity.', 'reuse-map.md l:log-mean-bounds: LeanCert dyadic arithmetic is optional, not an analytic log evaluator. Mathlib interval integration is sufficient. Endpoint rows are already proved with norm_num.', 'All variables in monotonicity are positive; c is in [3/5,1]. Rational enclosure statements explicitly require 0<s<1.', 'The diagonal x=y and f(1)=1 are treated separately. The rational series is used only below 1 and never at s=1.', 'The affine denominator is positive on [0,1]. For the rational remainder, 0<t<1 and 1-s>0 justify each division.'),
'NodesLocal':(['CoveredDepartureV2','PatternData.Covered','patternCurrent','patternNext','localMean','siteFunctional','responseI','responseJ'],['Finset.sum_congr','Finset.sum_mul','Finset.mul_sum','Finset.prod_mul_distrib'], 'First prove the one-tip identity from its normalizer and effective mean; realize this mean by three unit U fields. Resolve each missing or ball-valued corner field into antipodal unit fields. Disintegrate finite outside configurations and assemble the common nonnegative mixture. Apply H1 pointwise and cancel only positive normalizers.', 'No complete local-cover donor exists (reuse-map.md l:local). The common three-factor mean theorem supplies the full 3/5 ball. It must be a proved import, not an assumed Rec leaf.', 'V2 keeps exact non-tip status matching and intersects kept flags with original G. Original legs and both slots at each corner remain. H1 is the permitted independent computational premise.', 'A zero effective tip mean, a removed tip, an absent bond, and a zero corner field are all included. The mixture may contain zero weights; positive partition sums rule out an empty representing mixture.', 'Tip normalizers and departure partition sums are positive. Analytic comparisons require c>0 (or c>=3/5) and positive lower endpoints.'),
'NodesWalk':(['traceStep','traceNetwork','traceCoefficient','prefixNetwork','StoppedNetworkTrail','stoppedNetworkTrails','AdmissibleTarget','stoppedSum','uncoveredCount'],['Finset.sum_congr','Finset.sum_mul','Finset.abs_sum_le_sum_abs','Finset.card_le_card','hasSum_geometric_of_lt_one'], 'Use finite degree-four moment expansions for one step. Induct on the consumed original bonds, retaining untouched original legs and the live mark. Iterate unnormalized coordinate numerators and divide only at the end. For exposure telescope in the given order. For one-point estimates compare both pin choices to the same pointwise trail weight before summing a geometric tail.', 'reuse-map.md l:stepid, p:pairwalk, l:exposure and l:onepoint give no complete donor. Gen/Bellman first-hit infrastructure can organize a finite tree, but a model/trace bridge is still required.', 'Every active start is outside original S; U degree<=3 and D degree<=1. Targets have the explicit total-factor bound, including original legs. Trace classes forbid departures from S.', 'Length zero, no available bond, a dead branch, an initially D site, and a D target are included. The target is distinct from the start. No initial two-bond D expansion is introduced.', 'Positive finite-network normalizers justify ratios and telescope. Products over Fin 0 equal one; empty branch sums equal zero. H2 includes 0<q<1 for the geometric tail.'),
'NodesClosure':(['Network.Consistent','Network.ResponsePair','PairData','PairSetup','normalizeStart','prefixNetwork','CoveredDepartureV2','uncoveredCount'],['Finset.card_le_card','Finset.card_image_iff','Finset.mem_erase','Finset.mem_sdiff'], 'Induct on prefixes with a sole live kept-set defect. Separate U departure, initial D departure, later D departure and arrival. Delete the live interior point to recover an ordinary domain. For the second expansion retain one fixed protected defect and inject exceptional U departures into the punctured radius-two diamond.', 'reuse-map.md l:closure and l:terminalcover: no full donor. Use native finite lattice/Finset induction; these are model-specific combinatorics.', 'PairSetup retains an ordinary consistent starting pair, designated removed centre, explicit incoming direction, and u outside S. Second-expansion statements additionally require v outside S. Removing a protected terminal is never asserted.', 'Zero-length live D has two kept flags, while a later live D has one. The terminal protected site retains its U law and all original legs. Exceptions may occur anywhere, not just at a prefix.', 'No division occurs in the combinatorial invariant. Partition equality for normalization erases only a flag to an already removed centre.'),
'NodesKernel':(['ClosedTrail','kernelOrdering','responsePairs','pairShift','kernelLengthCoefficient','shiftKernel','shiftedKernel','shiftedLength','kernelMajorant','transportTheta','transportRho','RenewalRows'],['ENNReal.tsum_le_tsum','ENNReal.tsum_eq_iSup_sum','ENNReal.ofReal_tsum_of_nonneg','hasSum_coe_mul_geometric_of_norm_lt_one','hasSum_sq_mul_geometric_of_norm_lt_one'], 'Check the first-visit ordering, nonnegative coefficient support and the geometric shift bound. Regroup nonnegative sums in ENNReal. Dominate one length by H2 and sum n r^n. Exhaust H3 finite cutoffs at theta=1. Bound the shift increment and sum n(n+1)r^n, then apply the explicit epsilon budget with the same h and ordering.', 'reuse-map.md l:Mtheta has no full donor. Mathlib SpecificLimits supplies both geometric moments. Gen/Bellman/Growth.lean gives finite witness-growth patterns; it does not prove this shifted kernel.', 'OpenTrailBound contains CV>=1 and 0<q<1. Geometry uses a genuine closed first-hit trail. Every kernel entry stays ENNReal until finiteness is established. Perturbation takes a concrete numerical unshifted row premise.', 'No length-zero contribution; s=0 shift increment is zero. Zero reward is explicitly handled by shortOrderLE. The last target stays live. Revisit departures carry 1/5.', 'q/sqrt(theta)<1 follows from q^2<theta and q>0. transportB>0 follows from CV>=1 and 0<q<1. All theta powers in conversions have positive base.'),
'NodesRecursion':(['responseEnvelope','PairData','PairData.normalized','firstLength','firstTerm','secondTerm','recursionSeries','sourceConstant','protectedDistance'],['csSup_le','le_csSup','Finset.abs_sum_le_sum_abs','Finset.sum_congr','ENNReal.ofReal_tsum_of_nonneg'], 'Realize an ordinary response pair and fix a single lattice isometry for all of its trails. Split the finite pair expansion into target and boundary terms. For the target term use ordered exposure, response-pair closure, actual shift and the type-dependent kernel comparison. For the boundary term expand again, bound the residual uniformly, and sum pointwise maxima. Finally use the bounded supremum and ordinary U/X removal realization.', 'reuse-map.md l:recineq and t:rec have no complete donor. Finite-sum reindexing and conditional-complete-order lemmas are sufficient for the final gluing. Do not substitute a window or gap theorem.', 'The pair is in an ordinary consistent domain and has a designated removed centre. d>=1 ensures both endpoints are outside original S. The second trace always uses target e and stopping set S.', 'Supremum includes zero for the empty class; negative d is clamped by Int.toNat. Distances remain to original S, not to newly removed sites. A nonempty pair forces finite nonempty G and finite protected distance.', 'Use positive finite laws before bounding expectations by one. Real kernels are toReal of ENNReal coefficients only after summability. CV/(1-q) is defined with 0<q<1 from H2.'),
'NodesRenewal':(['RenewalRows','renewalOp','renewalIterate','renewalSource','hmin','hmax','genericAmplitude'],['Summable.tsum_le_tsum','Summable.tsum_add','hasSum_geometric_of_lt_one','tendsto_pow_atTop_nhds_zero_of_lt_one'], 'Prove the bounded positive action and finite iteration. Control the remainder by the unshifted h, uniformly on all integers, and the source by h theta^d. Apply the shifted row inequality iteratively and pass to the scalar geometric limit. Use explicit Summable premises whenever manipulating a real tsum.', 'Gen/Bellman/Basic.lean System.step_mono, step_add and horizon_eq_sum are useful ENNReal analogues; System already supports arbitrary shift labels; instantiate its state as PairType x Z and labels as PairType x N, then supply a finiteness/toReal bridge. Mathlib tsum/limit APIs suffice; no Perron-Frobenius donor is needed.', 'Rows are nonnegative and explicitly weighted-summable; h is positive at both types. Each statement retains 0<rho<1, q>0, q^2<theta<1, and CT>=0 where needed.', 'The operator is defined on ALL integer depths; arbitrary shifts may reach negative integers. Finite iteration works even without constant negative extension, since F<=2 and the negative source equals 2. k=0 is included.', 'hmin>0 and 1-rho>0 are required before division. theta>0 follows from q^2<theta. Negative integer powers are zpow, not natural subtraction.')}

special={
'NetworkPositiveStatement':'Check the zero-active-site product explicitly: the partition is one even when G is empty; zero-weight U atoms are not asserted to lie on the unit sphere.',
'ThreeFactorizationStatement':'The three neighbours are pairwise distinct by three separate inequalities. Integrate the current U law and the next D law without rescaling their masses.',
'TwoFactorizationStatement':'o != f is retained; the next D law has one remaining bond, whose integrated scalar is one.',
'RemovedMeanIntervalsStatement':'The free inequalities use degree-admissible pair insertions after removal; do not infer free positivity for arbitrary high-degree observables.',
'TwoMeanIntervalsStatement':'The two present neighbours are distinct, unpinned and nonadjacent after y is removed.',
'FreeRemovedPairStatement':'Distinct endpoints are explicit. If the departure is D its degree bound makes this two-neighbour class empty, which is legitimate rather than an extra case.',
'LogMeanBasicStatement':'Check x=y separately before using a log difference as denominator; the defining diagonal gives the divided-difference identity too.',
'LogMeanMonotoneStatement':'Both smaller inputs are strictly positive and both larger inputs inherit positivity.',
'CrudeLogEnclosureStatement':'The strict s<1 premise excludes the removable endpoint of the crude rational expression.',
'StepRatioPositiveStatement':'The post-step network must still satisfy LocalRules, including D degree<=2 and unchanged protected laws.',
'FreeRatioUpperStatement':'Treat D, one-, two- and three-neighbour U departures; free positivity is used only for degree-four pair insertions.',
'PinnedRatioUpperStatement':'The pointwise I>=1/2 estimate uses norm<=1 of positive-weight support atoms; zero-weight U zero atoms cannot invalidate a weighted inequality.',
'DStepTrivialStatement':'D has at most its outgoing present bond and no original pin, so deleting it destroys no other present bond.',
'OneStepTrivialStatement':'Present outgoing membership rules out a zero-neighbour case; card=1 leaves exactly that bond.',
'BetaPrimePositiveStatement':'The two I2 arguments have lower bound 22/25, so the logarithmic mean is strictly positive.',
'BetaPrimeUniformStatement':'Use the 22/25 endpoint, not the weaker three-neighbour endpoint.',
'TwoLogIdentityStatement':'Even when the two I2 values coincide, the same beta-prime definition is used and the response vanishes correctly.',
'AlphaPositiveStatement':'The lower estimate 25/102-25/116=175/5916 is strictly positive; a negative subtraction is not silently discarded.',
'AlphaUniformStatement':'Subtract a justified lower bound 25/134 for the second reciprocal mean.',
'BetaPositiveStatement':'Every I argument has lower bound 41/50; avoid proving positivity by an unjustified division simplification.',
'BetaUniformStatement':'The crude rational enclosure gives 367502/10^6, strictly below 36751/100000.',
'ThreeLogIdentityStatement':'Order of the log subtraction and pin choices matches the paper. The alpha term multiplies only the fg response.',
'ReciprocalIntegralStatement':'On the diagonal the integrand is constant 1/x; both endpoints of the affine denominator remain positive.',
'LogCoefficientMonoXStatement':'Use 5c>=3 and c<=1 simultaneously; monotonicity would not follow for arbitrary positive c.',
'LogCoefficientMonoYStatement':'The larger y inherits positivity and the closed t interval includes both endpoints.',
'EightTermRemainderStatement':'The geometric identity has eight terms k=0..7 and exponent 16 in the remainder; integration gives exponent 17 and divisor 17.',
'LogEnclosureLowerStatement':'Rat.cast preserves the exact finite sum and all positive denominators; no floating logarithm enters.',
'LogEnclosureUpperStatement':'The remainder denominator includes all of 17, 1-t^2 and 1-s.',
'TipReplacementStatement':'v may be any vector because the integrated factor is affine in v. The effective mean is realized by unit U fields even for an actual D tip.',
'BallSlotConvexityStatement':'b=0 needs a chosen unit direction; t=1/2 then fills a missing factor. Endpoints t=0,1 are allowed.',
'LocalMixtureStatement':'Both partitions use the same nonnegative weights; proportional tip normalizers are absorbed in those weights, not silently equated.',
'CoveredRatioStatement':'Incoming and outgoing are related to an actual present outgoing neighbour. The normalized pattern type agrees with decide(outgoing=incoming).',
'CoveredIntegratedLowerStatement':'J is positive when converting ratio<=1/c to I>=cJ; use I2>=c in the two-neighbour case.',
'BetaPrimeAnalyticStatement':'c>0 and I0>=1 supply positivity of both mean arguments even though It>0 is not separately listed.',
'BetaAnalyticStatement':'c>=3/5, Jt>=116/125, and J0>=1 imply all four mean arguments are positive.',
'AlphaAnalyticStatement':'Preserve the same Jt,J0 subtraction when lowering I, then lower the J arguments using monotonicity of G_c.',
'UStepMomentStatement':'k=0 has zero inserted first moment; k=3 has total degree four, exactly the maximum permitted.',
'DStepMomentStatement':'The explicit k<=1 premise excludes the false two-bond mass-free D identity.',
'TraceDynamicsStatement':'A D removal destroys only the outgoing present bond; this is the key fact making trails of initial bonds valid in the evolving trace.',
'TraceCoefficientStatement':'ND counts evolving D departures. Positive coefficient excludes visits to removed departure sites.',
'TraceTelescopeStatement':'Use positive normalizers at every prefix and include the zero-step empty product.',
'CoordinateStepStatement':'The target degree restriction counts original legs and is not replaced by its present degree alone.',
'PairExpansionStatement':'Use insert v S as the stopping set. Sum lengths through card(bonds), including the empty class at length zero.',
'PairTerminalFactorStatement':'A D target loses its sole arrival bond and is isolated, yielding 3/5 rather than the U value one.',
'PairDegreeStatement':'At a terminal self-pair the same site receives two insertions; factorDegree then has at most two remaining factors.',
'ProductExposureStatement':'c_i<=1 and x_i>=1 are both used. Empty products and sums give the exact zero-step statement.',
'OnePointPointwiseStatement':'The maximum is pointwise before summing. Each exceptional U departure costs 12/5, and the exception positions are unrestricted.',
'OnePointSumStatement':'The absent virtual incoming bond enforces forbidden initial reversal in H2; do not enlarge to unrestricted first-step trails.',
'NormalizeStartStatement':'Partition equality holds for every observable and both pin choices because only a flag to an X site changes.',
'KeptInvariantStatement':'At zero length an initially D start retains two kept flags. Only positive-length arrivals leave a live D with one.',
'RemovedClosureStatement':'The hypothesis excludes removing a protected terminal. The removed centre remains inside original G.',
'CoveredClosureStatement':'V2 is essential here: a U boundary corner keeps neighbours intersect G, while outside directions are original leg slots.',
'PairClosureStatement':'The response endpoints are distinct nonremoved present neighbours; their D present degree drops to at most one after deletion.',
'TerminalDefectStatement':'No ordinary-domain membership after removing the protected e is claimed. Its law and original legs survive.',
'SecondStartStatement':'v outside S is explicit; the paper gives a counterexample without it. The target e has lost one arrival bond.',
'TerminalExceptionLocationStatement':'Only 0<distance<=2 is asserted for exceptional U departures; a departure at protected e is prohibited.',
'UDepartureInjectiveStatement':'Two distinct indices cannot both have status U at the same evolving site. Initially D sites need no special first-visit assertion.',
'DiamondTwelveStatement':'Use taxicab distance and the punctured ball, not a 24-site sup-distance shell.',
'TerminalExceptionCountStatement':'Inject exceptional U indices into the twelve sites, using U-departure uniqueness rather than bounding all revisits.',
'KernelOrderingStatement':'Permutation and Nodup do not require the score comparator to satisfy a linear-order law. Zero rewards have a separate branch.',
'KernelPositivityStatement':'A response pair is a powersetCard 2 element, not an ordered double count; every table coefficient is positive.',
'ShiftGeometryStatement':'pairShift is the maximum over the pair of minimum distances to the original endpoints. n=0 has no departure index.',
'KernelSupportStatement':'The finite cutoff range(n+2) includes s=n+1. Strict n+1<s is the vanishing condition.',
'KernelRegroupStatement':'Regroup in ENNReal before any toReal conversion; theta>0 rules out vanishing zpow weights.',
'KernelLengthMajorantStatement':'At most n first visits each contribute total coefficient <=alpha-bar+2 beta-bar. A fixed entry is below this full reward.',
'MajorantFiniteStatement':'H2 has positive q. Thus q^2<theta gives q/sqrt(theta)<1 and theta>0, rather than only an absolute-value bound.',
'UnshiftedWitnessStatement':'Every finite H3 cutoff is needed; a finite numerical prefix alone is insufficient. n=0 is exactly zero.',
'ShiftPowerIncrementStatement':'s=0 has increment zero. Negative powers use positive bases b,theta; s<=n+1 justifies the common exponent bound.',
'TransportChoiceStatement':'The minimum defining epsilon has two strictly positive arguments; B_*>0 uses CV>=1 and q>0.',
'WitnessPerturbationStatement':'The same dyadic h and orderings are used at theta=1 and theta<1. The row premise is concrete and local, not another leaf Prop.',
'ShiftedRowsRealStatement':'Finite entries plus positive h and positive theta weights justify real coefficient summability, not merely finite real tsums.',
'FiniteKernelTailDominationStatement':'F is any bounded nonnegative function with its bound explicit. A real tsum is used only after H2 row finiteness.',
'EnvelopeBoundsStatement':'The defining set contains zero and is bounded above by two; conditional completeness of real sSup is respected.',
'EnvelopeOrderStatement':'Negative d uses Int.toNat=0. Antitonicity is on all integers, including the clamped half-line.',
'ProtectedDistanceFiniteStatement':'G.Nonempty is essential. The conclusion gives a point of protectedSites and rules out infinity for every ambient x.',
'PairCanonicalGeometryStatement':'The chosen equivalence preserves both ordered endpoints and the designated centre, so a single symmetry works for every trail.',
'TraceExposureStatement':'The permutation covers all n departures; D log responses vanish. All x_i>=1 and pinned step upper bounds are explicit.',
'PairEnvelopeShiftStatement':'Depth loss is integer subtraction. A negative resulting depth is handled by the envelope constant extension, not Nat subtraction.',
'TraceKernelLengthStatement':'The pair has d>=1. Compare true D departures to lattice revisits, and use beta-prime only when one non-outgoing live neighbour remains.',
'ResidualTargetBoundStatement':'Both endpoints outside original S are explicit. The target e must be an S endpoint of the first stopped trail.',
'SecondTermBoundStatement':'Use the first-trail sum of maxima and a second-trail bound uniform in the first trail. Source exponent is exactly 2*d.',
'PairResponseSplitStatement':'The second endpoint is outside S, so target and boundary terminal classes are disjoint. The same trace coefficients are used for both pin choices.',
'RemovalEnvelopeStatement':'Y is a subset of G minus original S, and the common removed centre lies in Y. Nonempty endpoint data force finite protected distance.',
'RenewalActionStatement':'Real-row summability is explicit. B is existential and the zero function is covered; positivity follows termwise.',
'RenewalFiniteIterationStatement':'All integer depths are covered. Negative-source value two extends the inequality without needing an unproved fixed point.',
'RenewalRemainderStatement':'The remainder bound is unweighted and uniform on negative d; weighted norm control of F itself is not assumed.',
'RenewalSourceStatement':'The source is bounded by h theta^d on negative as well as nonnegative integers. zpow is used for d<0.',
'RenewalScalarLimitStatement':'a,b are nonnegative and 0<rho<1; k=0 is included and the geometric partial sum is empty then.'}
rows=[]
for mod in order:
    p=root/(mod+'.lean'); s=p.read_text()
    for m in re.finditer(r'^def (\w+Statement) : Prop :=',s,re.M):
        name=m.group(1); a=s.rfind('/--',0,m.start()); b=s.find('-/',a)
        doc=' '.join(s[a+3:b].split())
        rest=s[m.end():]; end=re.search(r'\n(?:/--|theorem |end |def |structure )',rest)
        statement='def '+name+' : Prop :='+rest[:end.start() if end else len(rest)].rstrip()
        paper=re.search(r'`([^`]+)`',doc)
        paper_label=paper.group(1) if paper else 'l:response'
        line=s[:m.start()].count('\n')+1
        difficulty='hard' if name in hard else ('easy' if name in easy else 'medium')
        cfg=config[mod]
        row={'lean_name':'AKLT.Blueprint.Rec.'+name,'module':'AKLT.Blueprint.Rec.'+mod,
             'source_file':str(p),'source_line':line,'paper_label':paper_label,
             'paper_locator':doc.split('. ')[0], 'difficulty':difficulty,
             'estimated_proof_lines':{'easy':90,'medium':220,'hard':380}[difficulty],
             'statement':statement,'dependencies':{'definitions':['AKLT.Defs.'+x if not x.startswith(('CoveredDepartureV2','Departure','PairData','PairSetup','normalizeStart','prefixNetwork','stoppedSum','uncoveredCount','firstLength','firstTerm','secondTerm','recursionSeries','sourceConstant','protectedDistance','shiftedLength','kernelMajorant','transport','RenewalRows','renewal','hmin','hmax','genericAmplitude')) else 'AKLT.Blueprint.Rec.'+x for x in cfg[0]],
               'library_lemmas':cfg[1]},
             'suggested_proof_route':doc+' '+cfg[2], 'donor_reuse_pointers':cfg[3],
             'trap_check':{'status':'reviewed; no remaining statement defect identified',
                'missing_premises':cfg[4], 'vacuity_and_degenerate_cases':cfg[5],
                'specific_check':special.get(name,'Exact rational arithmetic; no semantic approximation.'),
                'coercions':'Real expectations and rational coefficients are separated; cast rational inequalities before arithmetic. Nat/Int/ENat depth indices are explicit.',
                'finset_vs_fintype_sums':'DirectionWord n sums are Fintype sums. Actual domain trails are filtered Finsets; stoppedSum has a finite length cutoff. ENNReal infinite kernel sums are kept distinct from real renewal sums.',
                'nat_subtraction':'Depth subtraction is in Z. The only predecessor Nat subtraction belongs to wordIncoming under its nonzero-index branch. No positive depth is truncated to zero accidentally.',
                'division_by_zero':cfg[6],
                'instances':'autoImplicit=false project build checks every declaration. Fin n, PairType, Compass, active-site subtypes and the original-volume PinAssignment remain explicit; no Fintype instance is silently discarded.'},
             'status':('assembled' if name=='FirstTermBoundStatement' else 'proved') if name in proved else 'open'}
        if name in proved:
            row['proof_theorem']='AKLT.Blueprint.Rec.'+proved[name]
            row['proof_provenance'] = (
                'Assembly implication; remains within the blueprint agent scope.'
                if name=='FirstTermBoundStatement' else
                'Leaf proof completed before the author rule and retained under its explicit exception.')
        else:
            row['proof_assignment'] = {
                'first_attempt': 'A different, cheaper model selected by the orchestrator.',
                'current_agent_scope': 'Blueprint and assembly only; do not attempt this leaf proof.',
                'proof_status_at_cutover': 'Open; no proof attempt recorded by this agent.',
                'new_soundness_obligations': 'Any checker soundness needed later must be a separate exact closed open leaf.'}
        rows.append(row)
openrows=[r for r in rows if r['status']=='open']
# Dependency lists name only definitions and proved library facts, never another Rec leaf.
leafnames={r['lean_name'].split('.')[-1] for r in rows}
for r in openrows:
    assert not any(any(n in d for n in leafnames) for ds in r['dependencies'].values() for d in ds)
assert all(r['lean_name'].split('.')[-1] in special for r in openrows)
(out/'leaves.json').write_text(json.dumps(openrows,ensure_ascii=False,indent=2)+'\n')
(out/'nodes.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'nodes':len(rows),'open':len(openrows),'proved_or_assembled':len(rows)-len(openrows)},ensure_ascii=False))
