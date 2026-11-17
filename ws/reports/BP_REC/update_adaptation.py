from pathlib import Path
import json,re,hashlib,copy
out=Path('/home/ubuntu/aklt/reports/BP_REC')
root=Path('/home/ubuntu/aklt/wt/BP_REC/AKLT/Blueprint/Rec')
prefix='AKLT.Blueprint.Rec.'
oldleaves=json.loads((out/'leaves-pre-adaptation.json').read_text())
oldnodes=json.loads((out/'nodes-pre-adaptation.json').read_text())
base=json.loads((out/'adaptation-baseline.json').read_text())
for name,expected in base['frozen_files_sha256'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected, 'Frozen source changed: '+name
superseded={name:name+'V2' for name in [
    'LocalMixtureStatement','CoveredRatioStatement','CoveredIntegratedLowerStatement',
    'OnePointPointwiseStatement','OnePointSumStatement','CoveredClosureStatement',
    'PairClosureStatement','TerminalExceptionLocationStatement','TerminalExceptionCountStatement']}
reasons={
'LocalMixtureStatement':'Replace intersection/full-kept matching by shared internal-present-bond and one-sided tip matching.',
'CoveredRatioStatement':'Broaden the pointwise local comparison to the shared paper-scope matcher.',
'CoveredIntegratedLowerStatement':'Top.ResponseTypedStatementV2 requires the shared matcher rather than the frozen Rec-local predicate.',
'OnePointPointwiseStatement':'Count exceptions with the shared matcher; the new exception count can be smaller.',
'OnePointSumStatement':'Use the shared-matcher exception premise in the sum-of-maxima contract.',
'CoveredClosureStatement':'Conclude shared internal-bond coverage rather than the frozen local intersection predicate.',
'PairClosureStatement':'Expose the corrected non-arrival neighbour clause, broadening the old present-neighbour specialization.',
'TerminalExceptionLocationStatement':'Detect uncovered sites with shared present-bond matching.',
'TerminalExceptionCountStatement':'Use uncoveredCountV2 built from the shared matcher.'}
retarget_routes={
'TraceKernelLengthStatement':' Adaptation: implement using the repaired Top.ResponseTypedStatementV2, the non-arrival-only response-pair clause, and fixed short/long ordering scopes; the numerical conclusion of this frozen leaf is unchanged.',
'ResidualTargetBoundStatement':' Adaptation: use shared-matcher covering and twelve-exception bounds in the second expansion; the residual estimate itself is unchanged.',
'SecondTermBoundStatement':' Adaptation: use the shared-matcher one-point estimates while preserving the identical sourceConstant and original-S distances.',
'KernelOrderingStatement':' Adaptation: retain this true general permutation/Nodup helper. The new short/long leaves state the published ClosedTrail domain and exact within-type order.',
'PairResponseSplitStatement':' Adaptation: the finite expansion identity is matcher-independent and unchanged.',
'OnePointConstantStatement':' No change.'}
def annotate_old(row):
    row=copy.deepcopy(row);name=row['lean_name'].split('.')[-1]
    row['proof_status']=row.get('status','open')
    row['previous_status']=row.get('status','open')
    row['status']=row['adaptation_status']='superseded' if name in superseded else 'kept'
    row['frozen_source_sha256']=base['frozen_files_sha256'][Path(row['source_file']).name]
    row['superseded_by']=[prefix+superseded[name]] if name in superseded else []
    row['adaptation_reason']=reasons.get(name,'The closed mathematical statement is unchanged by the repaired layer and remains true.')
    row['in_active_proof_queue']=row['proof_status']=='open' and name not in superseded
    row['suggested_proof_route']+=retarget_routes.get(name,'')
    return row
oldleaves=[annotate_old(x) for x in oldleaves]
oldnodes=[annotate_old(x) for x in oldnodes]

# Every entry below names only definitions and already proved library APIs as dependencies.
# It never grants a Rec leaf as a hypothesis to another leaf.
newinfo={
'LocalMixtureStatementV2':dict(difficulty='hard',lines=380,old='LocalMixtureStatement',
 defs=['AKLT.Defs.CoveredDepartureV2','AKLT.Defs.PatternData.InternalPresent','AKLT.Defs.patternCurrent','AKLT.Defs.patternNext',prefix+'Departure'],
 libs=['Finset.sum_congr','Finset.sum_mul','Finset.mul_sum','Finset.prod_mul_distrib'],
 route='Disintegrate finite outside spins. On each tip keep every actual internal bond, and assign effective mean zero to every covering-only tip bond. Replace actual tip laws by covering U laws using the full 3/5 mean ball. Resolve both corner slots independently and absorb the common positive normalizers in the same nonnegative mixture weights.',
 trap='Shared matching constrains only internal present bonds, not external directions still inside G or flags to X sites. The one-sided tip condition forbids losing an actual tip bond; adding one is handled by mean zero. No claim that the shared matcher implies the stricter frozen local matcher is made.'),
'CoveredRatioStatementV2':dict(difficulty='medium',lines=180,old='CoveredRatioStatement',
 defs=['AKLT.Defs.CoveredDepartureV2','AKLT.Defs.LocalPatternBound','AKLT.Defs.stepRatio',prefix+'Departure'],
 libs=['Finset.sum_le_sum','mul_le_mul_of_nonneg_left','div_le_iff₀'],
 route='Apply the H1 pointwise inequality to the shared-cover local representation, average with the common nonnegative weights, and divide only after establishing positive current and next normalizers.',
 trap='The actual outgoing neighbour is present by Departure; external slot fields are not assumed to be actual bonds. H1 thresholds are positive and at most one.'),
'CoveredIntegratedLowerStatementV2':dict(difficulty='medium',lines=200,old='CoveredIntegratedLowerStatement',
 defs=['AKLT.Defs.CoveredDepartureV2','AKLT.Defs.responseI','AKLT.Defs.responseJ',prefix+'responseI₂','AKLT.Defs.stepRatio'],
 libs=['le_div_iff₀','div_le_iff₀','mul_le_mul_of_nonneg_left'],
 route='Integrate the departure to write the true step ratio as J/I or 1/I2. Use the shared-cover H1 partition inequality and positive J to obtain the displayed lower bound. Keep the same localThreshold Boolean and the same canonical I,J definitions.',
 trap='The needed premise is the shared matcher, explicitly qualified AKLT.Defs.CoveredDepartureV2. J>0 is justified before multiplying through a ratio. The exact two- and three-neighbour distinctness premises remain.'),
'LegacyCoverComparisonStatementV2':dict(difficulty='medium',lines=220,old=None,
 defs=[prefix+'CoveredDepartureV2','AKLT.Defs.CoveredDepartureV2','AKLT.Defs.PatternData.InternalPresent','AKLT.Defs.Network.Present','AKLT.Defs.normalizeRotation'],
 libs=['Finset.mem_inter','Finset.mem_image','Finset.mem_sdiff'],
 route='Keep the old witnessing pattern and status agreement. For active non-tips the old kept-set equality after intersection with G gives both directions of each internal present-bond equivalence. At tips only actual-to-cover presence is required. Handle the unoriented positive orientation by the symmetric InternalPresent predicate.',
 trap='This is only frozen-local-cover implies shared-cover. The converse is not stated and would impose forbidden external kept-flag constraints. Auxiliary supplies status X outside G and kept subsets inside G.'),
'BoundaryExampleCoveredStatementV2':dict(difficulty='easy',lines=70,old=None,
 defs=[prefix+'boundaryExampleD',prefix+'boundaryExamplePattern',prefix+'normalizeStart','AKLT.Defs.CoveredDepartureV2'],
 libs=['Finset.mem_image','Finset.mem_inter'],
 route='Use the existing concrete pattern as witness and check the shared non-tip status and internal bond conditions on the finite template. This new shared-scope statement must receive a cheaper-model first attempt; the retained kernel example proves only the old local predicate.',
 trap='No theorem about shared coverage is inferred merely by reusing the name V2: the retained Rec-local and shared Defs predicates are distinct declarations.'),
'OnePointPointwiseStatementV2':dict(difficulty='medium',lines=260,old='OnePointPointwiseStatement',
 defs=[prefix+'uncoveredCountV2','AKLT.Defs.CoveredDepartureV2','AKLT.Defs.traceCoefficient','AKLT.Defs.traceRatio','AKLT.Defs.trailWeight'],
 libs=['Finset.prod_le_prod','max_le','mul_le_mul_of_nonneg_left'],
 route='Compare each evolving departure coefficient times each pin-choice ratio to its lattice weight. Covered U steps use the shared local comparison, uncovered U steps pay 12/5, and D revisits pay exactly 1/5. Multiply and telescope, then take the common maximum.',
 trap='The maximum is taken before summing. The absent designated incoming bond is retained, and at most twelve uncovered U departures may occur at arbitrary positions.'),
'OnePointSumStatementV2':dict(difficulty='medium',lines=240,old='OnePointSumStatement',
 defs=[prefix+'uncoveredCountV2',prefix+'onePointSum',prefix+'onePointConstant','AKLT.Defs.OpenTrailBound','AKLT.Defs.StoppedNetworkTrail'],
 libs=['Finset.sum_le_sum','hasSum_geometric_of_lt_one','Finset.sum_congr'],
 route='Group the finite stopped trail sum by length and inject each group into H2 trails with the identical incoming direction. Use the shared-cover pointwise comparison and sum the q-geometric tail from the finite original protected distance.',
 trap='H2 contains CV>=1 and 0<q<1. The protected set is the original S(G); do not use distances to holes. Empty trail families and the length-zero convention remain explicit.'),
'CoveredClosureStatementV2':dict(difficulty='hard',lines=360,old='CoveredClosureStatement',
 defs=[prefix+'PairSetup',prefix+'prefixNetwork','AKLT.Defs.CoveredDepartureV2','AKLT.Defs.PatternData.InternalPresent'],
 libs=['Finset.mem_erase','Finset.mem_inter','Finset.mem_sdiff'],
 route='Run the frozen kept/status prefix invariant. At a live U departure the arrival bond is absent, remaining non-tip internal bonds match by active consistency, and every actual tip bond is kept in the cover. External flags to removed or outside-template sites are ignored, exactly as required by the shared predicate.',
 trap='Do not conclude ordinary-domain membership for the live pre-step network. Shared matching, not Rec-local intersection matching, is the conclusion. The whole radius-two template lies inside original G at an interior departure.'),
'PairClosureStatementV2':dict(difficulty='medium',lines=220,old='PairClosureStatement',
 defs=[prefix+'nonarrivalNeighboursV2',prefix+'PairSetup',prefix+'prefixNetwork','AKLT.Defs.Network.ResponsePair','AKLT.Defs.removeSite','AKLT.Defs.responsePairType'],
 libs=['Finset.mem_inter','Finset.mem_erase','Finset.mem_image'],
 route='For distinct active non-arrival neighbours of the live U site, consistency makes both passage bonds present. Removing the live point produces an ordinary domain, the distance-two type is B or C, and any D endpoint loses its passage bond so has present degree at most one.',
 trap='The incoming/arrival neighbour is explicitly erased. It can be D with TWO remaining present bonds, so the unrestricted nonremoved-neighbour assertion is not used. The old present-neighbour specialization remains true.'),
'TerminalExceptionLocationStatementV2':dict(difficulty='hard',lines=360,old='TerminalExceptionLocationStatement',
 defs=['AKLT.Defs.CoveredDepartureV2',prefix+'PairSetup',prefix+'normalizeStart',prefix+'prefixNetwork','AKLT.Defs.latticeDist'],
 libs=['Finset.mem_erase','Finset.mem_inter'],
 route='Repeat the prefix invariant for the second trace while holding the first protected endpoint e as the only fixed defect. A U departure farther than two from e has matching internal non-tip data; actual missing external factors and tip data are covered. Hence every shared-cover failure lies in the punctured radius-two diamond.',
 trap='v outside original S is required. No second departure is at protected e, no original leg is removed, and no claim is made that the whole terminal auxiliary network is ordinary.'),
'TerminalExceptionCountStatementV2':dict(difficulty='medium',lines=180,old='TerminalExceptionCountStatement',
 defs=[prefix+'uncoveredCountV2',prefix+'PairSetup',prefix+'normalizeStart','AKLT.Defs.latticeDist','AKLT.Defs.square'],
 libs=['Finset.card_le_card','Finset.card_image_iff'],
 route='Inject indices of uncovered U departures into their distinct sites in the punctured radius-two diamond around e. U status can depart only once at a site. The diamond has four plus eight sites, giving twelve.',
 trap='Count U departures rather than all visits. Exceptions can occur anywhere in the second trail; the second endpoint remains outside original S.'),
'ShortKernelOrderingStatementV2':dict(difficulty='medium',lines=190,old=None,
 defs=['AKLT.Defs.ClosedTrail','AKLT.Defs.kernelOrdering','AKLT.Defs.firstVisitList','AKLT.Defs.shortOrderLE'],
 libs=['List.pairwise_mergeSort','List.mergeSort_perm'],
 route='At n<=12 unfold the short branch. Establish transitivity and totality of the rational score comparison, with a separate zero-reward infinity branch and increasing-index ties, then use merge-sort pairwise correctness.',
 trap='The domain is the canonical u-to-v first-hit class ClosedTrail X, not cycles. Length twelve is short. No assertion equates short ordering with the phase path ordering.'),
'LongKernelOrderingStatementV2':dict(difficulty='easy',lines=90,old=None,
 defs=['AKLT.Defs.ClosedTrail','AKLT.Defs.kernelOrdering','AKLT.Defs.longOrdering','AKLT.Defs.firstVisitList','AKLT.Defs.wordStraight'],
 libs=['List.pairwise_filter','List.pairwise_lt_finRange'],
 route='For n>12 unfold the long branch. Both type lists filter the increasing finRange list, so strict path-index order is retained. Identify their concatenation with the existing longOrdering definition.',
 trap='Strict n>12 is required for kernel/phase order agreement. Both straight and turn subsequences retain increasing path index; type order alone is insufficient.'),
'StoppedQuotientSumStatementV2':dict(difficulty='medium',lines=300,old=None,
 defs=[prefix+'rawStoppedOperatorV2',prefix+'quotientStoppedOperatorV2','AKLT.Defs.MemoryQuotient.Correct','AKLT.Defs.finiteOperatorSum','AKLT.Defs.RawWindow'],
 libs=['Finset.sum_congr','Finset.mul_sum','Finset.sum_mul'],
 route='Induct on finite iterates, using raw-successor validity, the direction/kind/successor clauses of Q.Correct, and arrival-independent revisit coefficients. At terminal branches use the indicator pullback; at horizon zero use the reward pullback. Sum the iterate equalities over the finite horizon. Gen/Bellman/Quotient.lean Automaton.stopped_pullback supplies the nonnegative analogue; this rational equality still needs its own bridge or direct finite-sum proof.',
 trap='BOTH raw terminal indicator and raw terminal reward must be pullbacks. A raw reward distinguishing windows in the same quotient class is excluded even at horizon zero. Memory m>=1 is retained; p=0 and horizon R=0 are allowed.')
}
new=[]
for path in sorted(root.glob('NodesV2*.lean')):
    s=path.read_text()
    for match in re.finditer(r'^def (\w+StatementV2) : Prop :=',s,re.M):
        name=match.group(1);info=newinfo[name]
        a=s.rfind('/--',0,match.start());b=s.find('-/',a);doc=' '.join(s[a+3:b].split())
        tail=s[match.end():];stop=re.search(r'\n(?:/--|theorem |end |def |structure )',tail)
        statement='def '+name+' : Prop :='+tail[:stop.start() if stop else len(tail)].rstrip()
        label=re.search(r'`([^`]+)`',doc).group(1)
        row={'lean_name':prefix+name,'module':prefix+path.stem,'source_file':str(path),
          'source_line':s[:match.start()].count('\n')+1,'paper_label':label,'paper_locator':doc.split('. ')[0],
          'difficulty':info['difficulty'],'estimated_proof_lines':info['lines'],'statement':statement,
          'status':'new','adaptation_status':'new','proof_status':'open','in_active_proof_queue':True,
          'supersedes':[prefix+info['old']] if info['old'] else [],
          'dependencies':{'definitions':info['defs'],'library_lemmas':info['libs']},
          'suggested_proof_route':info['route'],
          'donor_reuse_pointers':('AKLT/Gen/Bellman/Quotient.lean: AKLT.Gen.Bellman.Automaton.stopped_pullback is an ENNReal analogue, not a direct theorem about arbitrary signed rational coefficients.' if name=='StoppedQuotientSumStatementV2' else 'The campaign reuse map has no full donor for this model-specific statement; use the named frozen definitions and Mathlib APIs.'),
          'owner_handoff':'BP_H3M may reuse this explicit terminal-data contract; it is not assumed by Rec or by importing this file.' if name=='StoppedQuotientSumStatementV2' else 'BP_REC',
          'proof_assignment':{'first_attempt':'A different, cheaper model selected by the orchestrator.','current_agent_scope':'Blueprint and assembly only; no leaf proof attempted.'},
          'trap_check':{'status':'reviewed; explicit hypotheses retained; proof open',
            'missing_premises':info['trap'],
            'specific_check':info['trap'],
            'vacuity_and_degenerate_cases':'Admissible active starts rule out empty G. Empty finite index families and zero rewards have their explicit conventions. The quotient equality allows p=0 and R=0; the ordering leaves range only over actual ClosedTrail X instances.',
            'coercions':'Keep original G and PinAssignment G. Use exact rational coefficients and explicit casts in real inequalities; no frame-alphabet restriction is introduced.',
            'finset_vs_fintype_sums':'DirectionWord n and finite phase sums are Fintype sums; stoppedNetworkTrails and index filters are Finsets. Finite operator sums use range(R+1); no divergent real tsum is introduced.',
            'nat_subtraction':'Depth losses remain integer subtraction in frozen definitions. wordIncoming predecessor subtraction retains its nonzero-index guard. The short/long boundary is <=12 versus >12.',
            'division_by_zero':'Current/next and tip normalizers are positive before dividing. H2 supplies 0<q<1. Short ordering has a separate zero-reward key branch. The stopped quotient equality requires no division or positivity of its rational weights.',
            'instances':'The full new module graph was kernel-checked with autoImplicit=false and relaxedAutoImplicit=false; Fin n, all finite phase/state indices and original-volume pins remain explicit.'}}
        new.append(row)
assert len(new)==14 and len(newinfo)==14
new.sort(key=lambda r:(list(newinfo).index(r['lean_name'].split('.')[-1])))
all_leaf_names={r['lean_name'].split('.')[-1] for r in [*oldnodes,*new]}
for row in new:
    name=row['lean_name'].split('.')[-1]
    assert name.endswith('V2')
    assert not any(re.search(r'\b'+re.escape(n)+r'\b',row['statement']) for n in all_leaf_names if n!=name)
for row in [*oldleaves,*new]:
    for group in row['dependencies'].values():
        assert not any(any(n in entry for n in all_leaf_names) for entry in group)
manifest=[*oldleaves,*new]
(out/'leaves.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
(out/'nodes.json').write_text(json.dumps([*oldnodes,*new],ensure_ascii=False,indent=2)+'\n')
(out/'leaves-new-v2.json').write_text(json.dumps(new,ensure_ascii=False,indent=2)+'\n')

asm=(root/'AssemblyV2.lean').read_text()
assembly_names=re.findall(r'^theorem (\w+)',asm,re.M)
assert len(assembly_names)==11
assert not any(re.search(r'^theorem ',p.read_text(),re.M) for p in root.glob('NodesV2*.lean'))
audit=(out/'adaptation-AKLT.Blueprint.Rec.AuditV2.log').read_text()
entries=re.findall(r"'AKLT.Blueprint.Rec.(\w+)' depends on axioms: \[([^\]]*)\]",audit)
assert {x for x,_ in entries}==set(assembly_names)
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(x.split(', '))<=allowed for _,x in entries)
(out/'adaptation-axioms.log').write_text((out/'adaptation-AKLT.Blueprint.Rec.Audit.log').read_text()+audit)
summary={'frozen_files_preserved':13,'old_open_kept':79,'old_open_superseded':9,
 'new_open_leaves':14,'active_open_leaves':93,'total_manifest_entries':102,
 'new_assembly_theorems':assembly_names,'axioms_allowed':True,'new_leaf_proofs':0,
 'old_to_new':{prefix+k:prefix+v for k,v in superseded.items()},
 'build':json.loads((out/'adaptation-build.json').read_text())}
(out/'adaptation-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
policy=json.loads((out/'proof-policy.json').read_text())
policy['adaptation']={'frozen_source_baseline':'adaptation-baseline.json','new_leaf_files':sorted(p.name for p in root.glob('NodesV2*.lean')),'new_leaf_proof_attempts':[], 'new_assembly_theorems':assembly_names,'first_attempt_rule':'All new and kept open leaf proofs first go to a different, cheaper model.'}
(out/'proof-policy.json').write_text(json.dumps(policy,ensure_ascii=False,indent=2)+'\n')

# Current report: the old detailed delivery remains available byte-for-byte as a historical report.
lines=['STATUS: COMPLETE','','| Leaf / node | Paper label | Difficulty | Adaptation | Proof state |','|---|---|---|---|---|']
for row in [*oldnodes,*new]:
    name=row['lean_name'].split('.')[-1]
    lines.append(f"| [{name}]({row['source_file']}:{row['source_line']}) | `{row['paper_label']}` | {row['difficulty']} | {row['adaptation_status']} | {row['proof_status']} |")
lines += ['', '## Adaptation', '',
'Adapted to the repaired layer merged by the orchestrator and the findings in [ARCH_0/stmt-fix.md](/home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md), [REF2_5](/home/ubuntu/aklt/reports/REF2_5/report.md), [REF2_6](/home/ubuntu/aklt/reports/REF2_6/report.md) and [REF2_7](/home/ubuntu/aklt/reports/REF2_7/report.md). All thirteen existing Rec Lean files are byte-identical to the post-merge baseline, including every old leaf, definition, proof, assembly and audit. Every source addition is a new file. Hash evidence is in [adaptation-baseline.json]('+str(out/'adaptation-baseline.json')+').', '',
'The updated manifest contains all 88 old open entries, marked `kept` (79) or `superseded` (9), plus 14 new open leaves. Thus 93 tasks remain in the active proof queue; nine additional historical true statements are retained as superseded records. `proof_status` is separate from `adaptation_status` and `status`; every entry in `leaves.json` remains unproved. The three retained rational leaf proofs and the existing assembled intermediate remain in `nodes.json` and the pre-rule proof inventory. Superseded means replaced in the paper-facing blueprint, never found false or edited.', '',
'| Old target | Current target | Changed or added leaves |','|---|---|---|',
'| `Top.ResponseStatement` | `Top.ResponseStatement` (same contract) | None; the frozen uniform response leaves are reused. |',
'| `Top.LogMeanBoundsStatement` | `Top.LogMeanBoundsStatement` (same contract) | None; the frozen analytic leaves and retained exact rational checks are reused. |',
'| `Top.ResponseTypedStatement`; frozen `Rec.ResponseTypedStatementV2` | `Top.ResponseTypedStatementV2` | `CoveredIntegratedLowerStatementV2`; supporting `LocalMixtureStatementV2`, `CoveredRatioStatementV2`, `LegacyCoverComparisonStatementV2`, and `BoundaryExampleCoveredStatementV2`. |',
'| `Top.MThetaStatement` | `Top.MThetaStatement` (same contract) | No change to the numerical conclusion or its leaves. New `ShortKernelOrderingStatementV2` and `LongKernelOrderingStatementV2` make the paper ordering scope explicit. |',
'| `Top.RecStatement` | `Top.RecStatement`, still required by `mainV2_of_partsV2` | New covering, non-arrival pair and exception/one-point refinement leaves listed below. Matcher-independent finite T1/T2, envelope, summability and renewal conclusions are kept. |',
'| Old local matcher and closure/one-point refinements | Shared `Defs.CoveredDepartureV2` | `CoveredClosureStatementV2`, `PairClosureStatementV2`, `TerminalExceptionLocationStatementV2`, `TerminalExceptionCountStatementV2`, `OnePointPointwiseStatementV2`, `OnePointSumStatementV2`. |',
'| Phase-to-kernel and stopped quotient handoffs | Length-qualified `LongPhaseKernelStatementV2`; explicit `StoppedQuotientSumStatementV2` | Long ordering is a new leaf; the phase-to-kernel conversion is an assembly from BP_H3M\'s `Top.PhaseExpansionStatementV2`. Terminal indicator and reward pullbacks are explicit in the new open handoff. |', '',
'### Shared matcher and unchanged conclusions', '',
'The shared `AKLT.Defs.CoveredDepartureV2` matches internal present bonds between non-tips, not whole kept sets or kept sets intersected with G. It ignores external directions even when they remain inside G, and ignores inactive flags toward removed sites. At covering tips it preserves every actual bond and permits an added cover bond with zero effective mean. Every new use is fully qualified to avoid confusion with the frozen, stricter `AKLT.Blueprint.Rec.CoveredDepartureV2`.', '',
'The frozen local proposal remains a sufficient specialization and is not used as the full shared scope. Its comparison to the shared predicate is a new open leaf, not a newly proved bridge. The old matcher diagnostic proofs keep their exact original meanings. Shared acceptance of the concrete boundary example is likewise an open V2 leaf.', '',
'The core assembly has 41 immediate closed leaf inputs, as before: the new integrated lower-bound leaf replaces the old one, and all other numeric/recursion conclusions retain their definitions. The retained `TraceKernelLengthStatement`, `ResidualTargetBoundStatement` and `SecondTermBoundStatement` are matcher-independent estimates; their manifest proof routes now explicitly use the shared typed statement and corrected refinements. No implication from shared matching to the stricter local matcher is assumed.', '',
'### Referee findings and lane boundaries', '',
'1. **Closure pairs (REF2_5 finding 1):** `nonarrivalNeighboursV2` explicitly erases the arrival site and intersects with active sites. `PairClosureStatementV2` uses pairs from this set. An arrival D endpoint may keep two present bonds after deletion and is not admitted. The frozen leaf only used present neighbours in the live pre-step network, which already excludes the deleted arrival bond; it remains true and byte-identical.',
'2. **Ordering domain (REF2_5 finding 2):** the new ordering leaves quantify `ClosedTrail X w`, the defined canonical u-to-v first-hit class with distinct endpoints. They do not require graph cycles. The short branch includes n=12 and preserves the rational key, zero-reward infinity case and path-index tie break.',
'3. **Within-type order and phase qualification (REF2_6 finding 2):** the long branch has n>12 and strict increasing path index within both type subsequences. `longPhaseKernel_of_partsV2` converts the phase algebra to `closedContribution` only under that long-trail hypothesis. Short hits are never evaluated with the phase ordering. The phase algebra itself remains BP_H3M\'s closed Top input.',
'4. **Stopped quotient data (REF2_6 finding 3):** the new raw and quotient operators permit state-dependent stopping data. Their exact finite-sum handoff requires both the raw terminal indicator and raw reward to be pullbacks through Q.project. The zero-horizon reward counterexample is therefore excluded explicitly. This is an open handoff available to BP_H3M, not an automatically discharged certificate fact.',
'5. **Unresolved H1/H3 witnesses (REF2_6 critical finding):** the new main assembly requires `Top.InputsStatementV2` as a closed input, including the explicit H1 finite-data, designated automaton and corrected stationary checks. No archive existence or passing check is inferred from enumeration counts, data literals, the referee\'s native H2 verifier or imported definitions. These numerical obligations remain with their certificate lanes.',
'6. **Appendix D (REF2_7):** the referee found no defect. ARCH_0\'s real-polynomial/operator and finite-data repairs are owned by BP_H1M/CERT_H1. Rec retains its exact H1 semantic input and the same degree-four moments; no operator leaf is silently claimed proved here.', '',
'### New source files', '',
'| File | Contents |','|---|---|']
roles={'NodesV2Local.lean':'Shared-cover local transfer, typed lower bounds, legacy comparison and diagnostic statements.',
'NodesV2Walk.lean':'Shared-matcher uncoveredCountV2 and the two one-point statements.',
'NodesV2Closure.lean':'Shared coverage, explicit non-arrival response pairs and terminal exception statements.',
'NodesV2Ordering.lean':'Short rational-key order and long path order on the canonical kernel-trail domain.',
'NodesV2Handoff.lean':'Generalized stopped raw/quotient operators and the terminal-data-pullback leaf.',
'AssemblyV2.lean':'Eleven proved assemblies for the repaired interfaces, ordering/phase handoff and repaired main assembly.',
'AuditV2.lean':'Axiom reports for every new assembly theorem.',
'AllV2.lean':'Single import of the adaptation and audit.'}
for name,role in roles.items():lines.append(f'| [{name}]({root/name}) | {role} |')
lines += ['', '### Kept and superseded leaves', '',
'Every old record is individually marked in [leaves.json]('+str(out/'leaves.json')+'). The nine replacements are:', '',
'| Frozen old leaf | New leaf | Reason |','|---|---|---|']
for name,newname in superseded.items():lines.append(f'| `{name}` | `{newname}` | {reasons[name]} |')
lines += ['', '### New open statements', '',
'All fourteen statements below are unproved. Their full dependency lists, proof routes, difficulty and trap checks are in [leaves-new-v2.json]('+str(out/'leaves-new-v2.json')+') and the combined manifest.', '', '```lean']
for row in new:lines.extend([row['statement'],''])
lines += ['```','', '### New assembly declarations', '',
'All hypotheses of the following assemblies are closed Props. `TypedLeavesV2` changes only its local lower-bound field. `AssemblyLeavesV2` otherwise reuses the frozen response, logarithmic-mean, Mtheta, finite T1/T2 and renewal bundles.', '', '```lean']
for match in re.finditer(r'^theorem (\w+)',asm,re.M):
    end=asm.find(':=',match.start());lines.extend([asm[match.start():end].rstrip(),''])
lines += ['```','', '### Trap check and proof policy', '',
'All existing eight-field trap checks are retained. Every new leaf has the usual separate checks for explicit premises, vacuity/degeneracy, coercions, sums, natural subtraction, divisions, instance arguments and the specific scope change. The decisive checks are:', '',
'| New leaf | Specific check |','|---|---|']
for row in new:lines.append(f"| `{row['lean_name'].split('.')[-1]}` | {row['trap_check']['specific_check']} |")
lines += ['',
'All original pins remain `PinAssignment G`, distances remain to original S(G), and auxiliary terminal networks are not coerced to ordinary domains. D starts still have at most one present bond; both endpoints are outside S in the second expansion. Exact coefficients, true revisit weight 1/5, twelve exceptions, source constant, fixed dyadic h and prescribed kernel orderings are unchanged. The stopped quotient lemma is a rational finite-sum equality and assumes no stochastic normalization or positivity of its signed weights. Weighted kernel sums still use ENNReal until the frozen finiteness/real-row bridges apply.', '',
'No leaf proof was written in this adaptation, including the easy ordering and diagnostic facts. Every active old/new open task has its first attempt assigned to a different, cheaper model. The eleven pre-rule non-assembly proofs are retained and inventoried in [proof-policy.json]('+str(out/'proof-policy.json')+'); the ten old assemblies remain unchanged. The eleven new theorems are all in AssemblyV2.lean and are assembly implications. No new checker soundness result was introduced or proved.', '',
'### Retained pre-rule proof inventory', '',
'These eleven non-assembly proofs were written before the author rule and remain byte-identical. The three named leaf proofs are crudeRational, logRationalRows and typedCrudeRows; the other eight entries are retained helpers or diagnostics. No cheaper-model first attempt is claimed for these pre-rule proofs.', '',
'`crudeRational`, `logRationalRows`, `typedCrudeRows`, `reciprocalLogMean_one`, `witness_positive`, `kernelRho_pos`, `traceCoefficient_singleton`, `coveredDeparture_to_v2`, `envelope_le_of_pair_bounds`, `boundaryExample_not_old_covered`, `boundaryExample_v2_covered`.', '',
'### Build and axiom audit', '',
'The build recompiled the relevant merged statement dependency graph and all frozen Rec modules, then checked the eight new modules. It used the pinned Lake environment, at most two Lean processes, explicit autoImplicit=false and relaxedAutoImplicit=false, and an isolated olean root under the assigned report directory. It generated no C for the 3.2 MB designated automaton literal, changed no package or frozen source, and did not build Mathlib.', '',
'```bash', 'PATH="$HOME/.elan/bin:$PATH" lake env python3 /home/ubuntu/aklt/reports/BP_REC/build_adaptation.py AKLT.Blueprint.Rec.AllV2', '```', '',
f"The new eight-module build passed in {summary['build']['wall_seconds']} seconds; [adaptation-build.json]({out/'adaptation-build.json'}) records commands, module timings and the parallel limit. Logs: [new build]({out/'adaptation-build.log'}), [merged-layer/frozen rebuild]({out/'adaptation-base-build.log'}).", '',
'All definition and library names in the new manifest were also checked by Lean: [adaptation-dependencies-check.log]('+str(out/'adaptation-dependencies-check.log')+'). Constraint/manifest verification is recorded in [adaptation-validation.json]('+str(out/'adaptation-validation.json')+').', '',
'Every new assembly axiom report is:', '', '```text',audit.rstrip(),'```','',
'The twenty-one retained exported theorem audits also passed against the merged layer. The combined [adaptation-axioms.log]('+str(out/'adaptation-axioms.log')+') contains all thirty-two reports; only propext, Classical.choice and Quot.sound occur. [adaptation-summary.json]('+str(out/'adaptation-summary.json')+') records the counts and old-to-new map.', '',
'### Preserved prior delivery', '',
'The original detailed node descriptions, proof inventory, all old theorem signatures, trap checks and earlier report are preserved in [report-pre-adaptation.md]('+str(out/'report-pre-adaptation.md')+'). Earlier claims about the proposed local V2 refer to the frozen Rec-local specialization and are superseded for the full published scope by the shared matcher described above. No legacy declaration has been retargeted by changing its body.', '',
'## ORCH-SUMMARY',
'Adaptation complete: 8 new Lean files; all 13 existing Rec Lean files preserved byte-for-byte.',
'Leaves: 79 old open kept, 9 old open superseded, 14 new open; active proof queue 93.',
'New nodes have V2-suffixed names and are only in NodesV2*.lean; no leaf proof was added.',
'Eleven new assembly theorems compile and use only the three allowed axioms; all 21 retained theorem audits pass.',
'Targets: Response and LogMean unchanged; typed target is shared Top.ResponseTypedStatementV2; MTheta and Rec unchanged.',
'mainV2_of_blueprintV2 connects the repaired InputsStatementV2 and Rec to Top.mainV2_of_partsV2.',
'Fully qualify Defs.CoveredDepartureV2: the frozen Rec-local name remains a stricter, different predicate.',
'Closure pairs now explicitly exclude arrival; short order has n<=12; phase-to-kernel conversion has n>12 and exact within-type path order.',
'StoppedQuotientSumStatementV2 explicitly requires terminal indicator AND reward pullbacks; available as an open BP_H3M handoff.',
'No H1/H3 numerical certificate or shared-matcher bridge was proved; InputsStatementV2 stays an explicit closed input.',
'New open names (namespace AKLT.Blueprint.Rec):']
for path in roles:
    names=[r['lean_name'].split('.')[-1] for r in new if Path(r['source_file']).name==path]
    if names:lines.append(path+': '+', '.join(names))
lines += ['Manifests include every old kept/superseded entry, exact new statements, routes, dependencies and trap checks.',
'All future leaf proofs first go to a different, cheaper model; coordinate the H3 handoff and remaining finite-data inputs with their owners.']
lines=lines[:lines.index('## ORCH-SUMMARY')]+[
'## ORCH-SUMMARY',
'Adaptation complete: 8 new files; all 13 existing Rec Lean files preserved byte-for-byte.',
'Leaves: 79 old open kept, 9 old open superseded, 14 new open; active queue 93; no new leaf proofs.',
'All 11 new assemblies and 21 retained theorem audits pass with only the three allowed axioms.',
'Shared Top.ResponseTypedStatementV2 is the changed target; four targets and main\'s required RecStatement retain their contracts.',
'Non-arrival pairs, exact within-type order, n>12 phase-to-kernel conversion and both terminal-data pullbacks are explicit.',
'All active leaf proofs first go to a different, cheaper model; all names below are in AKLT.Blueprint.Rec.',
'Kept open names:']
for module in dict.fromkeys(row['module'] for row in oldleaves if row['in_active_proof_queue']):
    names=[row['lean_name'].split('.')[-1] for row in oldleaves if row['module']==module and row['in_active_proof_queue']]
    lines.append(module.split('.')[-1]+': '+', '.join(names))
lines.append('New open names:')
for module in dict.fromkeys(row['module'] for row in new):
    names=[row['lean_name'].split('.')[-1] for row in new if row['module']==module]
    lines.append(module.split('.')[-1]+': '+', '.join(names))
lines += ['mainV2_of_blueprintV2 keeps InputsStatementV2, CutMOS, MainW and uniqueness as closed external inputs; H1/H3 finite checks remain open.',
'StoppedQuotientSumStatementV2 is an explicit open BP_H3M handoff. Superseded exact names and replacements are in the manifest/report table.']
assert len(lines[lines.index('## ORCH-SUMMARY')+1:])<=25
(out/'report.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({k:summary[k] for k in ['old_open_kept','old_open_superseded','new_open_leaves','active_open_leaves','new_leaf_proofs']}))
