"""Adaptation artifacts only. Existing Lean sources and V1 report generators stay frozen."""
from pathlib import Path
import hashlib,json,re,shutil
root=Path('/home/ubuntu/aklt/wt/BP_H3M')
rep=Path('/home/ubuntu/aklt/reports/BP_H3M')
ns='AKLT.Blueprint.H3.'
frozen=json.loads((rep/'frozen-v1-files.json').read_text())
for name,digest in frozen.items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
old=json.loads((rep/'leaves-pre-adaptation.json').read_text())
assert len(old)==30
for row in old:
    row['status']='kept'
    row['adaptation_status']='kept'
    row['proof_status']='open'
    row['adaptation_reason']='Statement and source file are unchanged and truth-swept true. The V2 assembly reuses this V1 obligation through explicit centre-zero bridges; no replacement is required.'
    if row['lean_name'].rsplit('.',1)[1] in {'LocalCoefficientComparisonStatement','SuffixWordComparisonStatement','StationaryWordExpansionStatement','StationaryFreeEdgeStatement'}:
        row['adaptation_reason']='Kept intentionally as a legacy-operator supporting fact. The explicit off-centre, centre-zero, continuation, and certificate V2 bridges transfer its frozen assembled consequences; no equality on arbitrary functions is inferred.'
new=[]
def add(name,module,label,source,lines,difficulty,est,summary,deps,route,checks):
    text=(root/('AKLT/Blueprint/H3/'+module+'.lean')).read_text()
    match=re.search(r'^def '+name+r' : Prop :=\n(.*?)(?=\n\n(?:/--|end |namespace |theorem |def )|\Z)',text,re.M|re.S)
    assert match,name
    traps=dict(
        missing_premises='All mathematical assumptions are explicitly bound inside this closed Prop. No other leaf Statement is used as a premise.',
        vacuity='The statement is a general identity/implication on actual definitions, not an assertion of a finite certificate witness.',
        empty_degenerate='Zero memory/state/phase sizes and zero horizons are addressed by the explicit quantifiers and premises; no unsupported Fin index is constructed.',
        coercions='Exact rational coefficients and finite sums only. No floating arithmetic or truncating ENNReal coercion is used.',
        finset_fintype='Directions and phases retain their separate fixed Fintype instances and all edge multiplicities. The quotient does not divide by class sizes.',
        nat_subtraction='No new natural subtraction is introduced; existing finite horizons use range (R+1).',
        division_zero='No new variable denominator; the existing thresholds and coefficient/value scales are fixed positive constants.',
        instances='No section variables or implicit typeclass parameters; all leaf parameters are quantified in its definition.')
    traps.update(checks)
    new.append(dict(lean_name=ns+name,module=ns+module,paper_label=label,paper_source=source,paper_lines=lines,
        status='open',adaptation_status='new',proof_status='open',
        first_attempt_policy='The first Lean proof attempt must be assigned to a different, cheaper model; the blueprint architect must not attempt this leaf.',
        proof_assignment='Unassigned; orchestrator to select the cheaper model.',
        estimated_proof_lines=est,estimated_writer_hours='1–2',difficulty=difficulty,
        statement_summary=summary,statement='def '+ns+name+' : Prop :=\n'+match[1].strip(),
        dependencies=deps,suggested_proof_route=route,trap_check=traps))
app='/home/ubuntu/aklt/reports/REV_C2/app-input-contracts.tex'
add('StationaryCoefficientOffCentreStatementV2','NodesV2Stationary','d:stationary-walk',app,'517–553; ARCH_0 F9','easy',45,
    'The corrected and legacy scalar coefficients agree on every edge whose destination is not the centre.',
    ['AKLT.Defs.stationaryCoefficientV2','AKLT.Defs.stationaryCoefficient','AKLT.Defs.kernelCentre'],
    'Split the current-terminal/admissibility guard and known-site guard in both literal definitions. The explicit non-centre destination premise removes the only changed branch. No quotient correctness proof is necessary. This elementary proof is deliberately left open under the author rule.',
    dict(missing_premises='x+d.step≠kernelCentre is explicit and indispensable. The identity is not asserted on centre-destination edges.',empty_degenerate='m=0 is allowed; q=0 makes the quantified Fin q state absent. Arbitrary malformed quotient fields are allowed because this is a literal guard identity.'))
add('StationaryCentreZeroOperatorStatementV2','NodesV2Stationary','l:stationary-local-global',app,'763–826; ARCH_0 F9','easy',85,
    'The corrected and legacy backward operators agree on every rational function zero at the centre.',
    ['AKLT.Defs.stationaryApplyV2','AKLT.Defs.stationaryApply','AKLT.Defs.stationaryCoefficientV2','AKLT.Defs.stationaryCoefficient','Finset.sum_congr'],
    'Compare each direction/next-phase summand. For a destination equal to the centre use the displayed F(ψ,b,c)=0 premise on both sides. For every other destination split the literal guards. The existing Bellman system/word proofs can then be reused only on this explicit subspace.',
    dict(missing_premises='F is required to vanish at the centre for every phase and quotient state; no arbitrary-function equality is claimed.',vacuity='There are nonzero centre-zero functions. No sign or summability premise is needed for this finite rational identity.',empty_degenerate='Empty quotient state types make state quantifiers vacuous; all zero functions and zero values are covered.'))
add('StationaryContinuationBridgeStatementV2','NodesV2Stationary','l:stationary-domination',app,'555–686; ARCH_0 F9','medium',160,
    'All finite continuation sums from the fixed stationary target reward agree for the corrected and legacy operators.',
    ['AKLT.Defs.stationaryContinuationSumV2','AKLT.Defs.stationaryContinuationSum','AKLT.Defs.stationaryReward','AKLT.Defs.stationaryApplyV2','AKLT.Defs.stationaryApply','AKLT.Defs.kernelTarget','Function.iterate_succ_apply\'','Finset.sum_congr'],
    'Prove, as internal helpers, that the fixed reward is zero at the centre and both operators have zero rows there. Induct jointly on equality of the iterates and their centre-zero invariant. Compare non-centre destinations by the literal coefficient definitions and kill centre terms by the invariant, then sum j∈range(R+1). The fixed reward is essential; an arbitrary initial reward would give a false statement.',
    dict(missing_premises='The statement fixes stationaryReward X, with kernelTarget X distinct from kernelCentre; it does not quantify arbitrary terminal data.',empty_degenerate='R=0 includes just the zero-step target reward and both sums agree. The centre has zero reward even for the zero terminal phases.',nat_subtraction='There is no cutoff subtraction and no limit passage; this assertion covers each finite R including zero.'))
add('StationaryCertificateBridgeStatementV2','NodesV2Stationary','d:stationary-certificate',app,'688–760; ARCH_0 F9','medium',150,
    'Every V2 passing integer certificate supplies the exact legacy passing rows used by the frozen soundness graph.',
    ['AKLT.Defs.StationaryData.PassesV2','AKLT.Defs.StationaryData.Passes','AKLT.Defs.StationaryData.extended','AKLT.Defs.coefficientCeiling','AKLT.Defs.stationaryCoefficientV2','AKLT.Defs.stationaryCoefficient','Finset.sum_congr'],
    'Copy the unchanged positivity, terminal-cap, free-row, cap and terminal-data conjuncts. In each inside integer row compare summands by whether the destination is the centre. A centre destination has C.extended ψ b c=0 by the explicit checked terminal data, so both rounded-coefficient products are zero. All other coefficients and ceilings are equal. Preserve both natural scales. No supplied array or Correct witness is constructed.',
    dict(missing_premises='PassesV2 includes the centre-zero extended-value checks. They are needed before comparing rounded rows; coefficient inequality alone would not prove the desired reverse reuse implication.',coercions='The changed row comparison is entirely in ℕ. Rounded coefficients multiply the checked integer zero; no rounding equality is inferred from a floating approximation.',vacuity='The implication leaves all passing-certificate existence obligations with the external data checker. No incomplete/default array is installed.',empty_degenerate='The fixed finite square includes zero terminal values; zero-valued inside entries are legal. A zero-state quotient gives universal empty row checks without a fabricated state.'))
add('StoppedQuotientIntertwiningStatementV2','NodesV2Quotient','l:automaton-quotient',app,'315–363; REF2_6 finding 3','medium',220,
    'Finite stopped sums intertwine when the stopping indicator and terminal reward are explicit pullbacks of quotient data.',
    ['AKLT.Blueprint.H3.rawStoppedBackwardV2','AKLT.Blueprint.H3.quotientStoppedBackwardV2','AKLT.Defs.MemoryQuotient.Correct','AKLT.Defs.RawWindow','AKLT.Defs.windowSuccessor','AKLT.Gen.Bellman.Automaton.stopped_pullback','AKLT.Blueprint.H3.rawBackward_pullback','Finset.sum_congr','Function.iterate_succ_apply\''],
    'Use the explicitly assumed raw-successor closure. Prove one-step rational pullback by separate direction/phase comparisons, using Correct for labels and arrivals only on non-revisit edges. The terminal tests are equal on valid raw states by the explicit pullback premise. Induct on iterates; zero steps use the independent terminal-reward pullback premise. Sum the finite horizon. Gen.Bellman.Automaton.stopped_pullback is the existing nonnegative template, while these operators are exact rational ones.',
    dict(missing_premises='Both terminalRaw=terminalQuotient∘project and rewardRaw=rewardQuotient∘project are explicit on all raw states; the quotient reward also vanishes off the stopping set. Raw-successor closure and revisit arrival-independence are explicit.',empty_degenerate='R=0 tests the zero-step reward premise. m≥1 is explicit. Empty Fin p or Fin q types do not require invented indices. A zero reward needs no division.',vacuity='The REF2_6 counterexample with a raw-only zero-step reward is excluded by the reward pullback premise, not by making all stopping states impossible.',finset_fintype='The two operators sum the same absolute directions and next phases, preserving parallel edges and list/quotient multiplicities. No spatial quotient is introduced.'))
assert len(new)==5
allrows=old+new
assert len(allrows)==35
assert len({x['lean_name'] for x in allrows})==35
for r in new:
    assert r['lean_name'].endswith('V2')
    assert len(r['trap_check'])==8
    assert r['estimated_proof_lines']<=400
    assert not any(d.endswith('Statement') or d.endswith('StatementV2') for d in r['dependencies'])
(rep/'leaves.json').write_text(json.dumps(allrows,ensure_ascii=False,indent=2)+'\n')
# New audit source only. Never regenerate the frozen Audit.lean.
lines=['import AKLT.Blueprint.H3.AssemblyV2','','namespace AKLT.Blueprint.H3','']
for file in ['NodesV2Stationary.lean','NodesV2Quotient.lean','NodesV2.lean']:
    text=(root/'AKLT/Blueprint/H3'/file).read_text()
    for name in re.findall(r'^def (\w+)',text,re.M):
        if re.search(r'^def '+name+r' : Prop :=',text,re.M):
            lines.extend([f'#check ({ns+name} : Prop)',f'#print {ns+name}'])
        else:lines.append(f'#check {ns+name}')
text=(root/'AKLT/Blueprint/H3/AssemblyV2.lean').read_text()
for name in re.findall(r'^theorem (\w+)',text,re.M):
    lines.extend([f'#check {ns+name}',f'#print axioms {ns+name}'])
lines.extend(['','end AKLT.Blueprint.H3',''])
p=root/'AKLT/Blueprint/H3/AuditV2.lean';source='\n'.join(lines)
if not p.exists() or p.read_text()!=source:p.write_text(source)
print('Updated manifest: 30 kept, 0 superseded, 5 new open leaves. Generated AuditV2.lean only.')
