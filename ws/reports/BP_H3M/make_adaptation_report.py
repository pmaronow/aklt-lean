from pathlib import Path
from collections import Counter
import hashlib,json,re
root=Path('/home/ubuntu/aklt/wt/BP_H3M')
rep=Path('/home/ubuntu/aklt/reports/BP_H3M')
ns='AKLT.Blueprint.H3.'
rows=json.loads((rep/'leaves.json').read_text())
frozen=json.loads((rep/'frozen-v1-files.json').read_text())
for path,digest in frozen.items():assert hashlib.sha256((root/path).read_bytes()).hexdigest()==digest,path
assert len(rows)==35
old=[r for r in rows if r['adaptation_status']=='kept']
new=[r for r in rows if r['adaptation_status']=='new']
assert len(old)==30 and len(new)==5
state=json.loads((rep/'adaptation-build-state.json').read_text())
for m in ['AKLT.Blueprint.H3.AssemblyV2','AKLT.Blueprint.H3.AuditV2','AKLT.Blueprint.H3.Audit']:
    assert m in state
logs=rep/'adaptation-build-logs'
oldlog=(logs/'AKLT.Blueprint.H3.Audit.log').read_text()
newlog=(logs/'AKLT.Blueprint.H3.AuditV2.log').read_text()
assert not re.search(r'error:|warning:',oldlog+newlog)
axioms={}
for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",oldlog+newlog):
    axioms[name]=[x.strip() for x in axs.split(',') if x.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms",oldlog+newlog):axioms[name]=[]
assert len(axioms)==65,len(axioms)
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in axioms.values())
(rep/'axioms-v2.json').write_text(json.dumps(axioms,indent=2)+'\n')
(rep/'declarations-v2.log').write_text(newlog)
newsource=(root/'AKLT/Blueprint/H3/AssemblyV2.lean').read_text()
newtheorems=re.findall(r'^theorem (\w+)',newsource,re.M)
assert len(newtheorems)==13
assert all(ns+n in axioms for n in newtheorems)
for p in (root/'AKLT/Blueprint/H3').glob('NodesV2*.lean'):
    assert not re.search(r'^theorem ',p.read_text(),re.M),p
sources=[Path('/home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md'),
    *[Path('/home/ubuntu/aklt/reports')/f'REF2_{i}/report.md' for i in [5,6,7]],
    root/'AKLT/Blueprint/Top/ComputationV2.lean',root/'AKLT/Blueprint/Top/InputsV2.lean',
    root/'AKLT/Blueprint/Top/Assembly.lean',root/'AKLT/Defs/Stationary.lean',
    root/'AKLT/Defs/Computational.lean',root/'AKLT/Defs/Automaton10Data.lean']
(rep/'adaptation-sources-sha256.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},indent=2)+'\n')

def find(name):
    for p in sorted((root/'AKLT/Blueprint/H3').glob('*.lean')):
        for i,line in enumerate(p.read_text().splitlines(),1):
            if re.match(r'(?:@\[[^\n]*\]\s+)?(?:def|theorem) '+name+r'\b',line):return p,i
    raise KeyError(name)
def link(name):
    p,i=find(name);return f'[{name}]({p}:{i})'
def header(name):
    p,i=find(name);part='\n'.join(p.read_text().splitlines()[i-1:]);return part.split(' :=',1)[0]
def fl(name):return f'[{name}]({root}/AKLT/Blueprint/H3/{name})'

out=['STATUS: COMPLETE','','| Open leaf (namespace `AKLT.Blueprint.H3`) | Adaptation | Paper label | Difficulty |','|---|---|---|---|']
for row in rows:
    name=row['lean_name'].rsplit('.',1)[1]
    out.append(f'| {link(name)} | {row["adaptation_status"]} | `{row["paper_label"]}` | {row["difficulty"]} |')
out += ['', 'Current handoff: **30 old leaves kept, 0 superseded, 5 new open leaves**. All thirteen pre-adaptation Lean files, including every existing leaf file, are byte-identical to the adaptation baseline. No new leaf proof was attempted. The first attempt for every remaining proof belongs to a different, cheaper model.',
'', '## Adaptation', '',
'The repaired shared statement layer is merged into this worktree. This adaptation follows [ARCH_0/stmt-fix.md](/home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md) and the whole-paper referee findings in [REF2_5](/home/ubuntu/aklt/reports/REF2_5/report.md), [REF2_6](/home/ubuntu/aklt/reports/REF2_6/report.md), and [REF2_7](/home/ubuntu/aklt/reports/REF2_7/report.md). The old nodes remain true and useful supporting facts; the operator repair is handled by explicit new bridges rather than editing or weakening frozen statements.',
'', 'Names in the target table are in `AKLT.Blueprint.Top` unless explicitly marked H3-local. “New leaves” means additional open obligations; no old leaf body was changed.', '',
'| Old target | New target | Changed/new leaves and adaptation |','|---|---|---|',
'| `AutomatonQuotientStatement` | Same shared Top target, plus H3-local `AutomatonQuotientPaperStatementV2` | Add `StoppedQuotientIntertwiningStatementV2`; state both terminal-indicator and terminal-reward pullbacks and use frozen raw-successor closure. |',
'| `Automaton10Statement` | `Automaton10StatementV2` | External finite-check owner supplies the designated `Automaton10Data.supplied` archive checks. No local numeric proof or existential substitute. |',
'| `PhaseExpansionStatement` | `PhaseExpansionStatementV2`, plus H3-local `LongTrailPhaseExpansionStatementV2` | No new leaf: restrict the frozen general algebra to `ClosedTrail X w`; use the actual kernel contribution only for n>12. Chronological order within each type is `longOrdering`, not merely a type-order predicate. |',
'| `StationaryDominationStatement` | `StationaryDominationStatementV2` | Add `StationaryCoefficientOffCentreStatementV2` and `StationaryContinuationBridgeStatementV2`; the frozen closed-trail geometry supplies non-centre destinations. |',
'| `BellmanSoundnessStatement` | Unchanged | Reuse the preexisting proved generic Bellman interface and its frozen adapters. No new Bellman leaf proof. |',
'| `StationaryLocalGlobalStatement` | `StationaryLocalGlobalStatementV2` | Add `StationaryCertificateBridgeStatementV2`, `StationaryCentreZeroOperatorStatementV2`, and the continuation bridge. PassesV2 supplies the checked zero centre value. |',
'| `PrefixDominationStatement` | `PrefixDominationStatementV2` | Certificate bridge transfers the premise to the frozen prefix assembly; prefix expressions and true rows are unchanged. |',
'| `KernelReflectionStatement` | Unchanged | All reflection leaves and the existing B-only assembly are kept. |',
'| `StationaryCheckStatement` | `StationaryCheckStatementV2` | External finite-check owner supplies full PassesV2 tables for the same designated quotient as Automaton10StatementV2. |',
'| `StationaryAssemblyStatement` | `StationaryAssemblyStatementV2` | Certificate bridge transfers all five cases; exact prefix ceilings, row partitions, reflection and ENNReal assembly remain unchanged. |',
'| `H3Statement` | Unchanged semantic `H3Statement` | Obtain it from the repaired stationary assembly with both archive-bound V2 finite checks. No `Top.H3StatementV2` exists or is needed. |',
'| `InputsStatement` | `InputsStatementV2` | New `inputs_of_leaves_and_other_partsV2` supplies H3 and retains both V2 finite checks; H1, H2, the rate comparisons and H1 finite-data coverage remain explicit other-lane inputs. |',
'| `mainV2_of_parts` | `mainV2_of_partsV2` | New `mainV2_of_H3_and_other_partsV2` calls the repaired Top assembly with all foreign Rec/window/quantum/uniqueness contracts explicit. |',
'', '### Referee findings and their disposition', '',
'- **Closure neighbour pairs (REF2_5 finding 1):** the Rec lane owns the ordinary-domain closure statement and must restrict it to distinct nonremoved non-arrival neighbours. H3 already erases the arrival neighbour in `responseNeighbours`; its frozen live-pair/reward leaves do not claim closure for all neighbours. No broader pair-domain claim is added here.',
'- **Short-trail domain (REF2_5 finding 2):** `ClosedTrail X w` is the existing first-hit kernel-trail predicate, not a graph-theoretic cycle. The V2 phase target binds X and assumes that predicate. The existing short ordering remains the exact rational-key ordering, including zero-key and index tie branches.',
'- **Phase ordering (REF2_6 finding 2):** `longOrdering` filters `List.finRange n`, so straight visits and then turns are each chronological. The extra assembled `LongTrailPhaseExpansionStatementV2` identifies the phase fold with `closedContribution` only when 12<n. For shorter kernel trails the shared Top V2 formula concerns the separate longOrdering, not the prescribed short kernelOrdering. A length-twelve prefix of a long trail retains the long-trail phase weights.',
'- **Terminal data (REF2_6 finding 3):** the shared Top quotient contract already takes a quotient G and a position-only terminal test. The new general stopped leaf separately quantifies raw and quotient tests/rewards, assumes both pullbacks on RawWindow states, and requires the quotient reward to vanish off the stopping set. Its R=0 case explicitly uses reward descent; raw-only rewards of the referee counterexample are excluded.',
'- **Missing numerical witnesses (REF2_6 critical finding):** no finite witness existence is inferred from soundness or enumeration. Automaton10StatementV2 and StationaryCheckStatementV2 are hypotheses. Their concrete quotient is the same `Automaton10Data.supplied`. Compiling its literal definition is not claimed to prove raw coverage or Correct. The H1 handoff explicitly retains H1FiniteDataStatementV2.',
'- **Appendix D (REF2_7):** its sufficient certificate implication needs no H3 mathematical change. H1 finite-data/sector coverage remains an external input; this lane does not claim to discharge it.',
'', '### Why the frozen graph still suffices', '',
'The repair moves the centre-destination zero test before the known-site branch. The operators can therefore differ on arbitrary functions. The new leaves state only the correct restricted identities: coefficient equality off centre, operator equality on centre-zero functions, equality of fixed-target-reward continuation sums, and transfer of passing integer rows whose centre entries are checked zero. The V2 assemblies explicitly consume these identities; none is silently assumed or proved here.',
'', 'A V2 certificate maps to a legacy passing certificate through the new open certificate bridge. The existing local/global theorem then provides its nonnegative capped potential and legacy Bellman row. The centre-zero operator bridge transfers that row to stationaryApplyV2, while the continuation bridge transfers every finite horizon. True closed trails avoid centre-destination edges by the frozen geometric leaf, which transfers their pointwise coefficient bound. This preserves every true path and prefix multiplicity without copying the old eleven domination leaves.',
'', 'All thirty old leaves are therefore `kept`; none is `superseded`. Their exact statements, modules and source bytes are unchanged. `status`/`adaptation_status` in leaves.json record kept/new disposition, and `proof_status: open` records their unproved mathematical status.',
'', '## Files and reproduction', '', '| New or updated artifact | Contents |','|---|---|',
f'| {fl("NodesV2Stationary.lean")} | Four closed open bridges to the corrected coefficient/operator, finite continuation sum and passing integer certificate. |',
f'| {fl("NodesV2Quotient.lean")} | Two stopped operator definitions, one closed open terminal-data intertwining leaf, and the assembled paper-facing quotient target. |',
f'| {fl("NodesV2.lean")} | Five-leaf index package and the explicit long-trail phase target; these packages/targets are not additional leaves. |',
f'| {fl("AssemblyV2.lean")} | Thirteen proved assembly implications, including all nine repaired/unchanged H3 targets, referee clarifications, InputsStatementV2 and mainV2_of_partsV2 handoffs. |',
f'| {fl("AuditV2.lean")} | New closed-Prop/type/axiom audit; frozen Audit.lean is retained unchanged and was freshly rechecked. |',
f'| [leaves.json]({rep}/leaves.json) | All 35 open statements, with each old leaf marked kept, each new leaf marked new/open, exact statements, paper/reuse pointers, budgets and eight trap categories. |',
f'| [frozen-v1-files.json]({rep}/frozen-v1-files.json) | Baseline SHA-256 for all thirteen pre-adaptation Lean files. |',
f'| [declarations-v2.log]({rep}/declarations-v2.log), [axioms-v2.json]({rep}/axioms-v2.json) | Exact new declarations and fresh axiom inventory for all 65 old/new exported theorems. |',
f'| [build_adaptation.py]({rep}/build_adaptation.py) | Sequential, cached olean-only builder. It compiles imported AKLT modules only, uses prebuilt Mathlib and emits no C for the large archive literal. |',
f'| [make_adaptation.py]({rep}/make_adaptation.py), [make_adaptation_report.py]({rep}/make_adaptation_report.py) | Current manifest/new audit and report generators. They never regenerate frozen leaf or audit sources. |',
f'| [adaptation-sources-sha256.json]({rep}/adaptation-sources-sha256.json) | Hashes for repaired source contracts and all three referee reports. |',
f'| [report-pre-adaptation.md]({rep}/report-pre-adaptation.md), [leaves-pre-adaptation.json]({rep}/leaves-pre-adaptation.json) | Archived original handoff, including the prior build-scheduling note and leaf designs. The older make_manifest.py/make_report.py are V1-only archive generators; use the new adaptation generators. |',
'', 'Only the five new Lean files named above were written. No existing Lean file or Top/Defs/Gen/Vendor source was edited. No sub-agent or new leaf proof was used. All forty preexisting leaf/supporting proofs are retained under the author exception and listed below.',
'', '## Exported V2 assembly statements', '', 'All assembly hypotheses are closed Props. The combined declaration is:', '', '```lean',header('allTargets_of_leaves_and_checksV2'),'```','',
'`paperTargets_of_leaves_and_checksV2` adds the stopped-terminal and long-order qualifications. The other-lane handoffs are explicit:', '', '```lean',header('paperTargets_of_leaves_and_checksV2'),'',header('inputs_of_leaves_and_other_partsV2'),'',header('mainV2_of_H3_and_other_partsV2'),'```','',
'Exact signatures for the component assemblies and definitions are in `declarations-v2.log`. The H1/H2 rate conjunction is a closed other-lane numerical input, not an additional H3 leaf. The five V2 leaf definitions have no theorem witnesses; each first proof attempt remains assigned to a future different, cheaper model.',
'', '## New leaf statements and trap review', '',
'Every new leaf has its full exact closed statement, a proof estimate no larger than 220 lines, library/definition dependencies and suggested route in leaves.json. No new leaf type takes another leaf Statement as a hypothesis. The stopped leaf takes an explicit mathematical raw-successor closure premise, supplied by RawSuccessorStatement in the proved paper-facing quotient assembly.',
'', '| New leaf | Principal missing-premise/degenerate-case trap checked |','|---|---|',
'| `StationaryCoefficientOffCentreStatementV2` | Non-centre destination is indispensable; no arbitrary-edge equality is stated. Memory zero and malformed quotient fields are allowed because the literal guard identity remains valid. |',
'| `StationaryCentreZeroOperatorStatementV2` | F must vanish at the centre for every phase/class. Signed rational F is allowed because this is equality, not a monotonicity argument. |',
'| `StationaryContinuationBridgeStatementV2` | Uses exactly stationaryReward X, which is zero at the centre. R=0 includes the zero-step reward. It is not an arbitrary-initial-data assertion. |',
'| `StationaryCertificateBridgeStatementV2` | Centre-zero extended values are part of PassesV2. Rounded natural coefficients multiply zero there; both integer scales remain distinct. No passing data is constructed. |',
'| `StoppedQuotientIntertwiningStatementV2` | Both terminal tests and rewards descend on all valid raw states. Reward support, raw-successor closure, m≥1 and revisit arrival-independence are explicit; directions/phases retain multiplicity. |',
'', 'The complete per-leaf review retains all eight original categories: missing premises, vacuity, empty/degenerate cases, coercions, finite/list sums, natural subtraction, zero denominators and instances. New equalities are rational and finite, add no variable division and no extra natural subtraction, and introduce no dropped instance binder. Existing cutoff-zero, length-twelve-hit, B-only reflection, integer ceiling and nonnegative ENNReal series checks are unchanged.',
'', '## Retained pre-rule proofs', '',
'These forty leaf/supporting proofs were already written before the author’s cheaper-model-first rule. They remain byte-identical, were freshly rechecked against the repaired layer, and have not been reopened or extended. Exact types and the original retention inventory are in [retained-proofs.json]('+str(rep)+'/retained-proofs.json); the new fresh axiom inventory is axioms-v2.json.',
'', '| Existing proof | Module |','|---|---|']
retained=json.loads((rep/'retained-proofs.json').read_text())['retained_leaf_and_supporting_proofs']
assert len(retained)==40
for proof in retained:
    name=proof['lean_name'].rsplit('.',1)[1]
    out.append(f'| {link(name)} | `{proof["module"].rsplit(".",1)[1]}` |')
out += ['', 'The explicit old leaf/Top witnesses include coefficientCeiling_proved, wordSplit_proved, reflectionOrderingAlgebra_proved and bellmanSoundness_proved. New proofs occur only in AssemblyV2.lean and derive targets from supplied closed Props and existing proved assemblies.',
'', '## Axiom audit and builds', '',
'All 65 exported theorems (52 frozen, 13 new assemblies) were freshly checked against the merged statement layer. Every axiom set is a subset of propext, Classical.choice and Quot.sound. New assembly output:', '', '```text']
for name in newtheorems:
    full=ns+name
    out.append("'"+full+"' depends on axioms: ["+', '.join(axioms[full])+']')
out += ['```','',
'The sequential builder uses the pinned Lake environment, explicit autoImplicit=false/relaxedAutoImplicit=false, and an isolated report-directory olean root. It never invokes a Mathlib source build, lake update or C generation. This entire adaptation used at most one Lean process at once. The older, unmeasured V1 dependency-warmup scheduling deviation remains documented in the archived V1 report; it is not repeated in this round.',
'', 'Commands run from the worktree:', '', '```bash','export PATH="$HOME/.elan/bin:$PATH"',
'lake env python3 /home/ubuntu/aklt/reports/BP_H3M/build_adaptation.py AKLT.Blueprint.H3.NodesV2 AKLT.Blueprint.Top.Assembly',
'lake env python3 /home/ubuntu/aklt/reports/BP_H3M/build_adaptation.py AKLT.Blueprint.H3.AuditV2',
'lake env python3 /home/ubuntu/aklt/reports/BP_H3M/build_adaptation.py AKLT.Blueprint.H3.Audit AKLT.Blueprint.H3.AuditV2','```','',
'| Build stage | Modules compiled | Wall time | Parallel limit |','|---|---:|---:|---:|',
'| Repaired dependencies, frozen nodes, new node definitions and Top assembly | 53 | 203.36 s | 1 |',
'| Bellman/frozen assembly, new assembly and V2 audit | 4 | 13.37 s | 1 |',
'| Fresh full frozen Audit (V2 audit cached) | 1 | 3.61 s | 1 |',
'',f'Per-module commands, exit codes, source/dependency signatures and timings are in [adaptation-build-state.json]({rep}/adaptation-build-state.json) and [adaptation-build-logs]({rep}/adaptation-build-logs). All stages passed without warnings or errors. Frozen-file hash validation passed. A source scan found no forbidden proof escape or effectful Lean command.',
'', '## Open issues and handoff', '',
'Thirty kept and five new analytic leaves remain open, all with exact names/types in leaves.json. The two designated V2 finite checks remain external proof obligations. H1 semantic/finite data, H2/rates, Rec, CutMOS, MainW and TorusKernel remain explicit other-lane inputs of the optional headline assembly. No unconditional H1, H3 or gap theorem is claimed.',
'', 'No additional Top/Defs repair was required. The statement fixes and the two referee scope qualifications are reflected in the V2 assemblies and handoff. The orchestrator should assign all remaining first proof attempts to a different, cheaper model; this architect has supplied no new leaf proof.',
'', '## ORCH-SUMMARY', '',
'Adaptation COMPLETE: five new Lean files; all thirteen pre-adaptation Lean files are byte-identical.',
'Old leaves: 30 kept, 0 superseded. New open leaves (prefix AKLT.Blueprint.H3):',
'StationaryCoefficientOffCentreStatementV2.',
'StationaryCentreZeroOperatorStatementV2.',
'StationaryContinuationBridgeStatementV2.',
'StationaryCertificateBridgeStatementV2.',
'StoppedQuotientIntertwiningStatementV2.',
'Exact kept names/statements and all five new statements are in leaves.json (35 open obligations).',
'No leaf proof attempted; retain the forty existing leaf/helper proofs listed in this report.',
'All new proof declarations are assembly implications in AssemblyV2.lean.',
'allTargets_of_leaves_and_checksV2 derives all nine repaired/unchanged Top targets.',
'paperTargets_of_leaves_and_checksV2 adds explicit terminal pullbacks and the n>12 phase/kernel identity.',
'Both finite-check inputs are V2 and refer to the same designated Automaton10Data.supplied quotient.',
'inputs_of_leaves_and_other_partsV2 supplies InputsStatementV2 with other-lane inputs explicit.',
'mainV2_of_H3_and_other_partsV2 calls Top.mainV2_of_partsV2; this is conditional only.',
'Arrival pairs were already excluded in H3; Rec owns the ordinary-domain closure repair.',
'All 65 old/new theorem audits use only allowed axioms; builds passed with one Lean process.',
'V1 generators are archived; use make_adaptation.py and make_adaptation_report.py for this handoff.',
'Orchestrator: assign the 35 leaves to a different, cheaper model; obtain both V2 finite checks from CERT_H3.',
'No new shared-statement repair or mathematical replacement decision is required.','']
assert len(out[out.index('## ORCH-SUMMARY')+2:])-1<=25
(rep/'report.md').write_text('\n'.join(out))
print('Adaptation report complete: 30 kept + 5 new; 65 theorem axiom checks; 13 frozen files unchanged.')
