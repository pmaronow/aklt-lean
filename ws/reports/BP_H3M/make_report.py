from pathlib import Path
from collections import Counter
import json,re,hashlib,subprocess
root=Path('/home/ubuntu/aklt/wt/BP_H3M')
rep=Path('/home/ubuntu/aklt/reports/BP_H3M')
rows=json.loads((rep/'leaves.json').read_text())
ns='AKLT.Blueprint.H3.'
audit=(rep/'audit.log').read_text()
build=(rep/'build.log').read_text()
assert 'Build completed successfully' in audit and 'Build completed successfully' in build
assert not re.search(r'error:|warning:',audit+build)
clean=[]
keep=False
for line in audit.splitlines():
    match=re.match(r'info: AKLT/Blueprint/H3/Audit.lean:\d+:\d+: (.*)',line)
    if match:
        keep=True
        clean.append(match[1])
    elif line.startswith(('info:','ℹ ','✔ ','⚠ ','✖ ','Build completed','real ','user ','sys ')):
        keep=False
    elif keep:
        clean.append(line)
(rep/'declarations.log').write_text('\n'.join(clean)+'\n')
axioms={}
for name,axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",'\n'.join(clean)):
    axioms[name]=[x.strip() for x in axs.split(',') if x.strip()]
for name in re.findall(r"'([^']+)' does not depend on any axioms",'\n'.join(clean)):
    axioms[name]=[]
theorems=[]
for f in sorted((root/'AKLT/Blueprint/H3').glob('*.lean')):
    if f.name=='Audit.lean':continue
    theorems += [ns+n for n in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)',f.read_text(),re.M)]
assert set(theorems)==set(axioms),(set(theorems)-set(axioms),set(axioms)-set(theorems))
assert all(set(ax)<= {'propext','Classical.choice','Quot.sound'} for ax in axioms.values())
(rep/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
paths=[Path('/home/ubuntu/aklt/reports/REV_C2/app-input-contracts.tex'),Path('/home/ubuntu/aklt/reports/REV_C2/sec8-inputs.tex'),Path('/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md'),Path('/home/ubuntu/aklt/compfeas/report.md'),Path('/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md')]
(rep/'source-sha256.txt').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p)+'\n' for p in paths))
counts=Counter(r['difficulty'] for r in rows)
assembly=['automatonQuotient_of_nodes','phaseExpansion_of_nodes','stationaryDomination_of_nodes','bellmanSoundness','stationaryLocalGlobal_of_nodes','prefixDomination_of_nodes','kernelReflection_of_nodes','stationaryAssembly_of_nodes','h3_of_checks','allTargets_of_leaves_and_checks','reflectPair_injective','ceiling_rows','longExposureExpansion_of_nodes','reflectionPairs_of_nodes']

def filelink(name):
    return f'[{name}]({root}/AKLT/Blueprint/H3/{name})'
def lineof(name):
    for f in (root/'AKLT/Blueprint/H3').glob('*.lean'):
        for i,l in enumerate(f.read_text().splitlines(),1):
            if re.match(r'(?:@\[[^\n]*\]\s+)?(?:def|theorem) '+re.escape(name)+r'\b',l):return f,i
    raise ValueError(name)
def declaration_header(name):
    f,i=lineof(name)
    lines=f.read_text().splitlines()
    segment='\n'.join(lines[i-1:])
    e=segment.index(' :=')
    return segment[:e]

# Preserve the proofs written before the author's cheaper-model-first instruction.
# Target wrappers and implication-only refinements are assemblies; the remainder are
# conservatively inventoried as retained leaf or supporting proofs.
assembly_policy_names={
    'automatonQuotient_of_nodes','phaseExpansion_of_nodes','stationaryDomination_of_nodes',
    'bellmanSoundness','stationaryLocalGlobal_of_nodes','prefixDomination_of_nodes',
    'kernelReflection_of_nodes','stationaryAssembly_of_nodes','h3_of_checks',
    'allTargets_of_leaves_and_checks','longExposureExpansion_of_nodes','reflectionPairs_of_nodes'}
direct_leaf_witnesses={'coefficientCeiling_proved','wordSplit_proved',
    'reflectionOrderingAlgebra_proved','bellmanSoundness_proved'}
retained=[]
for full in theorems:
    name=full.rsplit('.',1)[1]
    if name in assembly_policy_names:
        continue
    f,line=lineof(name)
    retained.append(dict(lean_name=full,module='.'.join(f.relative_to(root).with_suffix('').parts),
        source_file=str(f),line=line,
        classification='preexisting leaf or Top-interface witness' if name in direct_leaf_witnesses else 'preexisting supporting proof',
        status='retained under the author exception for proofs written before the new rule',
        statement=declaration_header(name),axioms=axioms[full]))
assert len(retained)==40,len(retained)
policy_description='From the author-rule message onward, every first Lean leaf-proof attempt belongs to a different, cheaper model. This includes short proofs and checker soundness. This blueprint architect only writes statements, definitions, designs, executable computations/prototypes and proved assembly implications. Proofs already written before that message are retained.'
lean_hashes={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest()
    for f in sorted((root/'AKLT/Blueprint/H3').glob('*.lean'))}
(rep/'retained-proofs.json').write_text(json.dumps(dict(
    policy=policy_description,retained_leaf_and_supporting_proofs=retained,
    existing_assembly_and_wrapper_theorems=[ns+x for x in sorted(assembly_policy_names)],
    lean_source_sha256_at_policy_update=lean_hashes),indent=2,ensure_ascii=False)+'\n')
retained_report=['','## Author rule and proofs retained from before it','',policy_description,'',
    'This update changes the report and manifest metadata only. No Lean proof was added, extended, or attempted after the new instruction. All thirty remaining proof obligations stay open in `leaves.json`, each with the cheaper-model-first assignment rule. No executable checker with an unlisted pending soundness obligation was added.','',
    'The following forty existing leaf or supporting proofs are retained under the explicit exception. Names use namespace `AKLT.Blueprint.H3`; exact statements and axiom lists are in `retained-proofs.json` and `declarations.log`. Implication-only target/refinement assemblies and the existing Bellman alias are inventoried separately in `retained-proofs.json`.','',
    '| Existing proof | Module | Role |','|---|---|---|']
for proof in retained:
    name=proof['lean_name'].rsplit('.',1)[1]
    mod=proof['module'].rsplit('.',1)[1]
    role='leaf / Top witness' if name in direct_leaf_witnesses else 'supporting proof'
    retained_report.append(f"| [{name}]({proof['source_file']}:{proof['line']}) | `{mod}` | {role} |")
retained_report += ['',
    'The explicit closed leaf witnesses already proved are `coefficientCeiling_proved : CoefficientCeilingStatement`, `wordSplit_proved : WordSplitStatement`, and `reflectionOrderingAlgebra_proved : ReflectionOrderingAlgebraStatement`. The preexisting `bellmanSoundness_proved` proves the requested Top Bellman interface outright. Their proofs are kept; they are not reopened or reattempted.']

out=['STATUS: COMPLETE','','| Open leaf (namespace `AKLT.Blueprint.H3`) | Paper label / source lines | Difficulty | Estimated proof lines |','|---|---|---|---:|']
for r in rows:
    n=r['lean_name'].split('.')[-1];f,i=lineof(n)
    out.append(f'| [{n}]({f}:{i}) | `{r["paper_label"]}` / {r["paper_lines"]} | {r["difficulty"]} | {r["estimated_proof_lines"]} |')
out += ['',f'Thirty open leaves: {counts["easy"]} easy and {counts["medium"]} medium. Each has an estimated proof size below 400 lines and a suggested 1–2 hour writer route. These are proof-planning estimates, not completed proofs. The heavier exposure, reflection, known-site, and prefix arguments have been split again before reaching this table.',
'', 'The design task is complete. The AKLT mathematical proof still depends on these thirty closed propositions and on the two finite data checks owned by the computational agent. No unproved fact has been declared as a theorem.',
'', '## Files', '', '| File | Contents |','|---|---|',
f'| {filelink("Basic.lean")} | Phase folds/products, actual suffix windows, finite stationary word weights, finite shift support, reflection and exact concatenation helpers. |',
f'| {filelink("Positivity.lean")} | Proved coefficient/reward/product nonnegativity, positive exact witness, and 0<kernelRho<1. |',
f'| {filelink("Bellman.lean")} | Proved real-list and rational-stationary adapters to `AKLT.Gen.Bellman.System`, plus the entire Top Bellman interface. |',
f'| {filelink("NodesAutomaton.lean")} | Two quotient leaves and proved exact one-row pullback/congruence. |',
f'| {filelink("NodesPhase.lean")} | Six phase leaves, one derived exposure node, and its proved refinement. |',
f'| {filelink("NodesDomination.lean")} | Eleven geometry/counting/reward/path leaves and the explicit scalar predicate `TrueStepFacts`. |',
f'| {filelink("NodesCertificate.lean")} | One free-edge comparison leaf; proved ceiling, scaled rational rows, caps, and inside/free certificate soundness. |',
f'| {filelink("NodesPrefix.lean")} | Two prefix leaves, proved word equivalence and cutoff monotonicity. |',
f'| {filelink("NodesReflection.lean")} | Three reflection leaves, pair refinement, and proved ordering algebra. |',
f'| {filelink("NodesKernel.lean")} | Five finite-row/nonnegative-series leaves and proved zero-length normalization. |',
f'| {filelink("Nodes.lean")} | `AnalyticLeavesStatement`, the conjunction indexing exactly the thirty open leaves; this aggregate is not an extra leaf. |',
f'| {filelink("Assembly.lean")} | All nine target implications and the combined theorem from the leaf package and the two finite checks. |',
f'| {filelink("Audit.lean")} | Kernel-checked closed-Prop checks, exact declaration inventory, and axiom checks for every exported theorem. |',
f'| [leaves.json]({rep}/leaves.json) | Full Lean statements, definitions/library dependencies, paper pointers, suggested proof routes, budgets, and eight trap checks for each open leaf. |',
f'| [declarations.log]({rep}/declarations.log) | Exact Lean-printed statements/types of every exported declaration and all theorem axiom reports. |',
f'| [axioms.json]({rep}/axioms.json) | Machine-readable axiom inventory for all {len(theorems)} exported theorems. |',
f'| [retained-proofs.json]({rep}/retained-proofs.json) | Author-rule policy, exact inventory of the forty preexisting leaf/supporting proofs, assembly classification, and unchanged Lean source hashes. |',
f'| [build.log]({rep}/build.log), [audit.log]({rep}/audit.log), [dependency-check.log]({rep}/dependency-check.log) | Successful build, full audit, and checked library-reference logs. |',
f'| [source-sha256.txt]({rep}/source-sha256.txt) | Paper/plan/fallback/reuse-map snapshot hashes. |',
'', 'All source changes are under `AKLT/Blueprint/H3/`, with namespace `AKLT.Blueprint.H3`. No existing Top, Defs, Gen, Vendor, or other owner source file was edited. `make_manifest.py` and `make_report.py` reproduce the manifest/audit source and report artifacts in this report directory.',
*retained_report, '', '## Target assembly and exported statements', '', 'All assembly hypotheses are closed Props. The combined export has exactly the following type (the local namespace resolves the short names):', '', '```lean',declaration_header('allTargets_of_leaves_and_checks'),'```','',
'The eight analytic interfaces also have separate assemblies, so they can be used before the finite data checks are available. Exact types for these exports follow; helper signatures and every leaf body are also in `declarations.log`.', '', '```lean']
for name in assembly[:9]:
    out += [declaration_header(name),'']
out += ['```','',
'`longExposureExpansion_of_nodes` proves the internal exposure node from the two smaller list/order leaves. `reflectionPairs_of_nodes` proves the internal pair node from the live-pair bijection and scalar labels. `CoefficientCeilingStatement`, `WordSplitStatement`, and `ReflectionOrderingAlgebraStatement` have proved witnesses in their node files and are not open leaves.',
'', '## Reuse and assembly reasoning', '',
'`Bellman.lean` encodes a real edge list with natural-number labels, including repeated edges by their list indices. Its exact step and iterate bridges transfer `System.horizon_le` and `System.total_le` to the Top real-list statement. Terminal support is retained in the Top interface; the bound itself is stronger and does not need that support premise. `System` already supplies the generic first-hit path interpretation. No normalization, resolvent, eigenvalue, or stochasticity premise was added.',
'', '`NodesCertificate.rational_scaled_row` specializes the already proved `Gen.Bellman.scaled_row_sound`. The assembly applies that result to every free and inside row, uses caps and the one open model-specific free-edge inequality outside the square, and then applies `System.horizon_le` through the rational stationary adapter. The local/global and prefix sums are therefore actual lattice operators with exact rational weights. No periodic spatial identification is introduced.',
'', 'The domination assembly derives the at-most-two-departures budget from two smaller counting leaves, supplies every field of `TrueStepFacts`, transfers quotient successors through `Correct`, compares each concrete suffix word, and only then sums over words and horizons. The prefix assembly uses exact short ordering through twelve and splits every longer contribution at twelve; surviving prefixes and quotient multiplicities are explicitly preserved.',
'', 'The final assembly partitions each row by its first direction, uses only B north/south reflection, and proves the final ceiling arithmetic by rational `norm_num`/`linarith`. It then obtains the full ENNReal row by finite type/shift partition plus nonnegative series regrouping and lifting from all finite cutoffs. The exact dyadic `kernelWitness .C` is used throughout.',
'', '## Trap review', '',
'Each of the thirty entries in `leaves.json` contains separate checks for missing premises, vacuity, empty/degenerate cases, coercions, Finset/Fintype/list sums, natural subtraction, zero denominators, and instances. These are design reviews, not substitute proofs of the open leaves. The manifest validator checks that every leaf occurs exactly once in the aggregate, has no other open-leaf constant in its type, has all eight trap fields, and has a proof-size estimate at most 400.',
'', '- Positive memory is explicit for raw successor closure; every suffix window is used only at i≥10. The permanent known-site argument has L≥12, which forces i−10≥2 before remembered indices are compared to the two initial departures.',
'- Cutoff zero, zero-length paths, empty phase products, empty live-pair sets, zero rewards, the split L=0 or L=n, and the exact hit at length twelve are covered. A length-twelve hit belongs only to the short sum. The generic phase identities allow signed rewards and never divide by a reward.',
'- The coefficient-comparison leaf requires actual raw validity, non-revisit arrival consistency, one-way revisit detection, first-visit labels, reward domination, current/next terminal exclusions, and known-site safety through `TrueStepFacts`. The assembly constructs this predicate from the smaller leaves; its definition does not repeat the desired inequality.',
'- Directions and next phases remain separate labels, including parallel quotient successors and duplicate list edges. Prefix words remain individually indexed; passing to a quotient never divides by a fibre size. Every use of a list-to-Finset conversion has explicit Nodup.',
'- Rational sums are converted to ENNReal only after proved nonnegativity. Full series use ENNReal, whose divergent sum cannot silently collapse to zero. The zero-length row is proved zero before converting Icc 1 R cutoff bounds into an all-length tsum.',
'- All divisions use fixed positive denominators: the two local thresholds, 3, 5, the dyadic witness denominator, 2^16, and 2^48. This route does not divide by 1 minus a numerically estimated spectral radius.',
'- The type/shift decomposition keeps `kernelOrdering w` fixed; it does not optimize the ordering again for each component reward. Only the B target is reflection-fixed, so no C-row reflection claim enters any leaf.',
'- Lake compiled the files with the project’s `autoImplicit = false` and `relaxedAutoImplicit = false`. All leaf parameters are quantified within the definitions; no section variable or extra instance parameter is inferred. Fintypes are the concrete Defs instances.',
'', '## Top / Defs problems found', '',
'No false, ill-typed, or paper-divergent target declaration was found in this review. No V2 replacement was needed, and no Top or Defs declaration was changed.',
'', '`StationaryCheckStatement` itself includes a quotient and its `Correct` proof. Consequently the automaton cardinality/edge-count check is logically redundant once this stronger stationary check is supplied. `h3_of_checks` and the combined theorem retain `Automaton10Statement` as an explicit requested provenance input, but do not consume its counts a second time or assume an unprovided equality between two quotient witnesses. This is interface redundancy, not a counterexample.',
'', '## Axiom audit', '',f'All {len(theorems)} exported theorems were checked. Each uses a subset of `[propext, Classical.choice, Quot.sound]`; no additional axiom is present. The exact output for every assembly/refinement theorem is:', '', '```text']
for name in assembly:
    full=ns+name
    if axioms[full]:out.append("'"+full+"' depends on axioms: ["+', '.join(axioms[full])+']')
    else:out.append("'"+full+"' does not depend on any axioms")
out += ['```','', 'A source scan found no forbidden proof escape, kernel-check bypass, effectful Lean command, or unbounded heartbeat setting in the delivered Lean files. The complete audited output and machine-readable inventory are linked above.',
'', '## Build commands and timings', '', 'Run from `/home/ubuntu/aklt/wt/BP_H3M`:', '', '```bash','export PATH="$HOME/.elan/bin:$PATH"','lake build AKLT.Blueprint.H3.Assembly','lake build AKLT.Blueprint.H3.Audit','```','',
'Every imported local dependency was built through named module targets using the existing toolchain and prebuilt Mathlib. No `lake update`, Mathlib source build, package edit, or sub-agent was used. Later module rebuilds were staged in groups with at most four requested leaf-module jobs; the final Assembly and Audit builds were sequential named targets.', '',
'Initial dependency-warmup scheduling deviation: the first named dependency build used Lake’s default scheduler and was not manually bounded to four Lean processes. Its peak was not measured. All subsequent blueprint builds were explicitly staged to stay within four. No claim of a measured four-process peak is made for that initial warmup.', '',
'Final recorded successful builds (dependencies already compiled; Lake time includes checking the prebuilt dependency graph):', '', '| Command | real | user | sys |','|---|---:|---:|---:|']
for name,log in [('lake build AKLT.Blueprint.H3.Assembly',build),('lake build AKLT.Blueprint.H3.Audit',audit)]:
    t={k:v for k,v in re.findall(r'^(real|user|sys) ([0-9.]+)$',log,re.M)}
    out.append(f'| `{name}` | {t["real"]} s | {t["user"]} s | {t["sys"]} s |')
out += ['', 'Both builds completed with no warnings or errors. A separate `lake env lean` check verified every definition/library identifier cited in the dependency manifest. No numerical certificate data was executed or assumed to have passed.',
'', '## Open issues', '',
'The thirty table entries are the complete remaining analytic obligations. They are definitions of closed propositions, not incomplete proofs. The two external finite checks remain hypotheses and belong to their assigned computational owner. The checked implications prove that these obligations suffice for every requested Top target. There is no remaining assembly hole or required Top/Defs change.',
'', '## ORCH-SUMMARY', '',
'Delivered: 13 Lean modules in AKLT/Blueprint/H3, leaves.json, full declaration/axiom audits and this report.',
'All nine requested Top targets have proved assembly implications.',
'BellmanSoundnessStatement is proved outright from Gen.Bellman; ceiling, row scaling, caps, word split and ordering algebra are proved.',
'Combined export: AKLT.Blueprint.H3.allTargets_of_leaves_and_checks.',
'Open exact names below use prefix AKLT.Blueprint.H3:',
'RawSuccessorStatement; ProjectionRealizationStatement.',
'PhaseFoldExpansionStatement; SingleChangeFactorStatement.',
'ExposureListExpansionStatement; LongOrderingMultiplierStatement.',
'PrefixCoefficientCausalityStatement; PhaseSplitAlgebraStatement.',
'SuffixWindowValidityStatement; SuffixWindowLabelsStatement.',
'IncidentBondBudgetStatement; DepartureBalanceStatement.',
'KnownSiteMemoryStatement; TrueRewardIdentityStatement.',
'RewardForgettingStatement; LocalCoefficientComparisonStatement.',
'ClosedTrailStepGeometryStatement; SuffixWordComparisonStatement; StationaryWordExpansionStatement.',
'StationaryFreeEdgeStatement; LongTrailPrefixStatement; LongRowRegroupingStatement.',
'ReflectionGeometryStatement; ReflectionLivePairsStatement; ReflectionPairLabelsStatement.',
'FirstDirectionPartitionStatement; LengthShiftSupportStatement; LengthRewardPartitionStatement.',
'KernelSeriesRegroupingStatement; CutoffSeriesLiftStatement.',
'External inputs: Top.Automaton10Statement and Top.StationaryCheckStatement; not proved here.',
'No Top/Defs mismatch found; no V2 or shared-source edit. Automaton counts are redundant given StationaryCheck’s Correct quotient.',
'All exported theorem axioms are subsets of propext, Classical.choice, Quot.sound; builds and audits pass.',
'Deviation: initial dependency warmup used unbounded default Lake job scheduling; later blueprint builds were staged within four.',
'Orchestrator: assign the thirty leaves to a different, cheaper model using leaves.json; obtain both finite checks from their owner.',
'Author rule: all thirty first proof attempts go to a different, cheaper model; forty prior leaf/helper proofs are retained and listed.','']
assert len(out[out.index('## ORCH-SUMMARY')+2:])-1<=25
(rep/'report.md').write_text('\n'.join(out))
print(f'Report complete: {len(rows)} open leaves, {len(theorems)} audited exported theorems; all axiom sets allowed.')
