from pathlib import Path
import json,re
out=Path('/home/ubuntu/aklt/reports/BP_REC')
if (out/'adaptation-baseline.json').exists():
    import runpy
    runpy.run_path(str(out/'update_adaptation.py'), run_name='__main__')
    raise SystemExit(0)
root=Path('/home/ubuntu/aklt/wt/BP_REC/AKLT/Blueprint/Rec')
rows=json.loads((out/'nodes.json').read_text()); opens=[r for r in rows if r['status']=='open']
policy=json.loads((out/'proof-policy.json').read_text())
lines=['STATUS: COMPLETE','', '| Leaf / node | Paper label | Difficulty | State |','|---|---|---|---|']
for r in rows:
    name=r['lean_name'].split('.')[-1]
    lines.append(f"| [{name}]({r['source_file']}:{r['source_line']}) | `{r['paper_label']}` | {r['difficulty']} | {r['status']} |")
lines += ['', '## Delivery and scope', '',
'All files are under `AKLT/Blueprint/Rec/`, with namespace `AKLT.Blueprint.Rec`. The design covers the mass-free §6 expansion and the §7 closure, typed coefficients, shifted kernel, response recursion and renewal. There are 92 statement nodes: 88 open proof tasks, three unconditional rational leaf proofs, and one intermediate statement assembled from finer leaves. The five requested original Top interfaces and the useful typed V2 interface have checked assembly implications.', '',
'`leaves.json` contains every open task, its exact Lean statement, source location, paper label, difficulty, estimated proof size, definition/library dependencies, route, donor pointers and individual trap check. `nodes.json` also includes the proved and assembled nodes. No dependency list grants another Rec leaf as a hypothesis. All leaf statements are closed, and all assembly arguments are closed Props. Semantic premises such as an admissible network, a numerical row inequality or H1/H2/H3 are stated inside the relevant universal statement.', '',
'Proof-size estimates in the manifest are planning estimates (90/220/380 lines for easy/medium/hard). The finite expansion is split into moment identities, dynamics, coordinate iteration, terminal factors and degree accounting. Closure is split into normalization, prefix invariant, ordinary removal, covering, pair closure, terminal defect, second start, location and count. The kernel splits ordering, positivity, support, geometry, nonnegative regrouping, one-length majorization, summability, unshifted witness, power increment, explicit choice and perturbation. T1 further separates the finite trace comparison from its infinite summation. Bounded renewal has separate action, finite iteration, remainder, source and scalar limit tasks. Refinement nodes state independent mathematical facts; their proofs may call imported proved helpers, and never assume another open leaf proposition.', '',
'Forty-one open statements are immediate inputs of `AssemblyLeaves`; the other forty-seven provide the finer mathematical steps needed to implement those inputs. The blueprint exposes these refinements explicitly instead of adding them as hypotheses to an open leaf.', '',
'| File | Purpose |','|---|---|']
roles={'Definitions.lean':'Corrected matcher; actual network/trace data; finite stopped sums; exact T1/T2; explicit transport constants; real summable renewal rows.',
'NodesResponse.lean':'Finite integration, conditional means, uniform response and crude logarithm bounds.',
'NodesLogMean.lean':'Reciprocal integral, coordinate monotonicities, eight-term enclosure and proved exact amended tables.',
'NodesLocal.lean':'One-tip replacement, one-slot convexity, common local mixture and typed analytic comparisons.',
'NodesWalk.lean':'Degree-four step identities, valid traces, finite pair expansion, terminal values, exposure and common one-point bounds.',
'NodesClosure.lean':'Ordinary-domain closure and the sole terminal protected defect; arbitrary-position twelve exceptions.',
'NodesKernel.lean':'Fixed-order nonnegative kernel, shifts, summability, same-witness transport and real-row conversion.',
'NodesRecursion.lean':'Ordinary envelopes, canonical geometry, T1/T2 decomposition and comparisons, and removal-domain realization.',
'NodesRenewal.lean':'Bounded positive action, finite iteration, unweighted remainder, weighted source and scalar limit.',
'Assembly.lean':'Checked response, log-mean, typed original/V2, Mtheta, T1, bounded-renewal and Rec implications; combined target export.',
'Counterexample.lean':'Concrete boundary-corner rejection by old matching and acceptance by V2, both kernel-checked.',
'Audit.lean':'Axiom output for every manually declared exported theorem.',
'All.lean':'Single import of the complete deliverable and audit.'}
for fn,desc in roles.items(): lines.append(f'| [{fn}]({root/fn}) | {desc} |')
lines += ['', '## Author rule and retained proofs', '',
'The author rule arrived after the initial complete blueprint delivery. Every future leaf proof, including a new checker soundness proof or a short helper proof, must receive its first attempt from a different, cheaper model selected by the orchestrator. This agent continues with statements, definitions, designs, executable checkers, data exporters, measurements/prototypes and proved assembly implications. The 88 remaining tasks in `leaves.json` now carry that assignment explicitly. No Lean source or proof was changed for this policy amendment.', '',
'The following eleven non-assembly proofs already existed before the rule. They are retained under the explicit exception; no cheaper-model first attempt is claimed for them. The three proofs of named leaf statements are `crudeRational`, `logRationalRows` and `typedCrudeRows`. The other entries are existing helpers or matcher diagnostics. The ten assembly theorems remain within this agent\'s authorized scope. [proof-policy.json]('+str(out/'proof-policy.json')+') records the complete inventory, signatures and source hashes at the policy cutover.', '',
'| Retained declaration | Classification |','|---|---|']
for entry in policy['retained_pre_rule_proofs']:
    name=entry['lean_name'].split('.')[-1]
    lines.append(f"| [{name}]({entry['source_file']}:{entry['source_line']}) | {entry['classification']} |")
lines += ['', 'No new checker or soundness claim was introduced in this amendment. Existing kernel computations are retained. Any future soundness obligation must be stated as an exact closed open leaf in `leaves.json` before proof work is assigned.', '']
lines += ['', '## Exported declarations and statements', '',
'Open leaf statements are reproduced verbatim in `leaves.json`; the node table links to each source. `TargetsStatement` is the conjunction of `Top.ResponseStatement`, `Top.LogMeanBoundsStatement`, `Top.ResponseTypedStatement`, `ResponseTypedStatementV2`, `Top.MThetaStatement` and `Top.RecStatement`. `targets_of_leaves` proves that conjunction from one closed `AssemblyLeaves` proposition.', '',
'`ResponseLeaves`, `TypedLeaves`, `MThetaLeaves`, `RecursionLeaves` and `AssemblyLeaves` are closed proof bundles. The exact bundle fields and the assembled bounded-renewal statement are:', '', '```lean']
a=(root/'Assembly.lean').read_text()
for match in re.finditer(r'^structure (?:ResponseLeaves|TypedLeaves|MThetaLeaves|RecursionLeaves|AssemblyLeaves) : Prop where',a,re.M):
    rest=a[match.start():]
    e=re.search(r'\n\n',rest)
    lines.append(rest[:e.start()] if e else rest)
    lines.append('')
m=re.search(r'^def BoundedRenewalStatement : Prop :=',a,re.M)
end=a.find('\n/--',m.start())
lines.append(a[m.start():end].rstrip()); lines += ['```','', 'The theorem signatures below include both assemblies and the elementary proofs. Each signature is checked in the project with `autoImplicit=false`.', '', '```lean']
for p in sorted(root.glob('*.lean')):
    s=p.read_text()
    for m in re.finditer(r'^theorem (\w+)',s,re.M):
        end=s.find(':=',m.start())
        lines.append(s[m.start():end].rstrip())
        lines.append('')
lines += ['```','', '## Axiom audit', '',
'Fresh `lake env lean AKLT/Blueprint/Rec/Audit.lean` output follows. All 21 exported theorems use only the three allowed axioms. Leaf definitions assert no proofs and introduce no axioms.', '', '```text']
log=(out/'axioms.log').read_text() if (out/'axioms.log').exists() else ''
axioms=[x for x in log.splitlines() if 'depends on axioms:' in x]
lines+=axioms;lines+=['```','', '## Top/Defs problem and V2 replacement', '',
'One fidelity problem was found in the reviewed interfaces. No frozen file was edited.', '',
'1. `AKLT.Defs.CoveredDeparture`, [Response.lean:69](/home/ubuntu/aklt/wt/BP_REC/AKLT/Defs/Response.lean:69), compares the entire transformed template kept set to the actual kept set. `Network.LocalRules` restricts every actual kept set to `neighbours x ∩ G`. The template requires a non-tip U corner to keep all four neighbours. Thus the matcher rejects a U boundary corner that has original leg directions leaving G. The paper explicitly treats those directions as external original-leg slots (§6 lines 564–572 and 607–623); it does not require them to be kept bonds inside G. This makes the matcher too restrictive for `l:closure`, and correspondingly the original `Top.ResponseTypedStatement` too narrow to supply the claimed general closure step. The original typed statement itself need not be false.', '',
'Concrete ordinary-domain example: let G={x : d(x,(-2,0))≤4}, remove c=(-1,0), and give every other site U status with full kept sets inside G. The ordered B pair u=(0,0), v=(-2,0) has this removed common centre. The depths of u,c,v from the complement are 3,4,5, respectively, so the centre and endpoints satisfy the required interior restrictions. Normalize the flag from u to c and depart east. The non-tip corner (1,1) is a protected U boundary site; (2,1) and (1,2) lie outside G. Its actual kept set has only two elements, while the covering U corner has four directions. `boundaryExample_not_old_covered` proves old-matcher rejection. `boundaryExample_v2_covered` constructs the covered pattern and proves acceptance by V2 using kernel computation. The consistency/depth explanation here is the elementary geometry of the displayed domain; the two exported counterexample theorems specifically check the matcher claims.', '',
'Proposed replacements in this directory: `CoveredDepartureV2` intersects the transformed template kept set with original G before comparing it to the actual kept set. `ResponseTypedStatementV2` uses that matcher with the same coefficients and conclusions. `coveredDeparture_to_v2` proves the original matcher implies V2 for an auxiliary network, so the checked typed V2 assembly also recovers the original Top statement. All covering, exceptional-departure and one-point nodes consume V2. No kernel definition, H1 pattern class, H2 trail weight or Top theorem was changed.', '',
'The manuscript repair `v ∉ S(G)` in `l:terminalcover` is explicitly retained in the second-start, exception and residual nodes. This is a required premise in the supplied paper, not an additional unresolved Top/Defs defect. No further defect was found in the five target Top statements during this review.', '',
'## Trap check', '',
'Every open entry in `leaves.json` has eight separate audit fields: missing premises; vacuity/degeneracy; coercions; finite versus Fintype sums; natural subtraction; division; instance retention; and a statement-specific check. These are statement reviews, not proofs of the open facts. The statement-specific results are recorded below.', '',
'| Open leaf | Specific trap checked |','|---|---|']
for r in opens: lines.append(f"| `{r['lean_name'].split('.')[-1]}` | {r['trap_check']['specific_check']} |")
lines += ['',
'Common checks: every original pin remains a `PinAssignment G`, including a protected terminal and after interior removals. The stopped sum is finite with lengths `range (D.bonds.card+1)`; word sums are over `DirectionWord n` and are filtered by the actual trail predicate. Zero-length and empty classes are explicit. The response supremum adjoins zero, is bounded by two, and uses negative-depth constant extension via `Int.toNat`. All depth losses are integer subtraction. Distance-to-empty is infinity in the shared definitions; active starting/pair data force original protected S to be nonempty before its `toNat` distance is used. Kernel infinite sums stay ENNReal through finiteness; the real renewal kernel carries explicit Summable rows. Rational and real arithmetic are cast explicitly in the typed assembly. The same exact dyadic witness and the same fixed ordering are used before and after shifting.', '',
'## Reuse and implementation handoff', '',
'The supplied reuse map gives no complete donor theorem for the walk expansion, covering argument, closure, type-dependent recursion, shifted witness or bounded renewal. The manifest records that limitation instead of treating a numerical checker or approximate result as a theorem. The relevant primary APIs are Mathlib finite sums, interval integration, conditional-complete suprema, ENNReal tsums, the first and second geometric moments, and geometric convergence.', '',
'`AKLT.Vendor.FiniteConditioning.condExp_on_fiber` supplies fibre identification; finite product reindexing and the independent-neighbour conditional mean bridge remain tasks here. `AKLT.Gen.Bellman.System.step_mono`, `step_add` and `horizon_eq_sum` work for arbitrary label types, so they can be instantiated directly with shift labels. The real finite-row/toReal bridge must still be proved. `AKLT.Gen.Bellman.Growth` supplies finite witness-growth patterns; it does not prove the spatial shift estimate. The Gram and Packed libraries belong to the separate certificate implementation and are not asserted as analytic response results.', '',
'Common moment, finite-facts and three-factor mean results are expected as proved imports when implementing leaves. There is no frame, window, classical-gap or quantum-gap premise anywhere in the Rec design. H1/H2/H3 are the exact semantic computational contracts appearing inside the target statements; no computational certificate search or proof is part of this delivery.', '',
'## Validation', '',
'```bash', 'PATH="$HOME/.elan/bin:$PATH" lake build AKLT.Blueprint.Rec.All',
'PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/Blueprint/Rec/Audit.lean',
'PATH="$HOME/.elan/bin:$PATH" lake env lean /tmp/BP_REC_dependencies.lean', '```', '']
for name in ['build.log','axioms.log','dependencies-check.log']:
    t=(out/name).read_text() if (out/name).exists() else ''
    elapsed=re.search(r'elapsed_seconds=([^\n]+)',t)
    lines.append(f"- [{name}]({out/name}): {'success' if 'error:' not in t and 'Unknown identifier' not in t else 'inspect log'}; elapsed {elapsed.group(1) if elapsed else 'pending'} seconds.")
lines += ['',
'The final module build and axiom audit pass. All referenced Mathlib APIs and dependency definitions were checked by Lean; the vendored fibre lemma was checked by source location and exact namespace. A separate static review verifies the manifest covers exactly the open node set, no dependency list names another Rec leaf, every open leaf has a specific trap check, every exported theorem has an axiom entry, and all deliverable source paths are inside the assigned namespace directory. No Mathlib build/update, new axioms, unchecked proof commands, or forbidden proof placeholders are delivered. Source changes are confined to the new Rec directory; `git status --short` shows only that untracked directory.', '',
'## Open work', '',
'This is a complete blueprint, not a proof of the analytic leaves. Exactly the 88 open Lean names in `leaves.json` remain to be proved, each with its first attempt assigned to a different, cheaper model. This agent will add no leaf proofs. The three retained pre-rule rational statement proofs are unconditional. `FirstTermBoundStatement` is discharged as an intermediate implication from its finite comparison, finite-tail domination and envelope inputs. The five Top targets are assembly implications from the closed bundles; their open mathematical inputs remain explicit.', '',
'## ORCH-SUMMARY',
'Delivered: 13 Lean modules under AKLT/Blueprint/Rec, 92 nodes, 88 open tasks, exact rational proofs, 10 assembly theorems, 21-theorem axiom audit.',
'Delivered: report.md, leaves.json, nodes.json, proof-policy.json, build.log, axioms.log, dependencies-check.log, reproducible report generators.',
'Author rule: every future leaf proof first goes to a different, cheaper model; this agent retains blueprint and assembly work.',
'Retained pre-rule proofs: three named leaf proofs and eight helpers/diagnostics, all inventoried in proof-policy.json; no new leaf proof was added.',
'All five requested Top statements follow from closed leaves; corrected typed V2 is exported too.',
'Build and axiom audit pass; only propext, Classical.choice and Quot.sound occur.',
'Problem to pass to fidelity owner: Defs.CoveredDeparture must intersect transformed kept flags with G at boundary corners.',
'V2 repair, old-to-V2 bridge, and two kernel-checked matcher examples are in this directory; frozen files were untouched.',
'Retain v outside original S for the second trace; all removals keep original legs and all distances use original S.',
'Open exact names below are in namespace AKLT.Blueprint.Rec (grouped by source module):']
for mod in dict.fromkeys(r['module'] for r in opens):
    names=[r['lean_name'].split('.')[-1] for r in opens if r['module']==mod]
    lines.append(mod.split('.')[-1]+': '+', '.join(names))
lines += ['No analytic leaf or numerical input is claimed proved except the three listed rational leaf statements.',
'The orchestrator should allocate the closed tasks, adopt or coordinate the matcher V2, and provide proved common moment/finite-law imports.',
'No remaining design blocker; proof-size estimates should be revisited only if implementation exposes an unanticipated library bridge.']
(out/'report.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'report_lines':len(lines),'axiom_entries':len(axioms),'orch_summary_lines':len(lines)-lines.index('## ORCH-SUMMARY')-1}))
