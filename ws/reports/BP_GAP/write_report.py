import json,pathlib,re
r=pathlib.Path('/home/ubuntu/aklt/reports/BP_GAP')
w=pathlib.Path('/home/ubuntu/aklt/wt/BP_GAP')
nodes=json.loads((r/'nodes.json').read_text())
leaves=json.loads((r/'leaves.json').read_text())
leafnodes=[x for x in nodes if x['status']!='assembled']
axioms=[s for s in (r/'axioms.log').read_text().splitlines() if 'depends on axioms:' in s or 'does not depend on any axioms' in s]
assert len(axioms)==17,len(axioms)
assert all(s.endswith('[propext, Classical.choice, Quot.sound]') for s in axioms)
text=['STATUS: COMPLETE','', '| Leaf (namespace `AKLT.Blueprint.Gap`) | Paper label / locator | Difficulty | State |', '|---|---|---|---|']
for x in leafnodes:
 n=x['lean_name'].rsplit('.',1)[1]
 link=f'[{n}]({w/x["file"]}:{x["line"]})'
 state='proved' if x['status']=='proved' else 'open; main assembly' if x['in_minimal_mainW_assembly'] else 'open; supporting library'
 locator=x['paper_locator'].replace('|','\\|').replace('\n',' ')
 text.append(f'| {link} | {locator} | {x["difficulty"]} | {state} |')
text += ['', '## Files and scope', '',
 'The blueprint contains 67 leaf statements: 58 open and 9 proved. The six additional `…Statement` definitions are intermediate interfaces proved by assembly. Of the open leaves, 37 occur in the minimal direct assembly and 21 supply the finite library, the finer proof decomposition, or the terminal-radius corollary. All open leaves are closed definitions of `Prop`; none assumes another named closed leaf. Local data such as a specification, a stopped estimate for fixed parameters, or an eigenvalue bound for one kernel remain explicit mathematical premises.', '',
 f'- [Definitions.lean]({w}/AKLT/Blueprint/Gap/Definitions.lean): finite products, full conditional laws, plane specifications, shell row/path certificates, labelled torus blocks, coordinate changes, and scale conditions.',
 f'- [NodesFinite.lean]({w}/AKLT/Blueprint/Gap/NodesFinite.lean): Appendix `a:finite`, signed frame density comparison, and coordinate transport.',
 f'- [NodesShell.lean]({w}/AKLT/Blueprint/Gap/NodesShell.lean): `l:stopped`, `p:surgery`, and `l:hamming`.',
 f'- [NodesPeriodic.lean]({w}/AKLT/Blueprint/Gap/NodesPeriodic.lean): `t:periodic`, `l:colour`, `l:boxlift`, and the actual-frame interface adapters.',
 f'- [NodesMain.lean]({w}/AKLT/Blueprint/Gap/NodesMain.lean): intermediate result statements, closed input bundles, and elementary proved nodes.',
 f'- [Assembly.lean]({w}/AKLT/Blueprint/Gap/Assembly.lean): eight proved assembly theorems, including the requested `MainWStatement`.',
 f'- [All.lean]({w}/AKLT/Blueprint/Gap/All.lean) and [Audit.lean]({w}/AKLT/Blueprint/Gap/Audit.lean): import entry point, 73 closedness checks, the exact target signature check, and all 17 theorem axiom audits.',
 '- [leaves.json](leaves.json): one record per open leaf, with exact Lean statement, module, paper locator, difficulty, dependencies, route, reuse pointers, proof-size estimate and eight-category trap check.',
 '- [nodes.json](nodes.json): includes the proved leaves and the assembled interfaces as well.',
 '- [statements.txt](statements.txt): Lean-printed exact definitions and theorem signatures; [trap-checks.md](trap-checks.md): the per-leaf fidelity review.', '',
 'Only `AKLT/Blueprint/Gap/` was added in the worktree. Top, Defs, Challenge, vendored code and package sources were not edited. No sub-agents were used.', '',
 '## Proof assignment policy', '',
 'The author rule received after the initial delivery applies to every future written leaf proof, including short proofs and checker soundness lemmas: its first attempt must come from a different, cheaper model. No leaf proof has been added or attempted by the architect after receiving that rule. The 58 unproved leaves remain open in `leaves.json`, with their exact closed statements and an explicit first-attempt assignment field. Assembly proofs remain within the architect scope.', '',
 'The following nine proofs were written before the new rule and are retained under its explicit exception. All are in `AKLT/Blueprint/Gap/NodesMain.lean`: `groundOrthogonality`, `rayleighBound`, `positiveToProbability`, `independentPairsProbability`, `diagonalCoupling`, `deltaBounds`, `powerCount`, `poincareMonotone`, and `periodicBudget`. Their exact statement/proof mapping and source locations are recorded in [proof-policy.json](proof-policy.json); `nodes.json` marks their provenance. No end-to-end computation modules or checker soundness proofs were added.', '',
 '## Exported theorems and assembly', '',
 'All names below have prefix `AKLT.Blueprint.Gap`. The complete signatures, including every implicit finite instance in each closed statement, are in `statements.txt`.', '',
 '```lean',
 'reversibleSpectral_of_parts :',
 '  LipschitzEigenvalueStatement → ReversibleEigenvalueGapStatement → ReversibleSpectralStatement',
 'finiteContraction_of_parts :',
 '  BlockAverageFormStatement → LipschitzCouplingStatement →',
 '  ReversibleSpectralStatement → FiniteContractionStatement',
 'blockComparison_of_parts :',
 '  ConditionalBlockComparisonStatement → MultiplicityEstimateStatement → BlockComparisonStatement',
 'periodicCriterion_of_parts :',
 '  ContainingBlockCountStatement → ExteriorBlockCountStatement → BlockVolumeBoundStatement →',
 '  PeriodicNeighbourCouplingStatement → FiniteContractionStatement → BlockComparisonStatement →',
 '  PeriodicCriterionStatement',
 'stoppedCoupling_of_parts :',
 '  ShellRowStatement → TraceMarginalsStatement → TrialCountStatement → ShellAbsorptionStatement →',
 '  FiniteTrialFailureStatement → TraceDisagreementStatement → ThresholdSpacingStatement →',
 '  AKLT.Blueprint.Top.ShellGeometryStatement → StoppedCouplingStatement',
 'hammingAtScale_of_parts :',
 '  StoppedCouplingStatement → ScaleGeometryStatement → BinomialTailStatement →',
 '  HammingCardinalityStatement → HammingBudgetStatement → StoppedHammingConversionStatement →',
 '  FarBoundaryEqualityStatement → HammingAtScaleStatement',
 'mainW_of_parts :',
 '  FiniteAssemblyLeaves → ShellAssemblyLeaves → PeriodicAssemblyLeaves →',
 '  AKLT.Blueprint.Top.ShellGeometryStatement → AKLT.Blueprint.Top.ThreeFramesStatement →',
 '  AKLT.Blueprint.Top.StarStatement → AKLT.Blueprint.Top.PlaneEnergyStatement →',
 '  AKLT.Blueprint.Top.QDStatement → AKLT.Blueprint.Top.TorusKernelStatement →',
 '  AKLT.Blueprint.Top.MainWStatement',
 '```', '',
 '`mainW_of_core` is the eighth assembly theorem. It takes the preassembled Hamming/periodic interfaces and the local frame/gauge leaves directly; its exact 22-input signature is printed in `statements.txt`. The nine immediate proofs are `groundOrthogonality`, `rayleighBound`, `positiveToProbability`, `independentPairsProbability`, `diagonalCoupling`, `deltaBounds`, `powerCount`, `poincareMonotone`, and `periodicBudget`; each proves its correspondingly named statement in the node table.', '',
 'The construction chooses `n` from the four `l:hamming` inequalities before any torus periods or colourings, sets `M=n^8` and `L₀=2M+3`, and obtains the classical constant `(499/500)*frameRatio^(2*(2*M+1)*(2*M))`. QD then supplies the quantum constant `(starGap/2)*((499/500)*blockGapConstant M)`, algebraically `(499/1000)*starGap*blockGapConstant M`.', '',
 'The shell geometry Top input is consumed when extracting the local shell facts. PlaneEnergy supplies positivity, consistency, partial-assignment bounds and each lifted plane block gap. ThreeFrames supplies antipodality, positive signed interactions and `frameRatio>0`; Star supplies `starGap>0`. QD is applied after the periodic classical gap, and TorusKernel supplies the final kernel identity. The all-parity colour and local box gauge are internal nodes because Top has no corresponding exports.', '',
 'Hard steps are split further: quantitative conditional patch coupling is separate from a shell row; a row is separate from trace marginals, absorption, trial counting and failure; Lipschitz eigenvalue control is separate from weighted diagonalization; halo injection, bond correspondence, coordinate relabelling, law identity and form/coupling transport are separate. Estimated writer proofs are 80/200/350 lines for easy/medium/hard nodes, within the requested approximate 400-line cap; these are planning estimates, not completed leaf proofs.', '',
 '## #print axioms', '',
 'Actual output for every exported theorem follows. The first eight are the assembly theorems; the remaining nine are immediate leaf proofs. [axioms.log](axioms.log) also contains the closedness and exact-target checks.', '',
 '```text', *axioms, '```', '',
 '## Top/Defs problems found', '',
 'None found in the interfaces used by this part. No V2 replacement is needed. In particular, `conditionalProbability p E A` conditions on `E` first; the PlaneEnergy assignment clause correctly fixes `J` in that argument and prescribes `U` with exponent `U.card`. The shell spacing, integer floor, all-boundary window quantifiers, rate-one Poincare convention and eventual all-parity conclusion agree with the supplied paper.', '',
 'The missing Top exports for `l:colour` and `l:boxlift` are internal-interface gaps, not false statements. The corresponding closed leaves are delivered here. The fixed quantum eigenvector reduction is proved from the actual sum of orthogonal projectors, so it introduces no additional self-adjointness assumption.', '',
 '## Trap review', '',
 'Every one of the 58 open leaves has a detailed `trap_check` object in `leaves.json`, with separate entries for missing premises, vacuity, empty/degenerate cases, coercions, Finset/Fintype sums, natural subtraction, division by zero and retained instances. `trap-checks.md` lists the individual findings. The nine proved leaves are checked by their kernel-accepted proofs and the same closedness audit.', '',
 'The review retains empty products as one-point configuration spaces, zero-probability marginal fibres, empty shell pieces, singleton alphabets, `delta=1`, and equality in `L,N≥2M+3`. It counts all labelled updates and corner halo sites. The shell trial set stops at `h` while the surgery sequence runs through `h+1`. Natural exponents `h-3` and `n-3` have explicit size premises; real terminal-radius powers have a separate zero-base route. The far-site equality requires the seed outside the square. No comparison identifies letters from different site alphabets.', '',
 'Generic finite-product interfaces explicitly quantify the site `DecidableEq` along with `Fintype`. This avoids changing the finite-product enumeration between the kernel, Lipschitz and transport interfaces. The final audit confirms all 73 `…Statement` declarations have type `Prop` with no free external instance arguments.', '',
 '## Validation and remaining work', '',
 '```bash', 'export PATH="$HOME/.elan/bin:$PATH"', 'lake build AKLT.Blueprint.Gap.Audit', 'lake env lean AKLT/Blueprint/Gap/Audit.lean', 'lake env lean /home/ubuntu/aklt/reports/BP_GAP/PrintStatements.lean', 'lake env lean /home/ubuntu/aklt/reports/BP_GAP/CheckDependencies.lean', '```', '',
 'The final measured module build completed in 20.45 s; the direct axiom/closedness audit took 3.45 s, and the Lean statement catalogue took 3.69 s. See `build.log`, `axioms.log`, `statements.txt`, and `dependencies.log`. All commands passed. The dependency check verifies the non-vendor declaration names in the manifest; donor names and scopes were cross-checked against their vendored source and the supplied reuse map. No donor is claimed to prove an entire open manuscript result.', '',
 'The source scan found no forbidden proof constructs; all theorem axiom lists contain only the three permitted axioms. JSON parsing and whitespace checks passed. Lake used the linked prebuilt Mathlib; no update or package-source change was performed. Builds after prerequisite setup followed a single chain of Gap modules.', '',
 'The mathematical leaf proofs remain open by design. This deliverable proves the assembly implications, not an unconditional AKLT gap theorem. There are no outstanding build failures, Top/Defs corrections, external-data requests, or approvals.', '',
 '## ORCH-SUMMARY', '',
 'Delivered: Gap definitions, four Nodes modules, Assembly, All, Audit; report, exact statements, logs and manifests.',
 'Target: `AKLT.Blueprint.Top.MainWStatement` derived by `AKLT.Blueprint.Gap.mainW_of_parts`.',
 'Independent Top inputs: ShellGeometry, ThreeFrames, Star, PlaneEnergy, QD, TorusKernel statements.',
 'Open: 58 leaves; 37 in the minimal main assembly and 21 supporting/library or corollary leaves.',
 'Exact open names below share namespace `AKLT.Blueprint.Gap`:']
open_names=[x['lean_name'].rsplit('.',1)[1] for x in leaves]
for i in range(0,len(open_names),7):text.append(', '.join(open_names[i:i+7])+'.')
text += [
 'Proved leaves: groundOrthogonality, rayleighBound, positiveToProbability, independentPairsProbability, diagonalCoupling, deltaBounds, powerCount, poincareMonotone, periodicBudget.',
 'All eight assembly theorems and all nine leaf proofs use only propext, Classical.choice, Quot.sound.',
 'No Top/Defs problem found; no V2 proposal or frozen-file edit.',
 'Limit: the 58 remaining leaf proofs are not supplied; line/hour estimates remain estimates. No numerical gap or scale is certified.',
 'New author rule: retain the nine pre-rule leaf proofs; every future leaf-proof first attempt, including checker soundness, must use a different cheaper model.',
 'Internal colour/gauge interfaces were added locally because Top has no exports for those paper labels.',
 'Orchestrator: assign the 37 main leaves, schedule the 21 support/corollary obligations as needed, and integrate via Gap.All.',
 'Exact routes, dependencies, locators and trap checks: leaves.json; all closed statements/signatures: statements.txt.'
]
r.joinpath('report.md').write_text('\n'.join(text)+'\n')
trap=['# Per-leaf trap review','', 'All names have namespace `AKLT.Blueprint.Gap`. The exact quantified statements and full eight-category checks are in `leaves.json`. The common checks retain nonempty alphabets, zero or empty products, finite sum indices, explicit cardinal casts, controlled natural subtraction and nonzero conditioning denominators. The following notes record the leaf-specific checks.', '', '| Open leaf | Specific check |', '|---|---|']
for x in leaves:trap.append('| `'+x['lean_name'].rsplit('.',1)[1]+'` | '+x['trap_check']['missing_premises'].replace('|','\\|')+' |')
trap += ['', 'The nine proved leaf statements are listed in report.md; their proofs and closedness checks settle the corresponding edge cases. No open statement was accepted as a proof.']
r.joinpath('trap-checks.md').write_text('\n'.join(trap)+'\n')
orch='\n'.join(text).split('## ORCH-SUMMARY\n',1)[1].strip().splitlines()
assert len(orch)<=25,len(orch)
print('Wrote report.md; ORCH-SUMMARY lines:',len(orch),'Node table rows:',len(leafnodes))
