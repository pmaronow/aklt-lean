from pathlib import Path
import json,re
W=Path('/home/ubuntu/aklt/wt/BP_Q'); R=Path('/home/ubuntu/aklt/reports/BP_Q'); Q=W/'AKLT/Blueprint/Q'
rows=json.loads((R/'leaves.json').read_text()); meta=json.loads((R/'nodes-metadata.json').read_text())
verification=json.loads((R/'verification.json').read_text()); builds=json.loads((R/'build-results.json').read_text())
policy=json.loads((R/'proof-policy.json').read_text())
assert verification['all_commands_succeeded']
ns='AKLT.Blueprint.Q.'
lines=['STATUS: COMPLETE','',
'| Open leaf (`AKLT.Blueprint.Q`) | Paper label and sec3 lines | Difficulty | Closed statement content |',
'|---|---|---|---|']
for row in rows:
    label=row['paper_label']; loc=row['paper_lines']
    lines.append(f"| [{row['short_name']}]({row['source']}:{row['source_line']}) | `{label}`; {loc} | {row['difficulty']} | {row['summary']} |")
lines += ['',
'61 open leaves. Every row is a closed `def …Statement : Prop`, with a paper reference and proof idea in its docstring. The [machine manifest]('+str(R/'leaves.json')+') contains each exact Lean-printed closed statement, original source declaration and context, module, source line, definition/library dependencies, donor pointers, proof-size estimate, route, individual trap review, and required first-attempt routing. No open leaf is asserted as a theorem.',
'', '## Proved and derived nodes', '',
'| Node | Status and exported theorem |', '|---|---|']
for k,v in meta['proved'].items(): lines.append(f'| `{k}` | Proved: `{v} : {k}` |')
for k,v in meta['derived'].items(): lines.append(f'| `{k}` | Derived from smaller nodes: `{v}` |')
lines += ['',
'The four derived nodes are not writer assignments and do not occur in leaves.json. Their smaller leaves occur exactly once in the orchestration bundles. The six proved nodes are also excluded from leaves.json.',
'', '## Author rule on first proof attempts', '',
'The resumed orchestrator message requires every new leaf proof attempt, including a short proof or checker soundness proof, to start with a different, cheaper model. The blueprint author may continue statements, definitions, designs, checkers, data exporters, measurements, prototypes, and proved assembly theorems. This rule is now recorded in [proof-policy.json]('+str(R/'proof-policy.json')+') and in the first_attempt field of every open manifest entry. Model assignment remains with the orchestrator; no new leaf proof was attempted during this resumed turn.', '',
'The following proofs predate the rule and are retained. The first six are the named leaf proofs already counted above; the normalization helper and definition-field obligations are listed separately so no existing proof is hidden by its file placement.', '',
'| Existing declaration | Pre-rule proof retained |', '|---|---|']
for entry in policy['retained_pre_rule_proofs']:
    note={'named_leaf':'Named leaf proof', 'existing_mathematical_helper':'Generic scaled-normalization helper; already proved before the rule',
      'definition_with_existing_linearity_fields':'Existing map_add and map_smul proof fields inside a definition'}[entry['kind']]
    lines.append(f"| [{entry['lean_name']}]({entry['source']}:{entry['source_line']}) | {note} |")
lines += ['',
'All 61 open leaves remain open, with exact closed statements in leaves.json. The existing 14 composition theorems and the pre-rule normalization helper remain in Assembly.lean. No mathematical checker or new checker-soundness proof is part of this blueprint; verify.py checks existing builds, declarations, axiom output and report data. Lean source content and the existing axiom audit are unchanged by this policy/report update.',
'', '## Files', '', '| File | Contents |', '|---|---|']
desc={
'Definitions':'Spinor compatibility and kernels; physical/pair polynomials; weighted norms; signed beta/rho and fibre projection; boundary-absorbed product reference.',
'NodesFrames':'Frame geometry, moment encoding, separation and attained bound; rational rotation and scalar proofs.',
'NodesTight':'Spinor verification, complex degree-four kernels, local Gram expansion, tensorization.',
'NodesStar':'Fixed-star positivity, nonempty spectrum, spectral minimum, coercivity and amplification; proved multiplicity-two count.',
'NodesPolynomial':'Physical polynomial evaluation/reconstruction, pair divisibility, spectators, nonassociation, and local kernel facts; proved finite prime product.',
'NodesQuantum':'Determinant modulus, signed factorization, weighted ground transform, fibre projection and intertwining, quotient variance.',
'NodesEnergy':'Positive weights, consistent conditioning, Markov dependence, finite energy, partial assignments, product-reference density comparison; proved positive normalization.',
'NodesSplits':'Second split of pair spin identification, determinant primality, centre-degree cancellation, and star relabelling.',
'Assembly':'15 proved composition/helper theorems, six closed conjunction bundles, and the full five-target theorem.',
'All':'Import entry point.',
'Audit':'71 closedness checks and all 21 exported theorem axiom checks.'}
for m,d in desc.items(): lines.append(f'| [{m}.lean]({Q}/{m}.lean) | {d} |')
for f,d in [('leaves.json','61 open assignments, exact closed statements, first-attempt routing and individual trap checks.'),('proof-policy.json','Author rule, retained pre-rule proof inventory, declaration digests and unchanged Lean source snapshot.'),('exported-declarations.txt','Lean-printed statement definitions, bundles, and all exported theorem signatures.'),('axioms.txt','Verbatim axiom output for all 21 theorems.'),('verification.json','Machine-readable validation result.'),('build-results.json','Exact build commands, timings, exit codes and logs.'),('verify.py','Reproducible direct-Lean verification, dependency ordered, at most four Lean processes.'),('prepare.py','Recreates manifest and audit files from checked node sources plus routing metadata.')]:
    lines.append(f'| [{f}]({R}/{f}) | {d} |')
lines += ['', '## Assembly statements and dependency graph', '',
'The public target theorems are `threeFrames_of_leaves`, `tight_of_leaves`, `star_of_leaves`, `qd_of_leaves`, and `planeEnergy_of_leaves`. They conclude the existing Top declarations without modifying them. The fully composed theorem has this type:', '',
'```lean',
'AKLT.Blueprint.Q.allTargets_of_leaves',
'  (hMom : AKLT.Blueprint.Top.MomentsStatement)',
'  (hKernel : AKLT.Blueprint.Top.TorusKernelStatement)',
'  (hFrames : AKLT.Blueprint.Q.FramesInputs)',
'  (hTight : AKLT.Blueprint.Q.TightInputs)',
'  (hStar : AKLT.Blueprint.Q.StarInputs)',
'  (hPoly : AKLT.Blueprint.Q.PolynomialInputs)',
'  (hQuantum : AKLT.Blueprint.Q.QuantumInputs)',
'  (hEnergy : AKLT.Blueprint.Q.EnergyInputs) :',
'  AKLT.Blueprint.Top.ThreeFramesStatement ∧',
'  AKLT.Blueprint.Top.TightStatement ∧',
'  AKLT.Blueprint.Top.StarStatement ∧',
'  AKLT.Blueprint.Top.QDStatement ∧',
'  AKLT.Blueprint.Top.PlaneEnergyStatement',
'```', '',
'Every hypothesis in this target assembly is a closed Prop. The six `…Inputs` definitions are transparent conjunctions of the 61 open leaves, not new hypotheses hidden in structures or instances. No other external Top result is needed.', '',
'```mermaid', 'flowchart TD',
'  M[External MomentsStatement] --> F[ThreeFramesStatement]',
'  FL[7 frame leaves] --> F',
'  F --> T[TightStatement]',
'  TL[8 tight leaves] --> T',
'  K[External TorusKernelStatement] --> S[StarStatement]',
'  SL[8 star leaves] --> S',
'  PL[15 polynomial leaves + proved primeProduct] --> LK[Local kernel factorization and ground evaluation]',
'  F --> D[QDStatement]',
'  T --> D',
'  S --> D',
'  K --> D',
'  LK --> D',
'  QL[10 quantum leaves] --> D',
'  F --> E[PlaneEnergyStatement]',
'  EL[13 energy leaves] --> E',
'```', '',
'The QD assembly derives the density identity by summing the raw product weight with the physical isometry. For an orthogonal vector it forms the explicit ground quotient, proves its variance is the physical norm squared, transports each one-site Dirichlet term to a beta projection residual, applies the local kernel inclusion, and sums the star coercivity bounds. The last arithmetic step is proved for every real Poincare lower bound gamma; it does not add gamma>0.', '',
'The finite-energy assembly first extracts the numerical two-sign `interactionBounds` from ThreeFramesStatement. Its finite-model leaves take those explicit bounds as a mathematical premise, so their writers do not repeat the geometric separation proof. The block comparison keeps every boundary factor inside the positive product reference, compares unnormalized conditional-variance minima, and cancels the common interaction mean once, giving exactly r_b^(number of internal bonds).', '',
'All exported theorem signatures, including every explicit hypothesis, follow verbatim from Lean:', '', '```text']
exports=(R/'exported-declarations.txt').read_text()
start=exports.index('AKLT.Blueprint.Q.threeFrames_of_leaves ')
lines += [exports[start:].rstrip(),'```','', '## #print axioms', '',
'Verbatim output of the commands in Audit.lean, including every assembly theorem and every immediate proof:', '', '```text', (R/'axioms.txt').read_text().rstrip(), '```', '',
'All entries use exactly the allowed set `{propext, Classical.choice, Quot.sound}`. There are no additional mathematical axioms and no forbidden proof placeholders or computation escapes.', '',
'## Trap review', '',
'This is a statement/design audit, not a proof of the open facts. Each of the 61 leaf definitions was reviewed for all seven requested categories; the per-leaf record is in leaves.json. The Lean audit also checks all 71 statement declarations as closed Props and prints their actual instance binders in exported-declarations.txt.', '',
'- Missing premises: generic finite lemmas state their numerical, full-support, symmetry, nonzero, degree, and isometry premises inside the closed definition. Finite-model energy lemmas explicitly require interactionBounds. No open leaf takes another `…Statement` as a hypothesis.',
'- Vacuity: StarWitness supplies nonempty positive spectrum before sInf reasoning. Generic spectral-minimum leaves require an actual positive eigenvalue. Empty alphabets cannot meet the positive local probability or local Gram resolution premises; those premises are supplied from genuine frames in the assembly.',
'- Empty/degenerate cases: positive normalization explicitly requires a nonempty state space. An empty physical plane volume has one configuration; its products and normalizer are one. Partial assignments on U=empty have probability one. Density comparison gives gap one when there are no internal edges. Zero polynomials and physical vectors are covered by support statements and nonzero-factor cancellation. Spectator amplification allows n=0 without asserting a positive spectrum there.',
'- Coercions: Vec3 is a Pi type whose norm is not the Euclidean norm, so all geometric leaves use dot/normSq. The distance route explicitly transfers to EuclideanSpace before using its triangle inequality. Weights and quadratic forms are real; amplitudes, inner products, spinors and polynomial coefficients are complex. The first inner-product slot is conjugate linear.',
'- Finset/Fintype: torus Bond indexes count each unoriented edge once; incident products use the four actual bonds. Star enumeration and double counting handle periods three. Plane subsets are reindexed through their volume subtype with both subset premises, preserving cardinality. Dependent Fintype families are explicit binders in tensor and finite-product lemmas.',
'- Natural subtraction: physical j is in Fin 5. Kernel exponent differences are treated in the appropriate j<=k branch. Relative rotation uses an explicit natural witness between one and two. Degree saturation uses Euler derivation cancellation and never subtracts possibly larger multidegrees.',
'- Division: the spinor pole is handled before any square-root division. Binomial denominators have j<=4. norm(B), ground evaluations and beta are explicitly nonzero where canceled. Positive probabilities and full support supply event/fibre denominators. The interaction mean, m, M, 2-b and all scalar normalizers are positive before comparison.', '',
'Individual leaf-specific audit notes:', '', '| Leaf | Trap check |', '|---|---|']
for row in rows: lines.append(f"| `{row['short_name']}` | PASS — {row['trap_note']} |")
lines += ['', '## Top/Defs problems found', '',
'None found in the five assigned Top statements or the definitions used by them. No existing Top or Defs file was edited, and no V2 replacement is needed.', '',
'TorusKernelStatement exposes a global ground line and nonvanishing, not the local R={x} factorization consumed by quantumfibre. The local polynomial nodes and localKernelFactorization_of_leaves supply that separate bridge. The generic physical polynomial reconstruction explicitly assumes multihomogeneity; treating polynomialState as an inverse on arbitrary polynomials would be false.', '',
'## Proof routing and scope', '',
'The proposed routes use only finite sums, finite matrices and Mathlib polynomial/spectral infrastructure. Donor pointers are candidates for writer reuse, not already imported facts establishing AKLT bridges. In particular, the Physlib Clebsch-Gordan algebra still needs the displayed normalization and Hermitian coordinate bridge; the QICLean spectral theorem still needs the actual matrix/spectrum identification; FiniteConditioning identifies fibre means but does not supply the complex product Poincare theorem. The generic Gen/Gram, Gen/Bellman and Gen/Packed libraries are not needed for these five analytic/algebraic targets.', '',
'The representation-identification step is realized by fixed 25-dimensional Casimir calculations, diagonal-kernel rank, and subspace dimension equality, rather than formalizing irreducibility for every degree d. This is a finite alternative for precisely the spin-two/spin-four facts used by the targets. The local divisibility export is only the R={x} case needed for QD; the global torus kernel is an external Top input. Proper-colouring existence (l:colour) and lifted-square gauge (l:boxlift) are outside the five assigned targets and are not exported here.', '',
'All 61 writer assignments have estimated proof bands <=400 lines, with easy/medium/hard routes recorded in the manifest. These are planning estimates, not claims that those proofs have been written. The largest bridges have a second split in NodesSplits.lean. The degree-cancellation route uses the weighted Euler identity to keep the remaining generic algebra step bounded.', '',
'## Verification', '',
'Reproduction command (dependency ordered; it does not update Lake, build Mathlib, or edit package sources):', '',
'```bash', f'python3 {R}/verify.py', '```', '',
'The verifier runs `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false <file> -o <local .olean>` for the 11 Q modules and the same strict options for the printed statement export. All commands use the project Lean toolchain through `$HOME/.elan/bin`.', '',
'| Check | Seconds | Exit |', '|---|---:|---:|']
for b in builds: lines.append(f"| `{b['module']}` | {b['seconds']:.3f} | {b['exit_code']} |")
lines += ['', f"Final verification wall time: {verification['elapsed_seconds']:.3f} seconds; at most four concurrent Lean processes. All checks succeeded. Logs contain no warnings. The forbidden-construct scan is empty. Only AKLT/Blueprint/Q is changed in the worktree; report artifacts are under the assigned report directory.", '',
'## ORCH-SUMMARY', '',
'- Delivered 71 closed node Props, six immediate node proofs, four derived bridge nodes, and all five checked Top assemblies.',
'- Full checked entry point: AKLT.Blueprint.Q.allTargets_of_leaves.',
'- New rule recorded: every first leaf proof attempt goes to a different, cheaper model; no new leaf proof attempted on resume.',
'- Retained pre-rule proofs: six named leaves, normalize_from_scaled, and linearity fields in coherentMap/pairDiagonal; full inventory in proof-policy.json.',
'- External inputs: AKLT.Blueprint.Top.MomentsStatement and AKLT.Blueprint.Top.TorusKernelStatement.',
'- Open work: exactly the following 61 names, all in namespace AKLT.Blueprint.Q; leaves.json is authoritative.']
for m in ['NodesFrames','NodesTight','NodesStar','NodesPolynomial','NodesSplits','NodesQuantum','NodesEnergy']:
    ns2=[x['short_name'] for x in rows if x['module'].endswith('.'+m)]
    lines.append('- '+m+': '+', '.join(ns2)+'.')
lines += [
'- Every open leaf is closed; model separation bounds are explicit premises, not an assumed ThreeFramesStatement inside an open leaf.',
'- Immediate and derived nodes must not be assigned again; no V2 replacement or Top/Defs repair is requested.',
'- Deviations: fixed pair-Casimir proof replaces general all-degree SU(2) irreducibility; only singleton-region local divisibility is exported.',
'- Scope exclusions: l:colour and l:boxlift; no unconditional AKLT gap theorem is claimed by this design task.',
'- Proof-size/hour bounds are estimates; prioritize polynomial embedding, pair/spectator transport, star chart, and centre-degree cancellation.',
'- Orchestrator should pass the singleton local-factorization export to the global kernel owner to avoid duplicate algebra work.',
'- All 21 exported theorem axiom sets are allowed; final verification passes (11 Q modules plus declaration export, max four Lean processes).']
report='\n'.join(lines)+'\n'
assert len(report.split('## ORCH-SUMMARY\n',1)[1].splitlines())<=25
(R/'report.md').write_text(report)
print(f"Wrote {R/'report.md'} ({len(lines)} assembled lines, {len(report.splitlines())} rendered source lines)")
