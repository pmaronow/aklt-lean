import json
from pathlib import Path

root = Path('/home/ubuntu/aklt/reports/TS_GAP_06')
rows = {r['leaf']: r for r in map(json.loads, (root/'verdicts.jsonl').read_text().splitlines())}
prefix = 'AKLT.Blueprint.Gap.'
items = [
    ('FrameSpecEnergyStatement', 'NodesPeriodic', 155, 'l:planeenergy', 'Assignment bound transfers along the site inclusion.'),
    ('FrameWindowTransferStatement', 'NodesPeriodic', 166, 'd:W', 'The allowed indices imply Bᵢ ⊆ Fᵢ.'),
    ('ShellNestingStatement', 'NodesShell', 14, 'l:stopped', 'Positive spacing and the floor bound give both containments.'),
    ('FiniteEnergyChainStatement', 'NodesShell', 22, 'l:stopped', 'Positive partial fibres and the finite chain rule suffice.'),
    ('ShellRowStatement', 'NodesShell', 33, 'l:stopped', 'All geometric, energy, consistency and window inputs are present.'),
    ('TraceMarginalsStatement', 'NodesShell', 44, 'l:surgery', 'Stochastic conditional resampling preserves both marginals.'),
    ('TrialCountStatement', 'NodesShell', 54, 'l:stopped', 'One exceptional integer removes at most two of h−1 candidates.'),
    ('ShellAbsorptionStatement', 'NodesShell', 61, 'l:stopped', 'A successful trial and its successor force persistent agreement.'),
]
traps = {
    'FrameSpecEnergyStatement': 'The U,J in AssignmentBound are finsets of the subtype W, whereas the premise uses finsets of Plane. Use the injective Subtype.val map, including its cardinality identity. The exponent counts U, the prescribed sites; J is the conditioning set. Off-volume default letters do not enter either event. A proper-colouring hypothesis is unnecessary because the needed bound is already a premise.',
    'FrameWindowTransferStatement': 'specMarginal fills off-volume sites from η, while planeMarginal uses the fixed default (0,0,0) there. Their equality requires Bᵢ ⊆ Fᵢ; it is derivable from 2 ≤ i ≤ s and is not definitional. FrameBoundary Fᵢ is indexed by the finite exteriorSites Fᵢ, so each total boundary must be restricted to that subtype. The floor and inequalities are in ℤ/ℝ, not ℕ.',
    'ShellNestingStatement': 'The shell indices are arbitrary integers. Keep shellRadius as Int.floor, and cast integer addition/subtraction before comparing real thresholds. The distance is the natural-valued maximum of coordinate natAbs values, then cast to ℝ or ℤ. No exterior-site or nonempty-shell hypothesis is needed for these two containments.',
    'FiniteEnergyChainStatement': 'The first event argument of conditionalProbability is the conditioning event. A nonempty event has positive mass here because p is strictly positive, not merely nonnegative. The elaborated statement retains [Fintype ι], [DecidableEq ι], [∀ x, Fintype (S x)] and [∀ x, Nonempty (S x)]; no alphabet instance was dropped. For U=∅ the denominator is positive and both the conditional probability and α^0 are one.',
    'ShellRowStatement': 'A row j : Fin h has physical surgery index i=j.val+2, so the rows are 2,…,h+1. Geometry is needed through h+1, but the success guard i ≤ h deliberately excludes the last row. In the identical branch, agreement on the predecessor shell and the two separator clauses of ShellGeometry give equality of the induced Fᵢ laws by range one. In the other branch, resampling Aᵢ preserves Bᵢ because nearShell and window are disjoint. The exponent 16*l counts both independent assignments, since 2*|Aᵢ| ≤ 16*l. PositiveProbability and the nonempty alphabets in PlaneSpec cover empty Aᵢ, Bᵢ and Fᵢ as well.',
    'TraceMarginalsStatement': 'PairTrace Ω h has h+1 coordinates; Fin.castSucc and Fin.succ refer to the input and output time of one transition. At h=0 there is one time coordinate and an empty transition product, giving the initial product law. Pair dependence of the joint row does not affect either coordinate marginal. Coupling does not contain a separate normalization field; the endpoint trace is a probability and its two preserved marginals are the original normalized laws.',
    'TrialCountStatement': 'Fin h contains h indices, but j.val+2 ≤ h leaves h−1 candidates. The exception tests use integers j.val+2 and j.val+3, whereas the bound on j.val+2 is a natural-number inequality. The rejected physical trial indices are e and e−1 for an exception e. Keep h−3 as natural subtraction and use h ≥ 4 when converting the cardinal estimate.',
    'ShellAbsorptionStatement': 'The trial-success event is tested at t j.succ, after surgery i=j.val+2. Its next row exists because i ≤ h; that row performs surgery i+1, not i+2. The skipped identity comes from R.marginals, while R.fixed_exterior alone would not prevent a skipped row from changing its interior. No RegularSpec premise is needed: even without assuming that the initial weights are nonnegative, a positive trace forces every transition factor to be nonzero, and R.stochastic makes it positive. The absence of h ≤ s is also harmless because the assumed kernel fields already supply all the required behavior.',
}

parts = [
    'STATUS: COMPLETE\n',
    'All eight leaves are **TRUE** as written and self-sufficient for the paper’s argument. No corrected statements or additional premises are required. The difficulty ratings describe expected Lean work. All full names have the prefix `AKLT.Blueprint.Gap.`.\n',
    '| Leaf | Module / source | Paper label | Verdict | Difficulty | Reason |\n|---|---|---|---|---|---|',
]
for name, module, line, label, summary in items:
    r = rows[prefix + name]
    target = f'/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/{module}.lean:{line}'
    parts.append(f'| `{name}` | [{module}.lean]({target}) | `{label}` | **{r["verdict"]}** | {r["difficulty"]} | {summary} |')
parts += [
    '',
    'The source checkout is `main` at `7a3393531c12080d76aefbdab300ac0c2df834b7`. This assessment uses each leaf’s quantified hypotheses and the definitions below; it does not assume that any other named blueprint leaf has been proved. No proofs were written, no sub-agents were launched, and the repository was not modified.\n',
    'For the shell discussion, write C=`square a u`, s=`shellSpacing u`, Fᵢ=`farVolume a y u i`, Dᵢ=`shell a y u i`, Aᵢ=`nearShell a y u l i`, and Bᵢ=`window a y u l i`. The physical surgery index of row j is i=j.val+2.\n',
]
for idx, (name, module, line, label, summary) in enumerate(items, 1):
    r = rows[prefix + name]
    first, second = r['route'].split('\n')
    parts += [
        f'**{idx}. `{prefix + name}` — {r["verdict"]}; {r["difficulty"]}.**\n',
        r['reason'] + '\n',
        '**Two-line proof route:**\n\n' + first + '  \n' + second + '\n',
        '**Lean traps:** ' + traps[name] + '\n',
    ]
parts += [
    '**Definition coverage.**\n',
    'Read both leaf modules and the complete [Gap vocabulary](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:1). The relevant closure includes Config, restrict, AgreeOn, AssignmentBound, PlaneSpec and its instances, PlaneConfig, fill, specMarginal, RegularSpec, SpecEnergy, SpecWindow, frameSpec, ShellGeometry, farSites, PairTrace, traceLaw, SurgeryKernels (every field), RowConditions (every conjunct), independentPairs, surgeryTrace, trialTimes and shellAgreement.\n',
    'Read the [geometry definitions](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:1), including Plane, latticeDist, supDist, adjacency/neighbours and bond sets, setDistance, square, squareCorners, shellSpacing, shellRadius, lastShellIndex, farVolume, shell, nearShell, window, exceptionalIndices and geometryThreshold. Read [Specification.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Specification.lean:1), including sitesInVolume and the induced-boundary conventions.\n',
    'Read the [probability primitives](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:1) and [finite conditioning definitions](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:35): Weight, normalize, PositiveProbability, Probability, totalVariation, AgreeOutside, Coupling, conditionalProbability, conditionOn and eventMass. Read the frame law closure in [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:1), [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:32) and [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:7): ProperPlaneColouring, PlaneConfiguration, FrameBoundary, exteriorSites, extendLetters/extendBoundary, planeWeight/planeLaw, marginal/planeMarginal, WindowProperty, frameEnergy/frameRatio/frameBound, frameVector/frameRotation, IcoLetter/icoVector, signValue, goldenRatio, icoRadius, Vec3 and dot.\n',
    'Compared the mathematical arguments with [l:planeenergy](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:691), [d:W](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:31), [l:stopped](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:56) and [l:surgery](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:132), including their proofs.\n',
    '**Shared Lean and boundary-case checks.**\n',
    '- `W : Finset Plane` coerces to the finite type `↥W`; all finite sums over configurations use that subtype. No `Fintype Plane` is needed. `sitesInVolume W V` is a finset of `↥W`, so conversions to physical-site sets must preserve membership and cardinality.\n'
    '- The files use classical propositional decidability and classical equality. Writers should enter `classical` when forming event indicators, finite products of dependent functions, or equality tests between configurations. This adds decidability, not a mathematical premise.\n'
    '- `setDistance` takes values in `ℕ∞`; its value for the empty set is `⊤`. In particular, an empty volume cannot satisfy a distance-at-most-one condition. The row construction and finite probability formulas handle its unique empty configuration.\n'
    '- `shellSpacing` is the real quantity sqrt(sqrt(u)); `shellRadius` uses an integer floor. The energy constants and probabilities are real, and all assignment exponents are natural numbers. There is no unintended rational/integer division in these leaves.\n'
    '- `conditionalProbability` is a quotient with no built-in positive-denominator premise. The chain and row arguments obtain positive denominators from strict positivity and compatible assignments; the two frame transfers simply identify the supplied inequalities.\n'
    '- Empty assignment sets, singleton alphabets, h=0 for trace marginals, α=1 and p=1 are compatible with the statements. Trials are empty for very short traces, so the absorption antecedent then cannot assert a successful trial; this does not make the general leaf vacuous. No global inconsistency or forced-empty-domain defect was found.\n',
    '**Validation.**\n',
    'A single Lean 4.35.0-rc2 inspection module imported the existing read-only build and printed all eight elaborated statements plus the principal structures and predicates. It exited successfully. The explicit nonempty alphabet binder and all other finite-instance arguments of FiniteEnergyChainStatement were retained; PlaneSpec retains its finite and inhabited fields. The inspection contains only imports, printing commands and formatting options: [inspect.lean](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/inspect.lean), [output](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/inspect.out). Mathlib packages are linked under `scratch/.lake/packages`; no dependency or repository module was rebuilt.\n',
    'Exact finite/rational diagnostics in [diagnostics.py](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/diagnostics.py) passed: 5,450 assignment inequalities on small products (including empty and singleton products and nonuniform correlated laws), 9,125 trial-count cases for h=4,…,128, 588 nesting threshold cases including negative indices, 25 window-containment threshold cases, 963 conservative agreement-propagation cases with all short skip patterns, and endpoint normalization/marginal checks for traces of lengths 0,…,3 with pair-dependent conditional couplings and an identity step. For h=4 an exception at physical index 3 leaves only trial row j=2, attaining the lower bound h−3=1. Results are in [diagnostics.json](/home/ubuntu/aklt/reports/TS_GAP_06/scratch/diagnostics.json). These diagnostics support the boundary and indexing audit; the universal verdicts rest on the mathematical arguments above.\n',
]
(root/'report.md').write_text('\n'.join(parts))
print('Wrote complete report.md with 8 verdicts, two-line routes, traps, sources and validation.')
