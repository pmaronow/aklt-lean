#!/usr/bin/env python3
from pathlib import Path
import collections, hashlib, json, re
workspace=Path('/home/ubuntu/aklt/wt/BP_WIN')
root=workspace/'AKLT/Blueprint/Win'
report=Path('/home/ubuntu/aklt/reports/BP_WIN')
entries=json.loads((report/'nodes_inventory.json').read_text())
retained_stems={'MetricFacts','SpanCutParity','LogLipschitz','CutCostNonnegative','WindowCostArithmetic'}
proof_policy={
    'rule':'Every new Lean leaf proof receives its first attempt from a different, cheaper model.',
    'bp_win_author_scope':'Statements, definitions, designs, checkers, exporters, prototypes, measurements and proved assemblies only; no further leaf proof attempts, including checker soundness.',
    'first_attempt_owner':'A different, cheaper model selected by the orchestrator',
    'delegation_status':'Handoff only; no model or sub-agent was launched.',
    'existing_leaf_proofs_retained':sorted('AKLT.Blueprint.Win.'+n[0].lower()+n[1:] for n in retained_stems),
    'new_leaf_proofs_after_rule':0,
    'lean_source_changes_after_rule':False
}

# Each entry records the specific mathematical trap, in addition to the common
# checks on closedness, sums, natural subtraction, divisions and instances.
checks={
'ShellScale':('The hypotheses include l≥1 and u≥geometryThreshold(l); the fourth-power identity is a conclusion, not an assumption.', 'u=0 and small spacings are excluded by the displayed threshold; the square roots are their nonnegative real branches.'),
'CloseCorner':('Distance of the seed to the finite square is exactly one, so the seed is outside but within its one-neighbourhood.', 'The zero-radius square has repeated corner coordinates in a Finset; its strict radius<u filter is empty.'),
'ExceptionalLocalization':('The explicit s²+4s/3<u premise bounds all trial radii, including the last trial floor(s)+1.', 'An empty exceptional set gives a legitimate empty universal statement; a corner witness is retained whenever membership is asserted.'),
'RadiusGap':('s≥16 and i<j are stated; integer indices may be negative and the floor argument still applies.', 'Equality of indices is excluded. The strict gap is larger than 2s/3.'),
'ExceptionalCount':('Both corner localization and the strict radial gap are explicit local premises, together with at most one close corner.', 'An empty exceptional set or empty close-corner filter causes no missing witness; the conclusion is an upper cardinal bound.'),
'SideCornerWitness':('ShellSetup includes the exterior seed condition and the full geometric cutoff; i is in the entire stated trial range.', 'A side that misses the square is omitted by ParallelClearance. Failure of clearance constructs an actual corner witness.'),
'NearShellCount':('Parallel clearance is a premise. ShellSetup supplies s/3>l, so parallel strips cannot contribute.', 'Count with possible overlap across four sides and two perpendicular strips; no disjointness is assumed.'),
'ShellInclusion':('s≥2 and i≥2 imply floor(is)>(i−1)s; no upper trial bound is needed.', 'An empty shell gives an empty inclusion. The inequalities use real spacing, not a rounded spacing.'),
'PredecessorShell':('x is in the old square but outside F_i, and distance at most one to F_i is explicit.', 'If F_i is empty its distance is top, so the distance-one premise cannot hold. No finite default distance is substituted.'),
'SeedSeparation':('s≥2 and i≥2 give radius>(i−1)s>1 for every point of F_i.', 'Empty F_i has distance top; its separation conclusion remains true.'),
'MetricFacts':('The two metrics are the concrete coordinate formulas on the ambient integer plane.', 'Distance-one excludes a zero step; symmetry uses natAbs of a negated integer difference.'),
'FiniteDepth':('G is finite and the ambient plane is infinite; its complement therefore contains a witness.', 'Handles G=∅ and x outside G. toNat is used only after proving depth≠top and recording its cast-back equality.'),
'BoundaryMembership':('The boundary excludes U explicitly; a radius-one sup ball alone would also contain interior sites.', 'U=∅ gives an empty raw boundary and infinite distance. Finiteness is supplied by the Finset definition.'),
'ChainBox':('Only the finite Finsupp support and the two endpoints of each unordered edge are bounded.', 'The zero chain uses any R≥1, so no maximum of an empty nonempty subtype is taken.'),
'DiagonalElimination':('Both valid star edges and even degrees are premises; arbitrary looped or long-edge chains are not claimed fillable.', 'The zero chain is allowed. Coefficients and diagonal cancellation are in ZMod 2, not integer multiplicities.'),
'ColumnFlux':('The chain is even, has only nearest-neighbour edges, and every endpoint is in the explicit integer box.', 'All half-plane degree sums are restricted to finite support; an infinite sum over a half-plane is never used.'),
'TailSupport':('The box bound and zero column flux are explicit premises; without zero flux tails need not vanish below the box.', 'Zero chains and empty support sets P are allowed. Negative integer row indices are retained.'),
'PlaquetteReconstruction':('Evenness, nearest-neighbour support, a valid box, zero flux, and finite support for tail coefficients are all explicit.', 'P can contain additional zero coefficients or be empty. Vertical boundary terms vanish by the endpoint bound.'),
'PlaquetteTriangles':('The plaquette has four unit nearest-neighbour sides; the two triangles use one shared diagonal.', 'The diagonal occurs twice and cancels in characteristic two. No Euclidean planar noncrossing assumption is needed.'),
'CutEdgesNonempty':('A is a finite nonempty set; a maximal first coordinate therefore exists.', 'A singleton is included. The right neighbour is exterior and distinct from its inside endpoint.'),
'LinkedSeparation':('The premise is failure of reachability of crossing edges, not failure of vertex connectivity.', 'When cutEdges is empty the negated premise is false. The conclusion supplies witnesses in both parts.'),
'TriangleCutParity':('LinkClosed includes E⊆cutEdges and closure under all linked crossing edges.', 'A triangle has zero or two crossing edges. The same-component premise prevents a lone selected crossing.'),
'SpanCutParity':('The hypothesis is vanishing on every triangle generator, and membership in their linear span is explicit.', 'Zero, addition and scalar multiplication are proved by span induction, including scalar zero.'),
'TwoCrossingCycle':('Both A and its complement are star-connected and nonempty; both edges are crossing edges and e≠f is explicit.', 'Shared endpoints and one-point connecting paths are allowed. Odd traversal multiplicities yield a finite even chain.'),
'TwoCrossingParity':('E⊆cutEdges, e∈E and f∉E are stated; these already force e≠f.', 'Evaluate only the finite sum over E. Extra zero chain coefficients outside the crossing set do not matter.'),
'OuterEndpointTransfer':('Nonempty cutEdges is explicit, and every pair of crossing edges is joined in the linked-edge graph.', 'Consecutive exterior endpoints may coincide; reflexive path steps handle these repetitions and singleton boundaries.'),
'CrossFacts':('The cross is exactly the centre plus its four physical nearest neighbours.', 'The five points are distinct, its card is five, and its membership characterization is latticeDist≤1, not supDist≤1.'),
'CrossOverlap':('The centres are star-neighbours with sup distance exactly one.', 'Axial and diagonal displacements are both covered. No diagonal-only block exclusion is imposed.'),
'CrossUnion':('The centre set is nonempty and star-connected; the connected-cross and intersecting-cross facts are explicit local premises.', 'A single cross is included. Connectivity is obtained by chains of intersections, not by assuming the crosses are disjoint.'),
'NeighbourDecay':('θ is strictly positive and below one; G is finite, so all boundary depths are finite.', 'Centres or cross points may be outside G with depth zero. The factor θ⁻¹ still gives the correct inequality there.'),
'CrossWeightSum':('f is nonnegative everywhere and c≥0; each cross has five points and each covered value is ≤c times its centre value.', 'The centre set may be empty. Repeated coverage is deliberately overcounted; no disjointness premise is missing.'),
'ConnectedEnumeration':('ConnectedIn contains nonemptiness, so a root can be chosen and all induced graph distances are finite.', 'A singleton gives last=0 and Fin 1. The predecessor condition is required only at positive indices.'),
'CutScales':('CutSetup fixes l=64, u≥390⁴, an exterior seed and 2≤i≤s.', 'The upper bound k≤u−31 is an inequality in real numbers, avoiding truncated subtraction at small u.'),
'CoreConnected':('CutSetup implies 32≤k≤u−31 and puts y in the one-neighbourhood of C.', 'Each clipped coordinate interval contains a shell endpoint, hence the core contains a corner even when a side segment degenerates to a point.'),
'RadialPaths':('Every start site is in the tapered set; h−t≥32 and t≤T are the two invariants.', 'The core case t=0 uses a zero-length path. Inner and outer radial moves are different, and simultaneous maximal-coordinate motion is allowed as a star step.'),
'SquareExterior':('The volume is a finite translated square in the plane, not a periodic torus.', 'u=0 is included; the row at a₂+u+1 still joins all exterior sites.'),
'ComplementEscape':('CutSetup supplies the scale bounds and y outside C; the start is outside U.', 'Use separate outer-radius, inner-radius and failed-taper cases. The last case preserves h−t<32 even if t≤T later fails.'),
'WindowBuffer':('CutSetup fixes the protected physical window width at 64 and a nonexceptional trial.', 'An empty window makes its own inclusion automatic; U remains nonempty by the independent core construction.'),
'RawRange':('Raw boundary membership supplies a star neighbour in U. The near upper inequality uses failure of U at the raw site.', 'The global t≤T+1 bound also covers the far strip; the near h-range is asserted only when t≤T.'),
'RawDistanceObstructions':('The complement of G is B∪Cᶜ∪(C\\F). The three corresponding lower bounds are kept separately before taking a minimum.', 'An empty B or C\\F contributes infinite distance. boundaryDepth remains finite because G is finite.'),
'RawDepthArithmetic':('The unconditional premise is h≥30+t, in addition to t≤T+1; h≥31 alone would be too weak for the far conclusion.', 'Both t≤T and t>T are covered, including equality at T. This scalar node uses real variables, so it does not silently rely on integrality.'),
'RawHeight':('One-Lipschitz h and t at the neighbouring point in U give h≥30+t for every raw boundary site.', 'This is an unconditional estimate for both near and far sites; it supplies the extra premise required by RawDepthArithmetic.'),
'SignedSideExclusion':('The active-side clearance and CutSetup are explicit. Signed coordinate depths treat all positions of the original side.', 'Sides inside C, beyond the selected side, and beyond the opposite side are all treated; none can coincide with a near h-level side.'),
'SquareIntersection':('Both radii are strictly positive, and equality of parallel side coordinates is excluded for both axes and all signs.', 'Intersections at vertices may be counted more than once in the eight-point upper bound; the Finset intersection removes duplicates.'),
'RawLayerCount':('The near h-range, signed noncoincidence and generic eight-point intersection bound are explicit local premises.', 'j=0 may duplicate the two radius choices, which only weakens the upper bound. CutSetup guarantees positive radii of all relevant squares.'),
'NearSeries':('0<θ<1 guarantees summability and 1−θ>0.', 'The first seventeen indices 0 through 16 all have exponent 14; the tail begins at 17. max(j,16)−2 never underflows.'),
'RawWeightSum':('Raw sites lie in C, the near/far depth bounds and per-layer count are supplied, and summability plus its exact majorant are explicit.', 'Either near or far subset may be empty. All finite-to-infinite comparisons use nonnegative summands and the real-power far exponent.'),
'ThickDepth':('Every centre has original depth at least 14; finite-depth Lipschitz yields depth at least 13 for every cross point.', 'An empty centre set gives empty thickening. Positive depth forces membership in G rather than assuming it.'),
'CutSeparation':('B⊆U⊆F, both adjacency buffers, rawBoundary(U)⊆X and X⊆F\\B are all premises.', 'One or both components may be empty. The two sets give the whole disjoint union G\\X; original exterior and window adjacency restrictions are both retained.'),
'OriginalPositivity':('The permitted C finite-facts export is an explicit closed input. The active U network has original pins and degree at most four.', 'G\\Y may be empty even when Y is not a subset of G; that sum is one. Removed tails retain no pins.'),
'PartLawBridge':('The numerator model is concrete, and the actual partSum normalizer is assumed strictly positive for the chosen Bool branch.', 'Zero individual spin weights are permitted. The empty configuration product is inhabited and has mass one.'),
'EnumerationSteps':('X⊆G, depths≥3, injectivity and the earlier-neighbour property are explicit.', 'The first prefix is empty, the final prefix is X, and the singleton order has no nonseed predecessor obligations.'),
'SurvivorGeometry':('RemovalStep supplies membership, permitted removals and original depth≥3.', 'k=0 or 1 is permitted after earlier removals. The seed has exactly four neighbours, and a removed neighbour forces k≤3.'),
'RemovalIntegral':('The finite moment export and RemovalStep are explicit; x has no original leg and at most four incident bonds.', 'No quartic contribution occurs when k<4. Quartic uses the four fixed compass sites, never an out-of-range fourth element of Fin k.'),
'NeighbourFibres':('The moment and three-factor exports are explicit. Surviving neighbours have no mutual bonds or original legs and at most three other factors.', 'Only positive-mass conditioning fibres are controlled. V=∅ has an empty product; zero-mass fibres create no probabilistic assertion.'),
'PairMeanAveraging':('V⊆D, Probability p and NeighbourControl are explicit.', 'V=∅ and singleton V have no unequal pairs. Zero-mass fibres are omitted when averaging the conditional mean identity.'),
'QuarticMeanBound':('Probability p and the explicit unit icosahedron support from the moment export suffice for the bound.', 'An endpoint outside D is extended by zero and remains in the unit ball; no higher moment assertion is used.'),
'PolynomialLower':('The actual probability, k≤4, the pair mean lower bound and the quartic absolute bound are all supplied.', 'The conclusions are 41/50 for k≤3 and 14/25 for k=4. Both are strictly greater than one half, including k=0.'),
'RemovedPairResponse':('Distinct surviving neighbours have distance two and the common newly removed site x; allowed removals remain outside the original protectedSites(G).', 'The exponent is b_G(x)−3 only after finite depth and depth≥3 are justified. Distances never refer to a new hole.'),
'PairDifference':('k≤4 and d≥0 are stated. Each unequal ordered pair has its own response bound.', 'The ordered double sum has factor one half. k=0,1 contribute zero; k=2,3 use the bound three, and k=4 uses six.'),
'LogLipschitz':('Both real arguments are at least one half, hence strictly positive.', 'Equality of arguments is allowed. The proof uses log(a/b) and positive b before dividing.'),
'LogStepIdentity':('Both before- and after-removal normalizers are positive for pinned and free branches; both integration identities are explicit.', 'Logs are expanded only on positive partition ratios. A one-site or empty after-removal volume is included.'),
'LocalLogEstimate':('The two lower bounds, normalizer positivity, pair difference, quartic mean bounds and scalar log estimate are supplied explicitly.', 'The k=4 quartic cost is at most 4/5 and is enlarged to one; the k≤3 branch pays only 2d.'),
'RemovalTelescope':('Both endpoint-prefix identities and every local log increment bound are explicit.', 'The enumeration is nonempty by construction. last=0 gives an empty tail sum and exactly one seed cost.'),
'RemovalCostSum':('Depth≥3 for every X site and θ∈(0,1) justify the shifted-power identity and bounding seed decay by one.', 'The tail sum is enlarged over the injective full enumeration. No independent seed removal or missing quartic term is used.'),
'FrameFibreSum':('Proper colouring, B⊆F and no neighbour of B outside F are explicit, with actual unit frame vectors for original-leg pins.', 'Empty B or empty complementary volume uses finite empty products; frame configurations are reindexed on the actual site sets.'),
'ComplementQuadrature':('Both permitted frame and quadrature exports are explicit. Every summed site has separate degree at most four from its bonds and original legs.', 'Only the complementary partition polynomial is transferred. The unsummed window letters and their actual weights are held fixed.'),
'MarginalNormalization':('B⊆F and the actual plane-weight normalizer being positive are explicit.', 'Empty B is a singleton product; the sum of all fibre numerators is still the full normalizer.'),
'OriginalFactorization':('SeparatingCut supplies the full disjoint union and the absence of inter-piece bonds.', 'A component sum always removes G\\H from original G, so holes introduce no pins. Either or both pieces may be empty.'),
'ComponentPins':('All separation and original-leg conditions are explicit; each original endpoint not in G lies in B or outside F.', 'Shared outside endpoints use the same frame boundary letter. Removed tails contribute the factor one.'),
'WindowWeightPositive':('Proper colouring and the positive frameBound export control every actual internal window bond.', 'The empty window weight is the empty product, hence positive; no alphabet is silently changed to icoVector.'),
'WindowRewrite':('Strict partition positivity, actual window positivity, the normalized fibre formula, cut factorization and component pin independence are all explicit local premises.', 'A fixed exterior/window assignment exists on every finite product. The resulting positive base weight is independent of η, but may depend on κ,F,B and placement.'),
'BoundedTilt':('The state space is explicitly finite and nonempty, w is strictly positive and E≥0.', 'This excludes a zero normalization sum. A singleton state space and E=0 are included.'),
'OverlapMinorization':('Both laws and the reference are probabilities, and p₀≥0 together with both pointwise lower bounds is explicit.', 'Zero atoms are allowed. Normalization itself forces any feasible common minorization to have p₀≤1; the empty state space admits no probability premise.'),
'TailExponential':('θ∈(0,1), u≥1 imply c=−log θ>0 and s>0 before any negative power or division is used.', 'The factorial is the nonzero integer 10!, and the far exponent is a real power, not a truncated natural exponent.'),
'TailThreshold':('The supplied polynomial/exponential estimate holds for every u≥1; the threshold dominates 390⁴, K² and one.', 'The natural ceiling is used only after proving the quantities real and finite. K>0 and s²=√u justify K/s²≤1.'),
'CutCostNonnegative':('A≥2 and θ∈(0,1) make every factor in the displayed cutCost nonnegative.', 'θ≠0 and 1−θ>0 are available; no inverse-at-zero convention is used to justify positivity.'),
'WindowCostArithmetic':('A≥2, θ∈(0,1), both cut mass bounds, tail≤1 and the seed-preserving removal estimate are explicit.', 'All multipliers in the inequalities are nonnegative. The exact integer identity θ^(-3)θ⁻¹=θ^(-4) preserves the displayed cutCost.'),
'FrameWeightPositive':('Proper colouring applies to all internal and original exterior bonds; ThreeFramesStatement gives a positive lower bound.', 'The empty product gives positive weight on an empty volume. The result concerns actual planeWeight before normalization.')
}
assert len(checks)==len(entries),(len(checks),len(entries))
hard={'SideCornerWitness','PlaquetteReconstruction','TwoCrossingCycle','CoreConnected','ComplementEscape','RawLayerCount','NeighbourFibres','FrameFibreSum'}
for e in entries:
    stem=e['lean_name'].split('.')[-1].removesuffix('Statement')
    assert stem in checks,stem
    if stem in hard:
        e['difficulty']='hard'
    e['estimated_proof_lines']={'easy':[20,140],'medium':[120,280],'hard':[220,380]}[e['difficulty']]
    if e['status']=='proved':
        e['estimated_proof_lines']=[0,0]
    e['dependencies']=list(dict.fromkeys(x for x in e['dependencies'] if x!='linarith'))
    assert not any(x in {'FiniteDepth','RawRange'} for x in e['dependencies'])
    e['cross_lane_inputs']=['AKLT.Blueprint.'+x for x in e['dependencies'] if x.startswith('Top.')]
    module=e['module'].split('.')[-1]
    if module=='NodesShell':
        reuse=[{'path':'/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:43','note':'No matching shell-geometry donor. Use the checked Mathlib floor and finite-set APIs.'}]
    elif module=='NodesTopology':
        if stem in {'CrossFacts','CrossOverlap','CrossUnion','NeighbourDecay','CrossWeightSum','ConnectedEnumeration','FiniteDepth','MetricFacts'}:
            reuse=[{'path':'AKLT/Vendor/Balaban/LargeField/Geometry/Lattice.lean:61','symbol':'Balaban.LatticeGeom.Conn','note':'Finite-path infrastructure only; conversion from Fin 2 → ℤ to Plane is still required if reused.'},
                   {'path':'/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:84','note':'The connected-cross and weighted estimate are new.'}]
        else:
            reuse=[{'path':'AKLT/Vendor/Balaban/LargeField/Geometry/Plaquette.lean:85','symbol':'Balaban.LatticeGeom.exists_primitive_of_closed','note':'Cochain/parity proof pattern only; the star-edge triangle argument must be proved.'},
                   {'path':'AKLT/Vendor/Balaban/LargeField/Geometry/BoundaryConnectivity.lean:238','symbol':'Balaban.LatticeGeom.outerBoundary_mateConn','note':'Not directly applicable: donor assumes NN connectivity and uses the NN vertex boundary. The present boundary is the full sup-distance-one boundary.'},
                   {'path':'/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:83','note':'Audit explicitly requires a triangular/star-adjacency bridge.'}]
    elif module=='NodesCut':
        reuse=[{'path':'AKLT/Vendor/FiniteConditioning/P015/P015_FiniteConditioning.lean:79','symbol':'FiniteConditioning.condIndep_of_fiber_indep','note':'Possible conditioning infrastructure only; finite graph factorization and quantitative common minorization remain new.'},
               {'path':'AKLT/Vendor/FiniteConditioning/P015/P015_FiniteConditioning.lean:36','symbol':'FiniteConditioning.condExp_on_fiber','note':'Requires an explicit finite/discrete measure bridge if used.'},
               {'path':'/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:44','note':'No complete cut theorem is imported.'}]
    else:
        line={'NodesTaper':47,'NodesRemoval':45,'NodesTail':48}[module]
        reuse=[{'path':f'/home/ubuntu/aklt/reports/VENDOR_1/reuse-map.md:{line}','note':'No matching complete donor. Prove the explicit finite model geometry/algebra or real exponential estimate with the checked definitions and library lemmas.'}]
    e['donor_reuse_pointers']=reuse
    specific,degenerate=checks[stem]
    source=(root/(module+'.lean')).read_text()
    start=source.index('def '+stem+'Statement : Prop :=')
    body=source[start:]
    body=re.split(r'\n(?:/--|theorem |#print |end )',body,1)[0]
    e['statement_text']=body.rstrip()+'\n'
    e['statement_context']={
        'import':'AKLT.Blueprint.Win.Defs',
        'namespace':'AKLT.Blueprint.Win',
        'open':['AKLT.Defs'],
        'open_scoped':['BigOperators'],
        'noncomputable_section':True
    }
    e['source_file']=str(root/(module+'.lean'))
    e['source_line']=source[:start].count('\n')+1
    e['statement_sha256']=hashlib.sha256(e['statement_text'].encode()).hexdigest()
    if e['status']=='proved':
        assert stem in retained_stems,stem
        e['proof_provenance']='Written before the new author rule; retained under its explicit exception.'
    else:
        e['next_proof_attempt']={
            'owner':proof_policy['first_attempt_owner'],
            'bp_win_blueprint_author_may_attempt':False,
            'includes_checker_soundness':True
        }
    refs=re.findall(r'([\w.]+Statement)',body.split(':=',1)[1])
    assert all(x.startswith('AKLT.Blueprint.Top.') for x in refs),(stem,refs)
    natcheck='No natural subtraction in this statement. Integer coordinate subtractions are signed.'
    if stem in {'NearSeries','RawWeightSum'}:
        natcheck='max(j,16)≥16, so subtracting two is exact. The finite near-bound cast is explicitly proved in cutGeometry_of_leaves.'
    elif stem in {'RemovedPairResponse','RemovalTelescope','RemovalCostSum'}:
        natcheck='depthShift is toNat(depth)−3. Its physical uses have finite depth≥3; prefix counts and Fin(last) tail sums include the last=0 case.'
    elif stem=='CutScales':
        natcheck='u−31 is cast to a real subtraction in the statement, avoiding natural underflow.'
    division='No division or normalization appears in the conclusion; no nonzero-denominator premise is needed here.'
    if module in {'NodesRemoval','NodesCut'}:
        division='Original partition sums are proved positive or supplied explicitly before probabilistic normalization/log rewriting. Positive conditioning fibres alone are interpreted probabilistically; zero fibres are omitted.'
    if module=='NodesTail' or stem in {'NearSeries','RawWeightSum','NeighbourDecay'}:
        division='0<θ<1 gives θ≠0 and 1−θ>0. Tail estimates also have u≥1 and c=−log θ>0 before inverse powers or division by c/s.'
    if stem=='CrossWeightSum':
        division='The generic finite-cover inequality has no division; its scalar c is only required nonnegative.'
    e['trap_check']={
      'missing_premises':specific,
      'vacuity_and_degenerate_cases':degenerate,
      'coercions_and_sums':'Reviewed: physical distances are ℕ or ℕ∞, coordinate/radius differences are ℤ, and spacing/real powers are ℝ. Finset site sums and Fintype configuration sums are distinct. Finsupp support sums are finite; the sole near infinite series has explicit Summable data.',
      'nat_subtraction':natcheck,
      'division_and_zero':division,
      'instances':'The declaration is checked as a closed Prop with autoImplicit=false and relaxedAutoImplicit=false. State-space Fintype/Nonempty arguments are retained; concrete plane configuration products have their actual finite alphabets.',
      'other_win_leaf_hypotheses':'None. Only permitted cross-lane Top definitions can occur as closed named inputs. Generic local mathematical premises are expanded explicitly in the leaf.'
    }

open_entries=[e for e in entries if e['status']=='open']
retained_entries=[e for e in entries if e['status']=='proved']
assert {e['lean_name'].split('.')[-1].removesuffix('Statement') for e in retained_entries}==retained_stems
(report/'retained-leaf-proofs.json').write_text(json.dumps([
    dict(lean_name='AKLT.Blueprint.Win.'+e['lean_name'].split('.')[-1][0].lower()+e['lean_name'].split('.')[-1][1:].removesuffix('Statement'),
         statement_name=e['lean_name'],module=e['module'],source_file=e['source_file'],
         provenance=e['proof_provenance']) for e in retained_entries
],indent=2,ensure_ascii=False)+'\n')
(report/'proof-policy.json').write_text(json.dumps(proof_policy,indent=2,ensure_ascii=False)+'\n')
(report/'leaves.json').write_text(json.dumps(open_entries,indent=2,ensure_ascii=False)+'\n')
(report/'nodes_inventory.json').write_text(json.dumps(entries,indent=2,ensure_ascii=False)+'\n')

# Check that the conjunction exposes exactly the remaining open obligations.
fields=re.findall(r'^  \w+ : (\w+Statement)$',(root/'Leaves.lean').read_text(),re.M)
assert collections.Counter(fields)==collections.Counter(e['lean_name'].split('.')[-1] for e in open_entries)
lean_files=list(root.glob('*.lean'))
for p in lean_files:
    source=p.read_text()
    forbidden=re.search(r'\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque)\b|#eval|run_cmd|skipKernelTC|maxHeartbeats\s+0',source)
    assert not forbidden,(p,forbidden.group(0))

build=json.loads((report/'build-results.json').read_text())
assert build['status']=='PASS'
log=(report/'build-logs/AKLT.Blueprint.Win.Audit.log').read_text()
axioms=[line for line in log.splitlines() if 'depends on axioms:' in line]
assert len(axioms)==14
for line in axioms:
    assert all(x.strip() in {'propext','Classical.choice','Quot.sound'} for x in line.split('[')[1].rstrip(']').split(',')),line

# A separate readable per-node trap log covers proved as well as open nodes.
trap=['# Per-node trap checks','', 'All 79 nodes were reviewed. The table records the specific premise and degenerate-case checks; the complete seven-field audit is in nodes_inventory.json, and every open entry also carries it in leaves.json.','', '| Node | Premise check | Empty / degenerate check |','|---|---|---|']
for e in entries:
    stem=e['lean_name'].split('.')[-1]
    trap.append('| `'+stem+'` | '+e['trap_check']['missing_premises'].replace('|','\\|')+' | '+e['trap_check']['vacuity_and_degenerate_cases'].replace('|','\\|')+' |')
(report/'trap-checks.md').write_text('\n'.join(trap)+'\n')

counts=collections.Counter(e['difficulty'] for e in open_entries)
r=['STATUS: COMPLETE','', '## Node table','', 'All names below are in `AKLT.Blueprint.Win`. There are 79 closed nodes: five proved and 74 open. This completes the blueprint and its conditional assemblies; it does not prove the open mathematical leaves.','', '| Leaf | Paper label / lines | Difficulty | State |','|---|---|---|---|']
for e in entries:
    module=e['module'].split('.')[-1]
    stem=e['lean_name'].split('.')[-1]
    line=next(i for i,s in enumerate((root/(module+'.lean')).read_text().splitlines(),1) if s.startswith('def '+stem+' : Prop'))
    r.append(f'| [{stem}]({root}/{module}.lean:{line}) | `{e["paper_label"]}`, {e["paper_lines"]} | {e["difficulty"]} | {e["status"]} |')
policy_section=['','## Leaf proof policy and retained proofs','',
'The author’s new rule reserves the first attempt at every new Lean leaf proof, including checker soundness, for a different, cheaper model. BP_WIN will continue only the blueprint/design work and proved assemblies. No new leaf proof was attempted after receipt of the rule. All 74 open entries in `leaves.json` now contain their exact closed Lean definition, source context, source location, statement hash and explicit routing to the orchestrator-selected different, cheaper model. No sub-agent was launched.','',
'The following five leaf proofs were written before the rule and are retained under its explicit exception:','']
for e in retained_entries:
    stem=e['lean_name'].split('.')[-1].removesuffix('Statement')
    theorem=stem[0].lower()+stem[1:]
    source=Path(e['source_file']).read_text()
    line=source[:source.index('theorem '+theorem+' :')].count('\n')+1
    policy_section.append('- [`AKLT.Blueprint.Win.'+theorem+'`]('+e['source_file']+':'+str(line)+') : `'+stem+'Statement`.')
policy_section+=['',
'Their machine-readable inventory is [`retained-leaf-proofs.json`]('+str(report/'retained-leaf-proofs.json')+'). The six pre-existing private assembly helpers (`joined_mono`, `joined_symm`, `connected_relation`, `connected_via`, `subset_thicken`, `decay_nonnegative`) are retained as assembly glue. This rule update changes only reporting and manifest data; all Lean sources still match the 33-module clean-build hashes in `checked-sources.json`.','']
r+=policy_section
r+=['','## Assemblies and inputs','',
'[`Assembly.lean`]('+str(root/'Assembly.lean')+') proves `shellGeometry_of_leaves : ShellLeaves → Top.ShellGeometryStatement` and `cutMOS_of_leaves : WindowLeaves → Top.MomentsStatement → Top.FiniteFactsStatement → Top.ThreeFactorMeanStatement → Top.ThreeFramesStatement → Top.ExactStatement → Top.CutMOSStatement`. All global hypotheses are closed Props. The seven intermediate assemblies prove the even-chain filling, boundary connectivity, connected thickening, taper connectivity, cut geometry, removal estimate, and common minorization.','',
'[`Leaves.lean`]('+str(root/'Leaves.lean')+') is an explicit conjunction of exactly the 74 open statements. Each node is independently closed; no node mentions another Win leaf as a named hypothesis. Generic algebra/path/counting nodes state their local mathematical premises in full, and the proved assembly passes those local facts. The permitted cross-lane Top inputs are explicit where needed. The only analytic response premise is `ResponseProperty A θ`, already present in the target.','',
'The pure shell export uses only `ShellLeaves`. The cut export uses the five closed A/C inputs above, with no recursion, numerical certificate, or gap conclusion. All additional definitions live in Win; the frozen statement layer is unchanged.','',
'## Size and proof routes','',
'The boundary proof is split into the even-chain filling route and the crossing-edge parity route, then further into diagonal elimination, finite box/flux/tail reconstruction, triangle parity, and two-crossing witnesses. The tapered-cut proof is split again into core/radial/escape paths, raw distance/range/depth arithmetic, signed-side exclusion, square intersections and layer counting, and weighted summation. The removal lower bound is split into fibre control, conditional-mean averaging, the quartic bound, and scalar polynomial/log bounds. Partition reindexing, quadrature, normalization, original-leg factorization, locality, and common minorization are separate nodes.','',
'Each open leaf has a suggested 20–380 proof-line budget; these are scheduling estimates, not measured completed proofs. The eight hard nodes are already isolated substeps of the second-stage decompositions. The manifest records definitions and compiler-checked library names, explicit cross-lane inputs, paper lines, donor pointers and the suggested route. Open-node counts: '+', '.join(f'{counts[k]} {k}' for k in ['easy','medium','hard'])+'.','',
'Potential donor use is restricted to proved finite conditioning/path/cochain infrastructure. The Balaban boundary theorem assumes nearest-neighbour connectivity and the nearest-neighbour vertex boundary; it cannot supply the present star-connected, full sup-distance-one boundary theorem directly. The manifest records that mismatch at every relevant pointer. Shell geometry, physical taper counts and the one-seed removal constants require new proofs.','',
'## Trap audit','',
'[`trap-checks.md`]('+str(report/'trap-checks.md')+') checks every node, including the five proved nodes. [`nodes_inventory.json`]('+str(report/'nodes_inventory.json')+') and [`leaves.json`]('+str(report/'leaves.json')+') record missing-premise, vacuity/degeneracy, coercion/sum, natural-subtraction, zero-denominator, instance and leaf-closure checks.','',
'The unconditional raw height is `h ≥ 30+t`; the far-depth scalar node requires that estimate. The weaker statement `h ≥ 31` alone would fail when s/12 is large. The near depth remains `max(t,16)−2`, the raw depth is at least 14, thick depth at least 13, the layer count at most 48, and thickening costs exactly `5/θ`. Signed side-depth exclusion includes the two exterior cases, preventing coincident sides without a diagonal-only block test.','',
'All removals keep original G, original legs and original S(G). `componentSum G H` means removal of G\\H from G, so holes acquire no pins. The removal order is nonempty, a singleton has an empty tail sum, and the seed retains the quartic cost. The assembled constants are exactly `1,4,2`, `l₀=64`, and `p₀=exp(-2*cutCost A θ)`.','',
'Empty volumes and window products have one empty configuration and positive partition sum. Empty components contribute one. Empty far volumes use distance top. Finite depth is justified before converting toNat or shifting by three. Generic minorization nodes explicitly require probabilities, a nonempty finite state space where strict positivity is used, and E≥0; `cutCostNonnegative` supplies E≥0 at the window theorem. Both upper and lower comparisons retain the actual window frame weights, with a reference law independent of the exterior boundary.','',
'## Verification','',
f'A fresh source rebuild compiled all {build["modules"]} local AKLT modules in the import closure of `Win.Audit`, using at most {build["max_lean_processes"]} Lean processes ({build["seconds"]} seconds). All local Top/Defs imports were rebuilt; the precompiled AKLT artifacts were not used. Mathlib used the existing Lake cache. Both `autoImplicit` and `relaxedAutoImplicit` were false. The toolchain is the project-pinned Lean 4.35.0-rc2.','',
'Run `python3 /home/ubuntu/aklt/reports/BP_WIN/build_blueprint.py` from the assigned worktree. Artifacts are written to `/tmp/bp_win_clean_build`; logs and structured results are in the report directory. [`Audit.lean`]('+str(root/'Audit.lean')+') checks every node as a zero-parameter Prop and prints every exported theorem\'s axioms. [`LibraryChecks.lean`]('+str(root/'LibraryChecks.lean')+') checks the dependency identifiers used in the manifest. The source scan finds no prohibited proof escape, placeholder, zero-heartbeat override or effectful Lean command.','',
'## #print axioms','', 'Verbatim output from the clean `Win.Audit` build (nine assemblies, then five proved leaves):','', '```text',*axioms,'```','',
'## Top/Defs problems found','',
'None found in the two target interfaces or the consumed geometry, pin, probability, specification and frame-model definitions. The target statements retain the paper’s nonexceptional parallel-clearance premise, real shell spacing, extended-natural empty-set distances, all translates/colourings, original pins, and exact cut constants. No frozen Top/Defs file was edited and no V2 replacement was needed. The stronger raw-height premise described above is a Win node-design trap, not a frozen-interface defect.','',
'## ORCH-SUMMARY','',
'- Lane: BP_WIN; blueprint status COMPLETE.','- Source directory: `AKLT/Blueprint/Win/` (11 Lean files).',
'- Targets assembled: `AKLT.Blueprint.Top.ShellGeometryStatement`, `AKLT.Blueprint.Top.CutMOSStatement`.',
'- Exported target assemblies: `AKLT.Blueprint.Win.shellGeometry_of_leaves`, `AKLT.Blueprint.Win.cutMOS_of_leaves`.',
'- Nodes: 79 closed; five proved; 74 open, listed individually in `leaves.json`.',
'- Author rule: every new leaf-proof first attempt goes to a different, cheaper model; BP_WIN writes no further leaf proofs.',
'- Retained pre-rule leaf proofs: `metricFacts`, `spanCutParity`, `logLipschitz`, `cutCostNonnegative`, `windowCostArithmetic`.',
'- Open manifest includes exact closed definitions, source contexts and routing; no new leaf proof or Lean-source change after the rule.',
'- Required cross-lane inputs: `MomentsStatement`, `FiniteFactsStatement`, `ThreeFactorMeanStatement`, `ThreeFramesStatement`, `ExactStatement`.',
'- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`; no added axioms.',
'- Build: all 33 local source modules passed, max four Lean processes; every delivered Lean file is in that checked closure.',
'- Frozen-interface changes/problems: none. No V2 requested.',
'- Integration: import `AKLT.Blueprint.Win.Assembly`; supply the open leaf conjunctions and the five allowed A/C exports. Remaining work is proof-writing for the 74 manifest entries.'
]
(report/'report.md').write_text('\n'.join(r)+'\n')
(report/'audit-results.json').write_text(json.dumps({'status':'PASS','closed_nodes':len(entries),'proved_nodes':5,'open_nodes':len(open_entries),'open_by_difficulty':dict(counts),'assembly_theorems':9,'exported_theorems':14,'all_leaf_names_closed':True,'no_other_win_leaf_hypotheses':True,'pack_matches_open_manifest':True,'prohibited_source_patterns':[],'allowed_axioms':['propext','Classical.choice','Quot.sound'],'frozen_files_changed':[],'trap_checks_all_nodes':True},indent=2)+'\n')
audit=json.loads((report/'audit-results.json').read_text())
audit.update(proof_policy_recorded=True,retained_pre_rule_leaf_proofs=proof_policy['existing_leaf_proofs_retained'],
             new_leaf_proofs_after_rule=0,exact_closed_statements_in_open_manifest=True,
             next_leaf_proof_attempts_reserved_for_different_cheaper_model=True)
(report/'audit-results.json').write_text(json.dumps(audit,indent=2)+'\n')
print(f'Report complete: {len(entries)} node checks, {len(open_entries)} open leaves, {len(axioms)} theorem audits.')
