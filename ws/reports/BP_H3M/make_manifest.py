from pathlib import Path
import json,re
root=Path('/home/ubuntu/aklt/wt/BP_H3M')
rep=Path('/home/ubuntu/aklt/reports/BP_H3M')
ns='AKLT.Blueprint.H3.'
items=[]
def add(name,mod,label,lines,difficulty,est,summary,deps,route,trap):
    text=(root/f'AKLT/Blueprint/H3/{mod}.lean').read_text()
    pat=r'^def '+name+r' : Prop :=\n(.*?)(?=\n\n(?:/--|end |namespace |theorem |def )|\Z)'
    match=re.search(pat,text,re.M|re.S)
    assert match,name
    base=dict(
        missing_premises='All mathematical premises are quantified inside the closed definition; no other Statement constant occurs in its type.',
        vacuity='No contradictory premise is introduced. The unconditioned conclusions and all supported boundary cases remain obligations.',
        empty_degenerate='Finite empty sums/products have their usual 0/1 values; no positive-length index is constructed without a bound.',
        coercions='Weights and finite products are rational. No truncating ofReal cast is used in the leaf conclusion.',
        finset_fintype='All finite index types have their fixed Defs instances; lists retain multiplicities unless Nodup is explicitly assumed.',
        nat_subtraction='No unguarded natural subtraction is introduced by the leaf.',
        division_zero='No new denominator is variable. Defs thresholds, 3, 5 and the exact dyadic denominator are nonzero.',
        instances='The declaration has no free variables or silently dropped instance binders. All types/instances are concrete or explicitly quantified.')
    base.update(trap)
    items.append(dict(lean_name=ns+name,module='AKLT.Blueprint.H3.'+mod,paper_label=label,
        status='open',first_attempt_policy='The first Lean proof attempt must be assigned to a different, cheaper model; the blueprint architect must not attempt this leaf.',
        proof_assignment='Unassigned; orchestrator to select the cheaper model.',
        paper_source='/home/ubuntu/aklt/reports/REV_C2/app-input-contracts.tex' if not lines.startswith('PLAN') else '/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md',
        paper_lines=lines,difficulty=difficulty,estimated_proof_lines=est,estimated_writer_hours='1–2',
        statement_summary=summary,statement='def '+ns+name+' : Prop :=\n'+match[1].strip(),
        dependencies=deps,suggested_proof_route=route,trap_check=base))
A='l:automaton-quotient'; P='l:phase-expansion'; D='l:stationary-domination'; L='l:stationary-local-global'; F='l:prefix-domination'; R='l:kernel-reflection'; H='h:H3'
add('RawSuccessorStatement','NodesAutomaton',A,'315–354','medium',180,
    'An admitted append-and-forget step preserves raw bond injectivity at positive memory.',
    ['AKLT.Defs.RawWindow','AKLT.Defs.WindowAdmissible','AKLT.Defs.windowSuccessor','AKLT.Defs.wordVertex','AKLT.Defs.wordBond','Finset.sum_bij'],
    'Translate the successor window by the first original step. Its first m−1 bonds are distinct old bonds with shifted indices; admissibility excludes its new last bond. Split m=1 explicitly. The generic Automaton API assumes this closure and cannot supply its lattice proof.',
    dict(empty_degenerate='m=0 is excluded by 1≤m. For m=1 the old suffix has no bonds and the successor is a one-bond raw word.',nat_subtraction='Shifted indices are created only after m≥1; do not simplify m−1 without this premise.'))
add('ProjectionRealizationStatement','NodesAutomaton',A,'315–339','easy',130,
    'Compatible surjective raw labels admit representatives and a Correct labelled quotient.',
    ['AKLT.Defs.CompatibleProjection','AKLT.Defs.MemoryQuotient.Correct','Classical.choose','AKLT.Gen.Bellman.Automaton.quotient','AKLT.Gen.Bellman.Automaton.quotient_compatible','AKLT.Gen.Bellman.Automaton.arrivalCoeff_compatible'],
    'Choose the supplied fibre witness for each class, set project=π and define allowed/kind/successor/arrival from representatives. Transport the fibre equalities; use the final-direction condition only on admitted non-revisit edges. Gen.Bellman.Quotient is the construction template; keep rational/signed coefficients out of ENNReal here.',
    dict(vacuity='When q=0 no map from the inhabited direction-word type to Fin 0 exists. For inhabited class sets, surjectivity gives genuine raw representatives.',finset_fintype='Directions are retained individually; do not divide a row by the size of a fibre.'))
add('PhaseFoldExpansionStatement','NodesPhase',P,'473–506','medium',250,
    'The generic four-phase terminal fold is the sum of its unique A→C and B→D changes.',
    ['AKLT.Blueprint.H3.phaseRun','AKLT.Blueprint.H3.phaseUpdate','AKLT.Blueprint.H3.singleChange','AKLT.Defs.phaseTransition','AKLT.Defs.phaseInitial','AKLT.Defs.phaseTerminal','List.foldl_cons','Finset.sum_comm'],
    'Induct on the finite index list/length with invariants for all four coordinates. A and B persist diagonally, while C and D collect exactly one change. Unfold the four-element Phase Fintype only, not direction-word enumerations. Prove the product/coordinate invariants as internal lemmas.',
    dict(empty_degenerate='At n=0 phaseInitial has zero terminal reward and the change-index sum is empty. Rewards may be zero or negative: this is an algebraic identity.',division_zero='There is no division by a reward or phase weight.'))
add('SingleChangeFactorStatement','NodesPhase',P,'480–505','medium',220,
    'Each true single-change product factors as the common base weight times its long-order reward term.',
    ['AKLT.Blueprint.H3.singleChange','AKLT.Blueprint.H3.trueKind','AKLT.Blueprint.H3.longRewardTerm','AKLT.Blueprint.H3.longMultiplier','AKLT.Defs.trailBaseWeight','Finset.prod_mul_distrib'],
    'Split the change index into revisit, straight, turn. Revisit changes are zero. On first visits factor 1/3 at every non-revisit index and 1/5 at revisits; the remaining passage factors are exactly longMultiplier. Use equality of finite products rather than cancellation by a possibly zero reward.',
    dict(vacuity='No IsTrail assumption is needed: the identity depends only on the three kinds and chronological index comparisons.',empty_degenerate='For n=0 there is no j; every product identity used at positive n still permits empty before/after factors.'))
add('ExposureListExpansionStatement','NodesPhase',P,'490–508','medium',130,
    'A nodup finite exposure list equals the sum of rewards times the product through each list position.',
    ['AKLT.Defs.exposureSum','AKLT.Blueprint.H3.orderedMultiplier','List.Nodup','List.idxOf','List.take','List.toFinset','Finset.sum_insert'],
    'Induct on the nodup list. The head contribution has the one head passage factor; every tail prefix-product gains the same factor. Rewrite idxOf for a member unequal to the head and distribute the finite sum.',
    dict(missing_premises='Nodup is explicit because the right side uses toFinset and would otherwise lose repeated responding indices.',empty_degenerate='The empty list gives zero on both sides. idxOf is interpreted only for indices in l.toFinset.'))
add('LongOrderingMultiplierStatement','NodesPhase',P,'490–508','medium',240,
    'The long ordering lists each first visit exactly once and has the prescribed prefix products.',
    ['AKLT.Defs.longOrdering','AKLT.Defs.firstVisitList','AKLT.Blueprint.H3.orderedMultiplier','AKLT.Blueprint.H3.longMultiplier','List.finRange','List.filter','List.Nodup','Finset.prod_filter'],
    'Use nodup and increasing order of finRange. The straight and turn filters are disjoint and exhaust the non-revisits. Characterize the list prefix before a straight member as earlier straight indices, and before a turn as all straight plus earlier turns; translate map-product to the Fin product.',
    dict(empty_degenerate='At n=0 the ordering is empty and both membership/product assertions are vacuous. At a selected member the response itself is included by idxOf+1.',finset_fintype='Nodup and disjointness justify toFinset. Chronological ties cannot occur because indices are distinct.'))
add('PrefixCoefficientCausalityStatement','NodesPhase',P,'509–515','medium',220,
    'Every transition matrix below L is unchanged on taking an actual prefix.',
    ['AKLT.Defs.takeWord','AKLT.Defs.wordVertex','AKLT.Defs.wordIncoming','AKLT.Defs.departureCount','AKLT.Defs.deadAt','AKLT.Defs.truePhaseCoefficient','AKLT.Defs.responsePairs'],
    'First prove equality of prefix vertices through L, then incoming directions and all earlier departure counts. Transport neighbours, outgoing vertices, dead sets, pair coefficients and witnessKappa. All information used at index i lies at indices ≤i+1≤L.',
    dict(missing_premises='L≤n is explicit. No statement about the artificial east padding when L>n is asserted.',empty_degenerate='L=0 has no i. L=n gives the full word. The departure at L−1 uses the actual vertex at L.',nat_subtraction='The incoming index i−1 is used only in the nonzero-index branch. min i L=min i n=i for i<L≤n.'))
add('PhaseSplitAlgebraStatement','NodesPhase',P,'509–515','medium',180,
    'Equality of the actual prefix matrices implies exact factorization at the phase at the split.',
    ['AKLT.Blueprint.H3.phaseRun','AKLT.Blueprint.H3.phaseUpdate','AKLT.Defs.prefixPhases','AKLT.Defs.truePhaseSuffix','List.foldl_append','List.take_append_drop','Finset.sum_comm'],
    'Prove linearity of a suffix fold in its initial phase row, split finRange by take/drop at L, and identify the prefix fold with the explicitly assumed coefficient equalities. Expand the initial row in the four delta-phase basis vectors.',
    dict(missing_premises='The premise is the pointwise equality of concrete coefficient matrices, not a leaf Statement. Assembly supplies it from prefix causality.',empty_degenerate='L=0 uses phaseInitial; L=n has an empty suffix and returns phaseTerminal.'))
add('SuffixWindowValidityStatement','NodesDomination',D,'574–582','medium',240,
    'A true trail supplies a raw remembered window and an admitted next direction after memory ten.',
    ['AKLT.Blueprint.H3.suffixWindow','AKLT.Defs.lastWindowWord','AKLT.Defs.takeWord','AKLT.Defs.IsTrail','AKLT.Defs.RawWindow','AKLT.Defs.WindowAdmissible','AKLT.Defs.wordBond'],
    'Identify window bonds with the distinct whole-trail bonds at indices i−10,…,i−1 after translating the origin. The next bond is distinct from all of them; immediate reversal would repeat the last one.',
    dict(missing_premises='The full true trail and 10≤i are explicit. The first-step virtual reversal condition alone is not substituted for the all-bond injectivity argument.',nat_subtraction='10≤i ensures the lastWindowWord default branch is never taken for any remembered letter.'))
add('SuffixWindowLabelsStatement','NodesDomination',D,'574–582, 612–619','medium',280,
    'Suffix windows update correctly, retain arrival, and detect only genuine revisits.',
    ['AKLT.Blueprint.H3.suffixWindow','AKLT.Defs.windowSuccessor','AKLT.Defs.windowArrival','AKLT.Defs.windowKind','AKLT.Defs.wordIncoming','AKLT.Defs.departureCount','AKLT.Blueprint.H3.trueKind'],
    'Compute the remembered letter at every Fin 10 index for times i and i+1. Translate remembered departure vertices to whole-trail vertices. A remembered earlier departure is a true one; a true first departure therefore gets its actual straight/turn kind.',
    dict(nat_subtraction='Use 10≤i and i<n before rewriting i−10 or i−1. The next window at i+1≤n includes the final bond when i=n−1.',missing_premises='The conclusion does not assert the false converse that every true revisit is detected by memory.'))
add('IncidentBondBudgetStatement','NodesDomination',D,'596–608','medium',260,
    'At every site the number of arrivals plus departures is at most its four lattice bonds.',
    ['AKLT.Blueprint.H3.arrivalCount','AKLT.Defs.departureCount','AKLT.Defs.IsTrail','AKLT.Defs.wordBond','AKLT.Defs.neighbours','AKLT.Defs.Compass.step','Finset.card_le_card_of_injOn'],
    'Create the disjoint arrival/departure index set for z. Map each occurrence to its used bond and then the other endpoint. Nonzero compass steps prevent a loop; full bond injectivity prevents duplicate incident occurrences. Inject the other endpoints into the four neighbours.',
    dict(empty_degenerate='At n=0 both counts vanish. z may be the start, target, endpoint, an interior site or a site never visited.',finset_fintype='arrivalCount ranges over all n bonds; departureCount at n uses min n n=n. Each incident bond is counted once at this fixed site.'))
add('DepartureBalanceStatement','NodesDomination',D,'596–608','easy',100,
    'A finite vertex sequence has at most one more departure than arrival at any site.',
    ['AKLT.Blueprint.H3.arrivalCount','AKLT.Defs.departureCount','AKLT.Defs.wordVertex','Finset.range','Finset.card_filter','Finset.sum_range_succ'],
    'Shift the index of every departure at times ≥1 to its preceding arrival. The remaining time-zero departure contributes at most one. Equivalently telescope indicator counts over the vertex list. No trail premise is needed.',
    dict(vacuity='This is asserted for every direction word, even one that repeats bonds.',empty_degenerate='The empty word has both counts zero; the endpoint contributes an arrival but no departure.'))
add('KnownSiteMemoryStatement','NodesDomination',D,'584–610','medium',300,
    'Known-site suffix departures are true revisits, cannot be memory revisits, and never reuse the initial bond.',
    ['AKLT.Defs.ClosedTrail','AKLT.Defs.SurvivingPrefix','AKLT.Defs.FirstDirection','AKLT.Defs.departureCount','AKLT.Blueprint.H3.suffixWindow','AKLT.Defs.windowKind','AKLT.Defs.IsTrail'],
    'Recover the first bond and the two initial departures from the surviving prefix. The current known-site departure is a true revisit. Any remembered additional departure has index ≥i−10≥L−10≥2, distinct from 0 and 1 and the current index; it would contradict the explicit per-site ≤2 budget. Bond injectivity separately excludes reuse of the initial bond.',
    dict(missing_premises='12≤L, L≤n, non-east first direction, survival, full closed-trail conditions and the per-word departure budget are all explicit.',empty_degenerate='If L=n there is no suffix i. L≥12 guarantees both initial departures exist.',nat_subtraction='i−10≥2 follows from i≥L≥12 before any comparison to remembered indices.'))
add('TrueRewardIdentityStatement','NodesDomination',D,'621–639','medium',160,
    'The true live-pair reward equals relaxedReward with its finite true-dead set, and a true step never reverses.',
    ['AKLT.Blueprint.H3.trueDeadSet','AKLT.Defs.responseNeighbours','AKLT.Defs.liveOtherNeighbours','AKLT.Defs.witnessKappa','AKLT.Defs.relaxedReward','AKLT.Defs.wordVertex','AKLT.Defs.IsTrail'],
    'Prove the successor-vertex formula, then identify both live-other-neighbour sets elementwise. The inserted centre is always truly dead and is harmless when remote. Match powersetCard and coefficient branches. Derive nonreversal at a noninitial index from distinct adjacent bonds.',
    dict(empty_degenerate='No departure index exists at n=0. The finite dead set need not include every dead lattice site, only neighbours plus the centre.',finset_fintype='Response pairs remain two-element Finsets; the outgoing site is inserted in both rules even if the dead set mentions it.'))
add('RewardForgettingStatement','NodesDomination',D,'621–639','medium',200,
    'Shrinking the dead set increases the exact type-dependent reward at a nonreversing passage.',
    ['AKLT.Defs.relaxedReward','AKLT.Defs.alphaBound','AKLT.Defs.betaBound','AKLT.Defs.betaPrimeBound','AKLT.Defs.kernelWitness','AKLT.Blueprint.H3.kernelWitness_pos','Finset.powersetCard'],
    'The live set for more dead sites is a subset of the other live set. Inject each existing pair by identity. A surviving outgoing pair has coefficient beta-prime when one other neighbour lives and beta when two live; check the two rational inequalities beta-prime≤beta. Added pairs have nonnegative coefficients.',
    dict(missing_premises='The dead-set inclusion is dead₁⊆dead₂ but the reward inequality is reversed. Nonreversal bounds the number of non-outgoing live neighbours by two.',empty_degenerate='Zero, one and two live non-outgoing neighbours are separate cases. With zero, the pair set is empty.'))
add('LocalCoefficientComparisonStatement','NodesDomination',D,'612–639','medium',200,
    'Explicit per-step true geometry and reward facts imply every true/stationary scalar phase coefficient inequality.',
    ['AKLT.Blueprint.H3.TrueStepFacts','AKLT.Defs.MemoryQuotient.Correct','AKLT.Defs.truePhaseCoefficient','AKLT.Defs.stationaryCoefficient','AKLT.Defs.phaseTransition','AKLT.Blueprint.H3.stationaryCoefficient_nonneg'],
    'Use Correct to transfer admitted labels, successors and non-revisit arrivals. Split known-site rows, then true/window revisits. Known sites agree at 1/5; remembered revisits agree; forgotten revisits are bounded by relaxed diagonals ≥1/3. At true first visits compare the nonnegative multiple of the assumed reward bound. Off-diagonal true zeros use stationaryCoefficient_nonneg.',
    dict(missing_premises='TrueStepFacts explicitly contains rawness, admission, arrival, one-way revisit detection, first-visit kind, reward bound, both terminal exclusions, next-centre exclusion and known-site safety.',vacuity='TrueStepFacts is constructed in the checked assembly from independent geometry/counting leaves; it is not defined as the desired coefficient inequality.'))
add('ClosedTrailStepGeometryStatement','NodesDomination',D,'578–582','easy',120,
    'Each closed-trail departure avoids both terminals, advances by its compass step, and does not enter the centre.',
    ['AKLT.Defs.wordVertex','AKLT.Defs.ClosedTrail','Finset.sum_congr','Finset.sum_ite_eq'],
    'Subtract the two finite vertex sums: only index i changes. Apply the quantified centre-avoidance and preterminal target-avoidance parts of ClosedTrail at i and i+1.',
    dict(empty_degenerate='For i=n−1 the next index equals n; centre avoidance explicitly includes this endpoint, while target avoidance is asserted only at i<n.'))
add('SuffixWordComparisonStatement','NodesDomination',D,'641–647','medium',320,
    'Pointwise coefficient domination plus actual successor transport dominates one completed suffix direction word.',
    ['AKLT.Defs.appendWords','AKLT.Defs.truePhaseSuffix','AKLT.Blueprint.H3.stationaryWordValue','AKLT.Blueprint.H3.suffixWindow','AKLT.Blueprint.H3.takeWord_append','AKLT.Blueprint.H3.truePhaseCoefficient_nonneg','AKLT.Blueprint.H3.stationaryCoefficient_nonneg','AKLT.Gen.Bellman.System.pathWeight'],
    'First prove finite forward/backward phase-fold duality by induction (four-dimensional sum commutation). Compute the suffix letters of appendWords, initial prefix window and endpoint. Induct through the suffix with the two explicitly assumed per-step comparisons; the terminal ClosedTrail endpoint turns stationaryReward into phaseTerminal. This is the concrete rational version of generic labelled pathWeight comparison.',
    dict(missing_premises='Both coefficient inequalities and successor-class equalities for all suffix indices are explicit. ClosedTrail supplies the target endpoint; no IsTrail or state-consistency hypothesis is omitted.',empty_degenerate='At r=0 the comparison is just equality of the two terminal rewards whenever the displayed closed-trail premise holds.'))
add('StationaryWordExpansionStatement','NodesDomination',D,'641–647; 677–684','medium',180,
    'A stationary iterate enumerates all absolute direction words with the terminal reward.',
    ['AKLT.Blueprint.H3.stationaryWordValue','AKLT.Defs.stationaryApply','AKLT.Defs.stationaryReward','List.ofFn','Fintype.sum_prod_type','AKLT.Gen.Bellman.System.exact_eq_tsum_paths'],
    'Induct on r and use DirectionWord(r+1) ≃ Compass × DirectionWord r. Decompose List.ofFn at the head and commute the phase/word sums. The generic exact_eq_tsum_paths theorem is the semantic model; coefficients are the exact rational sums here.',
    dict(empty_degenerate='At r=0 there is one empty direction word and the value is stationaryReward.',finset_fintype='All four directions and four next phases are independent labels. Parallel quotient destinations retain each distinct edge.'))
add('StationaryFreeEdgeStatement','NodesCertificate',L,'800–813','medium',260,
    'Every stationary labelled coefficient is at most its position-free counterpart.',
    ['AKLT.Defs.stationaryCoefficient','AKLT.Defs.freeCoefficient','AKLT.Defs.relaxedReward','AKLT.Defs.MemoryQuotient.Correct','AKLT.Defs.betaPrimeBound','AKLT.Defs.betaBound','AKLT.Gen.Bellman.patch_step_le_free'],
    'Prove translation invariance of the local reward and compare deletion of the centre by a direct live-pair subset argument. Check zero rows/forbidden edges, known-site 1/5 diagonals and ordinary rows. Correct supplies non-reversal and arrival consistency on non-revisit edges. patch_step_le_free explains the subsequent global sum comparison, already implemented in Assembly.',
    dict(missing_premises='Correct is explicit; no relation between the arrays of two cases is assumed. The bound holds at all positions, stronger than merely outside B70.',empty_degenerate='Terminal, killed, and centre-entering edges are zero and covered. Arbitrary arrivals on revisit-only classes are irrelevant because phaseTransition on revisit ignores reward.'))
add('LongTrailPrefixStatement','NodesPrefix',F,'996–1003','medium',170,
    'A closed first-direction trail longer than twelve has a true surviving twelve-step prefix.',
    ['AKLT.Defs.takeWord','AKLT.Defs.ClosedTrail','AKLT.Defs.SurvivingPrefix','AKLT.Defs.FirstDirection','AKLT.Defs.IsTrail'],
    'Identify prefix vertices and bonds and restrict whole-trail injectivity. Transfer the first direction. Every prefix time j≤12 satisfies j<n, so the full first-hit condition excludes the target there; transfer centre avoidance as well.',
    dict(missing_premises='12<n is strict. Replacing it by 12≤n would wrongly classify a hit at time twelve as surviving.',empty_degenerate='The short sum alone owns a hit at exactly time twelve.'))
add('LongRowRegroupingStatement','NodesPrefix',F,'996–1006','medium',340,
    'At a long cutoff the complete row equals the exact short row plus true continuation sums over surviving prefixes.',
    ['AKLT.Defs.firstDirectionPartialRow','AKLT.Defs.trueContinuationSum','AKLT.Defs.prefixPhases','AKLT.Defs.appendWords','AKLT.Blueprint.H3.takeWord_append','AKLT.Blueprint.H3.wordSplit_proved','Finset.sum_bij','Finset.sum_comm','Finset.sum_sigma'],
    'Use the supplied concrete word equivalences, survival implication and contribution factorization. Partition Icc 1 R at 12, reindex n=12+r, and apply the word equivalence to each long length. Reorder the finite phase/prefix/suffix sums. Surviving prefixes contribute zero at r=0 because their endpoint is not the target.',
    dict(missing_premises='The three premises are explicitly quantified mathematical facts: word equivalences, prefix survival and per-trail phase factorization. No other leaf Statement appears.',nat_subtraction='R−12 is used only under 12<R. Long n are exactly 12+r with 1≤r≤R−12.',finset_fintype='Surviving prefixes remain individually indexed by DirectionWord 12, so quotient classes never erase multiplicity.'))
add('ReflectionGeometryStatement','NodesReflection',R,'1035–1044','medium',280,
    'Horizontal reflection preserves word geometry, row-B first hits, first directions, straightness and revisits.',
    ['AKLT.Blueprint.H3.reflectSite','AKLT.Blueprint.H3.reflectWord','AKLT.Defs.wordVertex','AKLT.Defs.wordBond','AKLT.Defs.departureCount','AKLT.Defs.ClosedTrail','AKLT.Defs.wordIncoming'],
    'Show reflectSite is additive and sends d.step to reflectDirection d.step. Commute it with the finite vertex sum, transport bonds by its injective Finset image, and identify departure-index filters. Fixed u,c,v_B and incoming west then transfer all ClosedTrail and first-direction conditions.',
    dict(empty_degenerate='n=0 has no first direction on either side. Vertex equality holds also for clamped indices j>n.',nat_subtraction='For incoming i−1, first separate i=0. No geometric truncation or torus quotient is involved.'))
add('ReflectionLivePairsStatement','NodesReflection',R,'1045–1052','medium',220,
    'Reflection bijects every finite live response-pair set.',
    ['AKLT.Blueprint.H3.reflectSite','AKLT.Blueprint.H3.reflectWord','AKLT.Defs.responseNeighbours','AKLT.Defs.liveOtherNeighbours','AKLT.Defs.deadAt','AKLT.Defs.responsePairs','Finset.image_image','Finset.powersetCard'],
    'Transport neighbours and erased incoming/outgoing sites through reflection. Compare deadAt by centre fixation and equality of departure-index filters. For powersetCard use the involution to preserve both containment and cardinality two.',
    dict(empty_degenerate='The live set may have zero, one or two non-outgoing sites. PowersetCard automatically handles all these cases.',finset_fintype='The inner image is of plane sites; the outer image is of two-element Finsets. Both maps are injective under the involution.'))
add('ReflectionPairLabelsStatement','NodesReflection',R,'1050–1059','medium',200,
    'Each corresponding live pair has the same coefficient, type and row-B shift.',
    ['AKLT.Blueprint.H3.reflectSite','AKLT.Blueprint.H3.reflectWord','AKLT.Defs.pairCoefficient','AKLT.Defs.responsePairType','AKLT.Defs.pairShift','AKLT.Defs.latticeDist','Finset.sup_image'],
    'Match outgoing membership, cardinality of the live-other set and straightness to select the same coefficient. Reflection preserves coordinate equality and hence type. Compute the integer natAbs distances to the fixed B endpoints, then transport min and finite sup.',
    dict(missing_premises='Only pairShift .B is asserted: the C target is not fixed by this reflection. The coefficient comparison is restricted to actual live pairs.',empty_degenerate='Actual pairs have cardinality two; the finite-sup reasoning also tolerates empty sets without inferring extra C symmetry.'))
add('FirstDirectionPartitionStatement','NodesKernel','l:stationary-assembly','1188–1196','easy',150,
    'Every finite row splits into its north, west and south first-direction rows.',
    ['AKLT.Defs.kernelPartialRow','AKLT.Defs.firstDirectionPartialRow','AKLT.Defs.ClosedTrail','AKLT.Defs.FirstDirection','AKLT.Defs.kernelCentre','AKLT.Defs.kernelStart','Finset.sum_add_distrib'],
    'Work termwise at n∈Icc 1 R. The first index exists; its four compass cases are disjoint. The east case has vertex one equal to kernelCentre and contradicts ClosedTrail. Reassemble the three finite sums.',
    dict(empty_degenerate='When R=0, Icc 1 0 is empty. A first index is constructed only under 1≤n.',finset_fintype='There is no B symmetry premise here and none for C. The partition counts each closed word exactly once.'))
add('LengthShiftSupportStatement','NodesKernel',H,'PLAN:2146–2164','easy',110,
    'Each fixed length has zero coefficient outside its explicitly enumerated finite shift set.',
    ['AKLT.Blueprint.H3.lengthShifts','AKLT.Defs.responseKappa','AKLT.Defs.kernelLengthCoefficient','AKLT.Defs.exposureSum','Finset.mem_biUnion','Finset.mem_image'],
    'For every word/index/pair, membership in lengthShifts is immediate from the two biUnions. Thus an outside shift makes every indicator in responseKappa false. Induct on exposureSum to propagate the zero reward and sum over words.',
    dict(empty_degenerate='At n=0 the index biUnion is empty and every exposure is zero.',finset_fintype='No geometric n/2 bound is needed: lengthShifts is the actual finite set of shifts over all words, including non-trails.'))
add('LengthRewardPartitionStatement','NodesKernel',H,'PLAN:2146–2164','medium',240,
    'The finite h-weighted length row is the sum of its exact type-and-shift coefficients.',
    ['AKLT.Blueprint.H3.kernelLengthRow','AKLT.Blueprint.H3.lengthShifts','AKLT.Defs.witnessKappa','AKLT.Defs.responseKappa','AKLT.Defs.kernelLengthCoefficient','AKLT.Defs.exposureSum','Finset.sum_comm','Finset.sum_ite_eq'],
    'Partition each live pair by its unique actual responsePairType and pairShift in lengthShifts. Prove exposureSum is linear in its reward for a fixed list, then commute the finite type, shift and word sums. Keep kernelOrdering w fixed throughout the reward decomposition.',
    dict(missing_premises='No convergence premise is needed. The common kernel ordering is the one fixed using witnessKappa, not an order reoptimized for each Y,s.',coercions='This entire partition is over ℚ; converting it to ENNReal is a separate node that uses established nonnegativity.'))
add('KernelSeriesRegroupingStatement','NodesKernel',H,'PLAN:2146–2164','medium',180,
    'At theta one the full shifted kernel row is the nonnegative sum over finite length rows.',
    ['AKLT.Defs.shiftKernel','AKLT.Defs.shiftedKernel','AKLT.Blueprint.H3.kernelLengthRow','AKLT.Blueprint.H3.kernelLengthCoefficient_nonneg','AKLT.Blueprint.H3.kernelLengthRow_nonneg','AKLT.Blueprint.H3.kernelWitness_pos','ENNReal.tsum_comm','ENNReal.tsum_mul_right','ENNReal.ofReal_sum_of_nonneg','tsum_eq_sum'],
    'Use theta=1 to remove shift factors, commute ENNReal tsums over length and shift and the finite type sum, and use the explicit zero-support premise to replace each shift tsum by its finite sum. Convert each nonnegative rational partition to ofReal and apply the explicit finite-length equality premise.',
    dict(missing_premises='Both support and finite weighted-partition equalities are supplied explicitly for this X. Positivity of the fixed definitions is already proved in Positivity.lean.',coercions='ofReal preserves finite sums only after nonnegativity. All cast steps keep ℚ→ℝ→ENNReal in that order.',finset_fintype='ENNReal sums may be infinite, so no real-tsum or unproved Summable assumption is used. Nonnegative tsum commutation is unconditional.'))
add('CutoffSeriesLiftStatement','NodesKernel',H,'PLAN:2146–2164','easy',90,
    'Uniform rational Icc cutoff bounds control the ENNReal sum of all nonnegative lengths.',
    ['ENNReal.tsum_eq_iSup_nat','ENNReal.ofReal_sum_of_nonneg','ENNReal.ofReal_le_ofReal','Finset.sum_le_sum_of_subset_of_nonneg','Finset.range','Finset.Icc'],
    'Write the tsum as iSup of range partial sums. Drop f 0 using its explicit zero premise; bound the remaining range by Icc 1 R, allowing an extra nonnegative endpoint. Apply the cutoff premise and monotonicity of ofReal, then iSup_le.',
    dict(missing_premises='f≥0 and f 0=0 are both explicit; without the latter Icc 1 R would miss the zero-length mass.',vacuity='At cutoff R=0 the premise implies 0≤B; negative upper bounds do not slip through ofReal truncation.',division_zero='There is no division or spectral-radius denominator.'))
assert len(items)==30,len(items)
for i in items:
    assert not any(d.endswith('Statement') for d in i['dependencies']),i['lean_name']
(rep/'leaves.json').write_text(json.dumps(items,indent=2,ensure_ascii=False)+'\n')
# Full kernel-checked declaration inventory. No proof term dumps are needed for theorem signatures.
files=sorted((root/'AKLT/Blueprint/H3').glob('*.lean'))
checks=['import AKLT.Blueprint.H3.Assembly','','namespace AKLT.Blueprint.H3','']
for p in files:
    if p.name=='Audit.lean': continue
    src=p.read_text()
    for name in re.findall(r'^def (\w+)',src,re.M):
        if re.search(r'^def '+name+r' : Prop :=',src,re.M):
            checks += [f'#check ({ns+name} : Prop)',f'#print {ns+name}']
        else:
            checks += [f'#check {ns+name}']
    for name in re.findall(r'^(?:@\[[^\n]*\]\s+)?theorem (\w+)',src,re.M):
        checks += [f'#check {ns+name}',f'#print axioms {ns+name}']
checks += ['','end AKLT.Blueprint.H3','']
audit_path=root/'AKLT/Blueprint/H3/Audit.lean'
audit_source='\n'.join(checks)
if not audit_path.exists() or audit_path.read_text()!=audit_source:
    audit_path.write_text(audit_source)
print(f'Wrote {len(items)} open leaves and Audit.lean')
