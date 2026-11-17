STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Reason |
|---|---|---|---|
| `AKLT.Blueprint.Rec.NormalizeStartStatement` | TRUE | easy | Removed centre makes the erased flag irrelevant to every factor. |
| `AKLT.Blueprint.Rec.KeptInvariantStatement` | TRUE | hard | The live-site exception and active mutuality persist at every prefix. |
| `AKLT.Blueprint.Rec.RemovedClosureStatement` | TRUE | medium | Deleting an unprotected live endpoint restores ordinary consistency. |
| `AKLT.Blueprint.Rec.CoveredClosureStatement` | TRUE | hard | All non-tip covered rules hold; V2 correctly handles boundary corners. |
| `AKLT.Blueprint.Rec.PairClosureStatement` | TRUE | medium | Deletion gives the right removed centre, geometry and D endpoint degrees. |
| `AKLT.Blueprint.Rec.TerminalDefectStatement` | TRUE | medium | Protected status stays U; other protected kept sets remain full. |
| `AKLT.Blueprint.Rec.SecondStartStatement` | TRUE | medium | Target avoidance preserves v; the first arrival supplies the target degree bound. |
| `AKLT.Blueprint.Rec.TerminalExceptionLocationStatement` | TRUE | hard | Away from the radius-two defect, the second departure template is covered. |

All eight leaves are true and self-sufficient. No missing mathematical premise or counterexample was found. The exact terminal kept-set formula is an optional fidelity strengthening, not a correction needed for truth. These are truth assessments and proof routes; no Lean proofs were written.

Reviewed repository `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The relevant source hashes were unchanged during the audit. The paper arguments are [l:closure](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:61) and [l:terminalcover](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:169), together with the definitions [d:domain and d:trace](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:8) and [d:pattern](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:488).

**Definitions traced.** The leaves and their elaborated types were read in [NodesClosure.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:11). The dependency chain was followed through:

- [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:15): CoveredDepartureV2, normalizeStart, prefixNetwork, PairData, PairSetup and PairData.normalized.
- [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10): Network, active, Present, bonds, presentNeighbours, LocalRules, Ordinary, Auxiliary, Consistent, spins, partition, AdmissibleStart, traceStep, traceNetwork, HasPairType and ResponsePair.
- [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:24): DirectionWord, wordVertex, wordBond, wordIncoming, wordVertices, StoppedNetworkTrail and AdmissibleTarget.
- [Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:8): templateSites, templateTips, templateCorners, PatternData, statusAt, keptAt and every clause of Covered; [Response.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:25): removeSite and normalizeRotation; [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:47): responsePairType.
- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): Plane, Compass and steps, latticeDist, Adjacent, neighbours, internalBonds, originalLegs, setDistance, boundaryDepth, protectedSites and square. [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9) and [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9): PinAssignment, Vec3, dot, normSq, UnitVector, finite spin labels, explicit spin vectors and status-dependent weights.

The key invariant is stronger than the bare KeptInvariantStatement conclusion: a live U site keeps its three nonincoming flags; a later live D site keeps one flag, while an initial D start retains two flags and at most one present bond. A U departure leaves two flags; a D departure destroys no unused bond. This derives evolving admissibility from initial-network trail membership. Later routes below may reuse this derivable induction, but do not assume that an imported definition of a Statement is already a proved theorem.

**1. [NormalizeStartStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:11) — TRUE, easy.** PairData.pair unfolds to ResponsePair, which supplies status c = X. normalizeStart changes only the kept flag at u pointing to c, and only if u is U. Since c is inactive, neither orientation of any present bond changes. Active sites, spin weights, extended spins and original-leg factors are unchanged, so the partition functional agrees for every observable and both Bool pin choices. This does not require u outside the protected layer.

Proof route: Use the removed-centre premise to show Present is unchanged at every ordered adjacent pair, hence bonds agree.  
Unfold partition: active index types and all factors coincide, including the unchanged original legs.

Lean traps: The quantifier is over PairData, so no interior premise is available or needed. Equal bonds alone would not imply equal partition functionals for arbitrary networks: here normalizeStart also leaves status, active sites, spin coordinates and original legs unchanged. No positivity or nonzero denominator is needed.

**2. [KeptInvariantStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:19) — TRUE, hard.** PairSetup supplies an ordinary consistent ResponsePair, an interior first endpoint, and its incoming direction. After normalization only the live site can violate full-U/two-kept-D conditions. A U departure leaves exactly two kept flags and a D departure removes the site; the arrival erasure changes only the new live site. Erasures are mutual at the traversed bond, protected sites are never departed, and departed statuses never return to U. Initial-bond trail membership suffices: admissible D removal destroys no unused present bond, so every unused trail edge remains available.

Proof route: Induct on prefixes with the stronger live-U-keeps-three/live-D-keeps-one invariant, separating the initial D start (two kept, at most one present).  
Preserve unused initial bonds, mutual active flags and local degree bounds at each step; status changes are only U to D or D to X.

Lean traps: StoppedNetworkTrail checks Present in the initial network, not in each prefix. Availability must be derived using distinct unoriented bonds and the admissible D-removal argument. Its stopping clauses separately prohibit every protected departure, even when T is arbitrary. The base D start keeps two flags despite having at most one present bond.

**3. [RemovedClosureStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:32) — TRUE, medium.** No protected site occurs before the live endpoint; the explicit endpoint-outside-protected premise excludes a protected final arrival too. The prefix invariant leaves every other U site full and every other D site with two kept flags. Removing the live site eliminates the only possible ordinary kept-set defect. Kept subsets and degree bounds persist, and mutuality is only required between remaining active sites.

Proof route: Obtain the strengthened prefix invariant, and show all protected kept sets are unchanged since every prefix vertex avoids the protected layer.  
Set the live status to X; restrict active-site mutuality and use monotonicity of present degrees to verify Consistent.

Lean traps: removeSite changes status only; surviving flags pointing to an X site are allowed. Consistent compares flags only between active endpoints. The premise excluding the live site from protectedSites is essential; protected terminal deletion would violate Ordinary.

**4. [CoveredClosureStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:41) — TRUE, hard.** At a U departure the live site has the three nonincoming kept flags. The incoming neighbour is X or a just-departed D with two kept flags excluding the live site. Every other active D neighbour keeps the live bond and exactly one additional flag, by active mutuality; D corners have two flags, and other U non-tip sites are full. Departure sites lie outside the protected layer, so their radius-two diamond lies inside G. V2 intersects the transported template flags with G, correctly permitting full U boundary corners whose outside directions are original legs. Tips are unconstrained matching data and may be chosen U.

Proof route: Strengthen the prefix induction to identify the live kept set and the just-departed incoming site, and rotate incoming to north.  
Build PatternData from the nine non-tip sites, fill U flags in all four directions, choose U tips, and verify Covered plus the inside-G matching.

Lean traps: Use CoveredDepartureV2, not the older exact-set CoveredDeparture. The intersection is applied after transporting flags into ambient coordinates. Pattern tips are freely chosen U and excluded from matching. Canonical incoming is north, so the missing arrival direction is south; the actual incoming direction is the previous outgoing direction.

**5. [PairClosureStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:50) — TRUE, medium.** Present neighbours a and b are distinct active lattice neighbours of the live U site y, and neither is the erased incoming neighbour. Removing the interior live site restores an ordinary consistent network. A D endpoint is nonlive and has exactly two kept flags including its present bond to y; deletion leaves at most one present bond. The two neighbours have distance two, and responsePairType {a,b} selects exactly their collinear B or diagonal C geometry. The centre y lies in G and becomes X.

Proof route: Derive removed-live closure from the prefix induction; present membership supplies active endpoints, adjacency and kept incidence.  
Count the remaining possible bonds at D endpoints and classify the six pairs of distinct cardinal neighbours to verify ResponsePair.

Lean traps: ResponsePair includes Consistent, not merely Auxiliary. Both endpoint degree bounds must be checked after deleting y. The a != b premise makes {a,b} a two-element set and prevents the wrong pair geometry. presentNeighbours uses actual mutual bonds, not one-sided kept flags.

**6. [TerminalDefectStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:60) — TRUE, medium.** Stopping at the original protected layer gives a positive-length trail because the PairSetup start is interior. No protected site is a departure, so every protected status remains U. Only the final arrival can erase a protected kept flag; all other protected kept sets remain original. Auxiliary local rules persist by the admissible-prefix induction. The statement is weaker than the prose claim of exactly one lost arrival flag: it does not explicitly identify the terminal kept set or restate all nonprotected ordinary kept rules, but everything it asserts is true.

Proof route: Run the admissible-prefix induction to obtain Auxiliary for the full trace, using wordVertices length n+1.  
Use avoidance of protected sites at all departure indices to keep their statuses fixed and their kept sets unchanged except at the final endpoint.

Lean traps: For stopping set S, n = 0 is impossible because PairSetup.interior excludes u from S. The endpoint at index n is an arrival, never a departure. The current conclusion does not assert the exact terminal kept set, and should not be cited alone as supplying that stronger formula.

Optional strengthening: No correction required. Optional fidelity strengthening: identify the terminal kept set as (neighbours e ∩ p.G).erase (wordVertex p.u w (n - 1)), together with the derived n > 0.

**7. [SecondStartStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:72) — TRUE, medium.** PairSetup already places u outside S and the explicit premise places v outside S. Since the first trail stops in S and avoids insert v S before stopping, it never visits v; its status and kept flags remain original until second normalization, and its present degree only decreases. The removed centre c stays X. Thus a U v has at most three present bonds and a D v retains the ResponsePair bound of at most one. The first terminal e remains protected U, and the first arrival deletes a genuinely present internal factor, reducing its original at-most-four total bond-plus-leg factors to at most three. Original legs are counted without change.

Proof route: Derive first-trace admissibility and avoidance of v, preserve c as X, then erase only the harmless v-to-c flag and check the U/D start cases.  
At e use protected U status, positive first length, monotone present bonds and the deleted arrival factor to establish AdmissibleTarget including original legs.

Lean traps: PairSetup supplies u outside S, but not v outside S; the explicit v premise is necessary. Avoiding v follows from first-hit stopping in insert v S plus the protected terminal and v outside S. AdmissibleTarget counts original legs in the U case, so a bound on presentNeighbours alone would be insufficient.

**8. [TerminalExceptionLocationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesClosure.lean:83) — TRUE, hard.** After the first trail and second normalization, all ordinary kept rules hold away from the fixed protected endpoint e and the second live site. Repeat the admissible-prefix induction during the second trail; no departure is in S, so no departure equals e. At distance greater than two from e, every non-tip template datum satisfies the same covered rules as in first-trail closure, with V2 handling boundary slots and freely chosen covering U tips. Hence an uncovered U departure must have positive taxicab distance at most two from e, at any second-trail index. The explicit incoming equality supplies the correct second virtual arrival direction.

Proof route: Carry one fixed protected U defect e through a strengthened second-prefix induction, deriving the same live and incoming-site descriptions away from e.  
For distance > 2 construct the covered V2 template as in first closure; take the contrapositive and use departure avoidance of S for positive distance.

Lean traps: The second incoming direction is independently quantified and constrained by v = c + incoming.step; it need not equal p.incoming. The argument applies at every Fin m index, not just an initial segment. Exclude distance zero using protected-departure avoidance, not a geometric estimate alone.

**Shared Lean checks.** The printed declarations are closed Props: no variable or instance premise was silently dropped. PairData.pair contains the full ordinary-consistency, removed-centre, geometry and endpoint hypotheses; PairSetup adds the incoming equality and first interior endpoint. The finite volume is a Finset Plane, with spin configurations indexed by its finite active subtype; no Fintype Plane is assumed. Classical reasoning is appropriate for protectedSites, finite predicates and responsePairType and does not add a mathematical hypothesis.

Plane coordinates and translations use integers, so negative coordinates do not truncate. wordIncoming uses natural subtraction only in its nonzero-index branch; j <= n and Fin n bounds keep prefixes and predecessor indices valid. At n = 0, departure clauses have no indices, as intended; the invariant and deletion statements still have a real zero-prefix case. Protected-terminal hypotheses force positive first-trail length. None of the eight conclusions has a rational/real coercion or zero-division issue: the only analytic equality here is an unnormalized real partition functional.

**Nonvacuity and finite checks.** Take G = [-4,4]^2, c = (0,0), u = (-1,0), v = (1,0), with c removed and all other sites U with full inside-G flags; use any independent unit pins, for example (1,0,0) on every original leg. Here S consists of sites with maximum absolute coordinate at least three. The first trail [(-1,0),(-1,1),(0,1),(0,2),(0,3)] stops in S and avoids v. The second trail [(1,0),(1,1),(1,2),(1,3)] is valid after normalization. At y = (1,2), the fixed endpoint e = (0,3) is a U corner missing its first arrival flag to (0,2), so the departure is uncovered and has distance two from e. Thus even the exception-location antecedent has a concrete instance.

[audit_model.py](/home/ubuntu/aklt/reports/TS_REC_07/scratch/audit_model.py) completed semantic checks on all 64 choices of extra removals in the central 3-by-3 core, plus a D-start domain and a boundary-corner domain. It checked 1,830 first prefixes, 1,637 second prefixes, 2,996 response pairs and 329 second starts; all 1,309 first U departures were covered, and all 41 sampled uncovered second U departures lay at positive distance at most two from the fixed endpoint. An explicit returning trail checked a U-to-D revisit followed by removal. Counts are in [audit_results.json](/home/ubuntu/aklt/reports/TS_REC_07/scratch/audit_results.json). These finite checks support the induction analysis; they are not proofs of the universally quantified leaves.

A single Lean process successfully imported NodesClosure and printed the exact eight statements and key structures in [inspect.lean](/home/ubuntu/aklt/reports/TS_REC_07/scratch/inspect.lean); output is in [lean_inspect.log](/home/ubuntu/aklt/reports/TS_REC_07/scratch/lean_inspect.log). Cached packages were linked in the scratch directory. No repository file was modified and no sub-agents were used.
