STATUS: COMPLETE

| Leaf (all in `AKLT.Blueprint.Win`) | Verdict | Difficulty | Paper label |
| --- | --- | --- | --- |
| [CrossFactsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:141) | TRUE | easy | `l:thicken` |
| [CrossOverlapStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:147) | TRUE | easy | `l:thicken` |
| [CrossUnionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:151) | TRUE | medium | `l:thicken` |
| [NeighbourDecayStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:158) | TRUE | medium | `l:thicken` |
| [CrossWeightSumStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:164) | TRUE | easy | `l:thicken` |
| [ConnectedEnumerationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:171) | TRUE | medium | `l:Xconn` |
| [CutScalesStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:10) | TRUE | medium | `l:cutgeom` |
| [CoreConnectedStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:20) | TRUE | hard | `l:cutgeom` |

All eight statements are true as written and self-sufficient. No missing premise, counterexample, unintended vacuity, or correction was found. The extra global cross hypotheses are consistent; finiteness and the geometric inequalities needed by the other leaves follow from their stated hypotheses.

Repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`; the working tree was clean before and after the audit. No repository files were modified. No sub-agents were launched, and no proofs were written. Verdicts were appended to [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_WIN_04/verdicts.jsonl) as the leaves were settled.

**Definitions checked.** The following covers the mathematical definition dependencies of all eight statements, including dependencies hidden behind `CutSetup`.

| Source | Definitions and conventions inspected |
| --- | --- |
| [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) | `Plane = ℤ × ℤ`; `latticeDist`, `supDist`; `Compass`, its explicit `Fintype` instance and `Compass.step`; `Adjacent`, `neighbours`; `setDistance`, `boundaryDepth`, `decay`; `square`, `squareCorners`; `shellSpacing`, `shellRadius`, `lastShellIndex`, `shell`, `exceptionalIndices`, `geometryThreshold`. |
| [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:12) | `ShellSetup`, `CutSetup`; `StarAdjacent`, `JoinedIn`, `ConnectedIn`; `cross`, `thicken`; `squareDepth`, `radialOffset`, `taper`, `core`; all five fields of `RemovalEnumeration`. |
| Mathlib implementations | `Relation.ReflTransGen` is reflexive-transitive closure; `Finset.biUnion` removes duplicates; `ENat.toNat` sends infinity to zero. |

The imported top-level window statements add no assumptions to these definitions. In particular, neither the response property nor any unproved global geometric export is required as an additional hypothesis. The scale and coordinate facts used for `CoreConnectedStatement` can be derived directly from `CutSetup`.

**Lean cautions.** These are proof-writing concerns, not defects in the statements.

- `ConnectedIn R S` includes `S.Nonempty`. Although `JoinedIn` has reflexivity even outside `S`, every pair of endpoints in `ConnectedIn` is explicitly in `S`; nontrivial path steps also require both endpoints in `S`. Empty sets do not pass as connected, and singletons do.
- There is no `Fintype Plane`. The only full finite enumerations needed are `Compass`, `Fin (last + 1)`, or a finite subtype of a specified finset. Coercions `↑X` in connectivity are sets; the weighted sums and enumeration image are finsets.
- A finite volume has a nonempty exterior in the infinite lattice. Establish finiteness of `boundaryDepth` before converting it with `.toNat` or simplifying `decay`; its infinity branch and `.toNat ⊤ = 0` cannot be ignored without that step.
- Use `b(x) ≤ b(z) + 1` for neighbour decay. A rewrite involving `b(x) - 1` in `ℕ` would require handling truncated subtraction. In `RemovalEnumeration`, nonemptiness justifies `last = X.card - 1`; the singleton case gives `last = 0`.
- `shellSpacing` is a real double square root, not an integer fourth root. `shellRadius` is an integer floor. Lean inspection confirms that `(i - 1 : ℝ)` uses real subtraction, `shellSpacing u / 12` uses real division, and the weights and the factor `5 * c` are real-valued. The exponent in `decay` is natural.
- `squareDepth` is `max 0 ((u : ℤ) + 1 - (supDist z a : ℤ))`. The positive cutoff 32 permits its reduction to the inner-square condition; `radialOffset` takes `natAbs` after integer subtraction. No natural subtraction is hidden in either definition.
- Classical choices/decidability can be used when constructing paths, sorting, or minimizing. No extra decidability hypothesis is missing. Explicit elaboration confirmed that all eight leaves are closed propositions with the displayed quantifiers; no instance parameter or premise was silently dropped.

**Leaf assessments and two-line proof routes.**

**`AKLT.Blueprint.Win.CrossFactsStatement` — TRUE; easy.**

Plane is the unquotiented lattice Z x Z. Expanding neighbours gives the four distinct compass translates, all distinct from the centre; their union with the centre is exactly the latticeDist <= 1 ball. Each noncentre site is adjacent to the centre, so the nonempty cross is connected in the stated reflexive-transitive path sense. No hypotheses or typeclass parameters are missing.

Paper: [app-topology.tex:150](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:150) (`l:thicken`). Fix: None.

Route: Expand Compass.step and neighbours to list the five distinct coordinates and characterize latticeDist <= 1 by integer coordinate differences.  
Join every site to the centre by one edge or reflexivity, then concatenate the two centre paths.

**`AKLT.Blueprint.Win.CrossOverlapStatement` — TRUE; easy.**

StarAdjacent means supDist = 1, so the coordinate displacement is one of the eight nonzero vectors in {-1,0,1}^2. An axial displacement puts both centres in the intersection; a diagonal displacement gives the common point (y.1,x.2), as well as (x.1,y.2). The exact-distance definition excludes displacement zero, which would also cause no problem.

Paper: [app-topology.tex:155](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:155) (`l:thicken`). Fix: None.

Route: Split supDist = 1 into the four axial and four diagonal displacement cases using integer natAbs bounds.  
For an axial step choose a centre; for a diagonal step choose (y.1,x.2), and verify membership in both crosses.

**`AKLT.Blueprint.Win.CrossUnionStatement` — TRUE; medium.**

ConnectedIn explicitly includes nonemptiness of X0, and thicken is the duplicate-removing Finset.biUnion of its crosses. The two additional hypotheses supply connectedness of every cross and an intersection at every star edge. A path of centres therefore lifts to paths through overlapping crosses inside the union; the singleton case uses a reflexive centre path. These hypotheses are consistent and none is silently dropped.

Paper: [app-topology.tex:162](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:162) (`l:thicken`). Fix: None.

Route: Choose a centre for each endpoint in thicken and a JoinedIn star path between these centres in X0.  
Induct on that path, concatenate paths through the asserted cross intersections, and obtain nonemptiness from any centre.

**`AKLT.Blueprint.Win.NeighbourDecayStatement` — TRUE; medium.**

Every finite G in Z x Z has a nonempty complement, so both boundaryDepth values are finite natural minima, even when G is empty or an endpoint is outside G. The triangle inequality gives b(x) <= b(z) + 1. For 0 < theta < 1, theta^(b(z)+1) <= theta^b(x), which is the requested bound after dividing by theta. The paper's extra containment G superset X is unnecessary for this local inequality. Lean trap: ENat.toNat sends infinity to zero, so finiteness must be established before reducing decay to a natural power; use b(x) <= b(z)+1 rather than truncated natural subtraction.

Paper: [app-topology.tex:169](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:169) (`l:thicken`). Fix: None.

Route: Find an exterior point of finite G, obtain attained finite complementary distances, and apply the lattice-distance triangle inequality to get b(x) <= b(z)+1.  
Use antitonicity of natural powers for 0 < theta < 1 and divide theta^(b(z)+1) <= theta^b(x) by the positive theta.

**`AKLT.Blueprint.Win.CrossWeightSumStatement` — TRUE; easy.**

Nonnegative weights allow the sum over the Finset.biUnion to be bounded by the sum over all crosses with multiplicity. The local bound and the supplied cardinality five give each inner sum <= 5*c*f(x); finite-sum distributivity gives exactly the right-hand side. Empty X0 gives 0 <= 0; c=0 is also consistent, for example f=0. No disjointness or Fintype Plane is needed. The numeral 5 and all multiplication in the inequality are real-valued; c>=0 is harmless and stronger than necessary for this summation argument.

Paper: [app-topology.tex:174](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:174) (`l:thicken`). Fix: None.

Route: Overcount the union using nonnegativity: sum over thicken <= sum over x in X0 of the sum over cross x.  
Apply the pointwise bound to each inner sum, rewrite its cardinality as five, and factor 5*c out of the outer sum.

**`AKLT.Blueprint.Win.ConnectedEnumerationStatement` — TRUE; medium.**

ConnectedIn contains Set.Nonempty, so X.card >= 1 and last = X.card-1 is legitimate. Finite paths in X give finite shortest-path distances from a root; ordering vertices by distance with arbitrary finite tie-breaking supplies an injective, surjective site map and an earlier adjacent predecessor for every positive index. The predecessor relation has the orientation from the later vertex to the earlier one, which is available because Adjacent is symmetric. A singleton uses last=0 and has no positive index. Classical choice is permitted; no Fintype instance for the infinite Plane is assumed.

Paper: [sec5-window.tex:685](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:685) (`l:Xconn`). Fix: None.

Route: Choose a root in X, assign each vertex its shortest path length in the induced finite graph, and enumerate by increasing distance with ties broken by a finite order.  
Set last=X.card-1; the sorted bijection gives injective and image_eq, and a shortest-path predecessor gives previous for each positive index.

**`AKLT.Blueprint.Win.CutScalesStatement` — TRUE; medium.**

ShellSetup 64 supplies u >= geometryThreshold 64 = 390^4. For s=sqrt(sqrt(u)), nonnegativity gives s>=390 and s^4=u. The index bounds are exactly 2<=i and (i:Real)<=s. With k=floor(i*s), i*s-1<k<=i*s yields 2*s-1<=k<=s^2<=u-31; the strict predecessor clearance follows from 11*s/12-2>0. Exterior-seed and nonexceptionality assumptions are unused here but consistent. Lean inspection confirms (i-1:Real) subtracts in Real and s/12 is real division; there is no natural subtraction, rounding of s, or zero denominator.

Paper: [sec5-window.tex:419](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:419) (`l:cutgeom`). Fix: None.

Route: Unfold ShellSetup and geometryThreshold to obtain u>=390^4; use the nonnegative square-root identities to derive s>=390 and s^4=u.  
Combine floor bounds with 2<=i<=s, s^2<=s^4-31, and 11*s/12-2>0 to obtain all five displayed conclusions.

**`AKLT.Blueprint.Win.CoreConnectedStatement` — TRUE; hard.**

CutSetup implies s>=390, 32<=k=floor(i*s)<=u-31, and |y_j-a_j|<=u+1 for both coordinates, the latter from an attained sup-distance-one point in square a u. With m=u-31, the condition squareDepth>=32 is exactly supDist(z,a)<=m. Thus core is the radius-k square boundary clipped by the inner square of radius m. Each clipped coordinate interval is nonempty (k>=32) and contains a shell endpoint (k<=m); their product contains a shell corner. All surviving side segments join through that corner, so the core is nonempty and nearest-neighbour connected. On core, radialOffset=0, so both taper inequalities hold. Nonexceptionality is unnecessary for this leaf. Lean traps are integer casts and the max-with-zero in squareDepth, not absent geometric premises.

Paper: [sec5-window.tex:463](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:463) (`l:cutgeom`). Fix: None.

Route: Derive the scale bounds and |y_j-a_j|<=u+1 directly from CutSetup; identify core with the radius-k square boundary intersected with the inner square of radius m=u-31.  
Choose one shell endpoint in each clipped coordinate interval, join all surviving side segments through their common corner, and use radialOffset=0 to establish core subset taper.

**Nonvacuity and boundary cases.** A singleton centre set satisfies the connectivity premises; `f = 0, c = 0` satisfies the weight hypotheses, while `f = 1, c = 1` gives nonzero examples. `G = ∅` gives depth zero everywhere and the neighbour-decay inequality `1 ≤ θ⁻¹`. Singleton connected sets have removal enumerations with one site and no predecessor obligation.

For both taper leaves, an explicit admissible setup is `a = (0,0)`, `u = 390^4 = 23134410000`, `y = (u+1,0)`, `i = 2`. Then `s = 390`, `k = 780`, and the distance from `y` to the square is one. Every shell site has second coordinate between `-780` and `780`, so its distance to each square corner is at least `u-780 > s/3`; thus index 2 is nonexceptional. The core contains `(u-779,0)`. This rules out contradictory-setup vacuity. Nonexceptionality is not needed for either of these two conclusions, but is consistent with them.

**Verification.** [Inspect.lean](/home/ubuntu/aklt/reports/TS_WIN_04/Inspect.lean) imported the two existing blueprint modules and printed the elaborated propositions and key definitions. The single Lean process exited successfully; it wrote no proof and built no repository module. Full output is in [lean-inspection.txt](/home/ubuntu/aklt/reports/TS_WIN_04/lean-inspection.txt). Repository packages were linked read-only into the local scratch setup.

[audit_checks.py](/home/ubuntu/aklt/reports/TS_WIN_04/audit_checks.py) passed the following checks; [checks.json](/home/ubuntu/aklt/reports/TS_WIN_04/checks.json) contains the counts and witness.

- All 512 subsets of a 3×3 grid: 388 nonempty star-connected subsets thicken to connected sets, and all 218 nonempty nearest-neighbour-connected subsets admit the required enumeration.
- Cross tests: 25 translated centres, 2,025 distance-membership pairs, and all 200 star-neighbour overlap cases.
- 1,536 exact rational weight-sum checks, including empty sets, zero weights, repeated cross overlap, and nonconstant weights; 192,000 exact rational neighbour-decay checks, including empty volumes and exterior endpoints.
- 11,860 exact shell-scale cases at and around fourth-power thresholds and at larger volumes. The script computes `floor(i*u^(1/4))` and compares positive fourth powers using integer arithmetic; no floating-point rounding is involved.
- 1,212 checks of the reduced clipped-shell geometry, including 20 singleton cores. These check the geometric reduction under `32 ≤ k ≤ m` and coordinate bounds, rather than claim that small test squares satisfy the global threshold. The actual threshold setup above was also checked through its clipped shell; its core has 3,057 sites.

These finite checks support the mathematical audit; they are not formal proofs. File hashes for the inspected Lean and paper sources are recorded in [source-manifest.json](/home/ubuntu/aklt/reports/TS_WIN_04/source-manifest.json).
