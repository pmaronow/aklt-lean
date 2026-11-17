STATUS: COMPLETE

All eight leaves are **TRUE and self-sufficient as written**. No correction or additional premise is needed. None is vacuous in the sense of the brief. Names in the table have namespace `AKLT.Blueprint.Win`; their module is `AKLT.Blueprint.Win.NodesTopology`, and their paper label is `l:boundaryconn`.

| Leaf / exact statement source | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| [PlaquetteReconstructionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:73) | TRUE | hard | The tail coefficients reconstruct every finite nearest-neighbour even chain; any finite superset of their nonzero locus works as `P`. |
| [PlaquetteTrianglesStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:81) | TRUE | easy | The common diagonal of two triangle generators cancels over `ZMod 2`. |
| [CutEdgesNonemptyStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:85) | TRUE | easy | A point with maximal first coordinate has an exterior right neighbour. |
| [LinkedSeparationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:89) | TRUE | medium | A finite reachability component is a nonempty proper `LinkClosed` subset. |
| [TriangleCutParityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:97) | TRUE | medium | Triangle crossings occur in a linked pair and cancel modulo two. |
| [TwoCrossingCycleStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:121) | TRUE | hard | Two paths confined to their respective sides and the distinct crossing edges give the required even chain. |
| [TwoCrossingParityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:128) | TRUE | easy | Exactly the summand at `e` survives on `E`. |
| [OuterEndpointTransferStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:134) | TRUE | medium | Exterior endpoints carry linked-edge paths to boundary star paths, allowing equal endpoints. |

The reviewed repository revision is `7a3393531c12080d76aefbdab300ac0c2df834b7`. The paper argument was read in [app-topology.tex](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:10), including the definition of paths at line 4 and the full proof through line 135. Verdicts follow from the exact definitions and that argument; the computations below are supplementary checks. No Lean proofs were written or compiled, no sub-agents were launched, and the repository was not modified.

**Definition trace.** All project definitions used by the statements were read, including their geometry dependencies. `Plane` is the full integer plane, not a finite quotient. The core geometry definitions are in [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8); the topology and chain definitions are in [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:20).

| Leaves | Definitions traced |
| --- | --- |
| Reconstruction | `Plane`, `Adjacent`, `latticeDist`, `LatticeEdge`, `EdgeChain`, `ChainNN`, `ChainEven`, `ChainInBox`, `horizontal`, `tailCoefficient`, `plaquette`, `edge`. |
| Plaquette triangles | `Plane`, `LatticeEdge`, `EdgeChain`, `plaquette`, `edge`, `triangleSpan`, `triangle`, `IsTriangle`, `StarAdjacent`, `supDist`. |
| Cut nonemptiness | `Plane`, `LatticeEdge`, `cutEdges`, `starBall`. |
| Linked separation | `Plane`, `LatticeEdge`, `cutEdges`, `starBall`, `JoinedIn`, `Linked`, `IsTriangle`, `StarAdjacent`, `supDist`, `LinkClosed`. |
| Triangle cut parity | `Plane`, `LatticeEdge`, `EdgeChain`, `LinkClosed`, `cutEdges`, `starBall`, `Linked`, `IsTriangle`, `StarAdjacent`, `supDist`, `cutParity`, `triangle`, `edge`. |
| Two-crossing cycle | `Plane`, `LatticeEdge`, `EdgeChain`, `ConnectedIn`, `JoinedIn`, `StarAdjacent`, `supDist`, `cutEdges`, `starBall`, `ChainStar`, `ChainEven`, `TwoCrossings`. |
| Two-crossing parity | `Plane`, `LatticeEdge`, `EdgeChain`, `cutEdges`, `starBall`, `TwoCrossings`, `cutParity`. |
| Exterior endpoint transfer | `Plane`, `LatticeEdge`, `cutEdges`, `starBall`, `JoinedIn`, `Linked`, `IsTriangle`, `StarAdjacent`, `supDist`, `ConnectedIn`, `rawBoundary`. |

Relevant library meanings were also checked locally: `Sym2` is the quotient identifying reversed pairs and its membership is ordinary endpoint membership; `Finsupp.support` is exactly the nonzero locus; `Finsupp.single` gives one edge coefficient; `ZMod 2` has characteristic two; `Submodule.span` contains finite linear combinations of its generators; `Relation.ReflTransGen` permits zero steps; `Finset.Icc` includes both endpoints; `image` and `biUnion` remove duplicates.

**Two-line proof routes and statement-specific checks.** These are routes for the future writers, not formal proofs. The same two-line routes, detailed reasons, and difficulty ratings are in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_WIN_03/verdicts.jsonl).

**PlaquetteReconstructionStatement — hard.** Paper lines 60–81.

1. Evaluate both chains at an arbitrary unordered edge; reduce nearest-neighbour edges to horizontal/vertical cases and use `P`'s zero-outside condition to recover the two adjacent tail coefficients.
2. Use adjacent-tail cancellation horizontally and the finite even-degree telescoping identity vertically, treating rows below `-R` and at/above `R` with column flux and `ChainInBox`.

The horizontal coefficient is `n(i,j-1)+n(i,j)` and the vertical coefficient is `n(i-1,j)+n(i,j)`. The strict tail condition `j < r` has the correct index. The top vertical term vanishes because its upper endpoint is outside the box. Below `-R`, the full tail equals the explicitly assumed zero column flux. `P` may contain extra zero coefficients and need not be rectangular. Non-nearest-neighbour edges, including loops, vanish on both sides. The zero chain with `P = ∅` is valid.

**PlaquetteTrianglesStatement — easy.** Paper lines 82–86.

1. Use the triangles `(p,p+(1,0),p+(1,1))` and `(p,p+(1,1),p+(0,1))`, whose membership in `triangleSpan` follows from its generating set.
2. Add them in the submodule and cancel the shared diagonal in characteristic two to obtain `plaquette p`.

Both triangles satisfy all three star-adjacency requirements for every integer translate. Reversed edge representations must be identified in `Sym2`; cancellation is over `ZMod 2`.

**CutEdgesNonemptyStatement — easy.** Paper lines 88–91.

1. Choose `x ∈ A` maximizing the first coordinate, and set `y=(x.1+1,x.2)`; maximality gives `y ∉ A`.
2. Check `y ∈ starBall x` and insert `s(x,y)` through `Finset.mem_biUnion` and `Finset.mem_image`.

Finiteness comes from `A : Finset Plane`; `A.Nonempty` supplies the maximum. Connectivity is unnecessary. All coordinates and increments are integers.

**LinkedSeparationStatement — medium.** Paper lines 92–98.

1. Classically choose cut edges `e,f` with no `JoinedIn` path from `e` to `f`, and filter `cutEdges A` by reachability from `e`.
2. Use reflexivity for `e`, the chosen nonreachability for `f`, and closure of `ReflTransGen` under one further step for `LinkClosed`.

The negated bounded universal already supplies two cut edges and a proper component; no `A.Nonempty` hypothesis is missing. The empty cut makes the antecedent false, as intended. Although `Linked` is symmetric, forward reachability closure suffices for this particular conclusion. Filtering by reachability and extracting the witnesses require classical reasoning.

**TriangleCutParityStatement — medium.** Paper lines 99–107.

1. Classify the three vertices by membership in `A`; identify the zero or two triangle edges that lie in `cutEdges A`.
2. Use `LinkClosed` to give the two crossing edges equal `E`-membership, then evaluate the triangle coefficients and cancel in `ZMod 2`.

`IsTriangle` forces three distinct vertices and three distinct unordered edges. The subset clause in `LinkClosed` excludes noncrossing triangle edges from `E`, and its closure clause keeps the crossing pair together. Both clauses are present. Establish distinctness before simplifying the `Finsupp.single` coefficients.

**TwoCrossingCycleStatement — hard.** Paper lines 111–122.

1. Orient `e,f` by their `A`-membership witnesses, obtain the inside and outside `ReflTransGen` paths, and add their finite edge chains together with the two crossing-edge chains.
2. Track endpoint incidence modulo two to get `ChainEven`, retain star support under cancellation, and use the paths' side membership plus `e ≠ f` to verify `TwoCrossings`.

Each cut edge has exactly one endpoint in `A`. The two connectivity premises give the required paths even though the complement is infinite. Their internal edges never cross the cut. Shared inside or outside endpoints give zero-length paths and remain valid. Use traversal counts modulo two: taking the ordinary union of traversed edges would not in general give an even chain. The stated `e ≠ f` is essential for the disjunctive definition of `TwoCrossings` and is present.

**TwoCrossingParityStatement — easy.** Paper lines 120–123.

1. Restrict `TwoCrossings` to `g ∈ E` using `E ⊆ cutEdges A` and eliminate `g = f` using `f ∉ E`.
2. Evaluate `cutParity E c` by the single surviving summand at `e`, using `e ∈ E`.

`e ∈ E` and `f ∉ E` already imply `e ≠ f`; no extra premise is needed. Values of `c` outside the cut are irrelevant, so this leaf correctly does not require `ChainStar` or `ChainEven`.

**OuterEndpointTransferStatement — medium.** Paper lines 126–135.

1. Define the exterior-endpoint map on the finite cut-edge subtype, establish its image is `rawBoundary A`, and use cut nonemptiness to obtain a boundary point.
2. Induct along each `JoinedIn Linked` path, replacing a step by reflexivity for equal exterior endpoints or one star step otherwise, and transfer connectivity by surjectivity.

The endpoint must be chosen by its exterior membership, independently of a representative of the unordered pair. Surjectivity follows directly from the definitions of `cutEdges` and `rawBoundary`; it does not require an additional distance-to-set premise. A linked pair can have equal exterior endpoints, so a direct map of relations to `StarAdjacent` would be too strong. `ReflTransGen` handles those equalities with zero steps. The explicit nonempty cut supplies the nonempty conjunct of `ConnectedIn`; no separate connectivity premises on `A` or its complement are needed here.

**Shared Lean traps and vacuity checks.**

- `LatticeEdge := Sym2 Plane` includes loops and arbitrary pairs. `ChainEven` counts membership in a pair once, so on a loop it would differ from the usual graph-degree convention. This causes no defect here: reconstruction assumes `ChainNN`, the cycle conclusion requires `ChainStar`, and triangles and cut edges are loop-free by their definitions.
- All sums are over explicit `Finset`s or `Finsupp.support`. The lattice, its edge type, and the exterior set are infinite; no global `Fintype` instance is needed or silently available.
- `JoinedIn R S x x` is reflexive even if `x ∉ S`. All uses here also have the necessary endpoint memberships from cut membership or `ConnectedIn`; path-transfer induction must preserve those memberships explicitly.
- A `noncomputable section` is not a replacement for `classical` in a future proof. In particular, use classical decidability for a reachability filter and classical witness extraction in separation.
- Distances use `Int.natAbs` of integer differences; the box radius and all tail indices are integers. There is no truncated natural subtraction in these leaves, no real/rational coercion, and no division-by-zero issue. Chain coefficients, scalar actions, and parity values are all over `ZMod 2`.
- The statements have concrete types and explicit hypotheses; no section-level instance argument or mathematical premise has been silently dropped.
- Nontrivial hypotheses are satisfiable. A single plaquette witnesses reconstruction. A singleton `A` witnesses nonempty cuts, two-crossing cycles, and exterior transfer. For separation, `A={(0,0),(4,0)}` has two nonempty linked components: a triangle cannot contain both inside vertices. Selecting one component gives nontrivial instances of triangle parity and two-crossing parity as well. Conditional cases with empty cuts do not make any whole leaf unintentionally vacuous.

**Finite checks.** The reproducible standard-library Python script is [checks.py](/home/ubuntu/aklt/reports/TS_WIN_03/checks.py); its output is [checks-results.json](/home/ubuntu/aklt/reports/TS_WIN_03/checks-results.json). Running `python3 checks.py` passed all assertions.

| Check | Coverage | Result |
| --- | --- | --- |
| Plaquette reconstruction | 4,096 cases: all 512 even chains on a 4×4 nearest-neighbour grid, at four translations and two admissible radii; three choices of `P` each, including minimal support and extra zero terms. Includes eight zero-chain cases. | Pass |
| Plaquette triangle split | 49 integer translates, including negative coordinates. | Pass |
| Cuts, links, boundary image | All 512 subsets of a 3×3 grid; 124 cases with nontrivial separation and 387 cases satisfying exterior endpoint transfer. | Pass |
| Triangle cut parity | 42,048 triangle/component combinations. | Pass |
| Linked exterior endpoints | 19,456 linked pairs checked for equal or star-adjacent outer endpoints. | Pass |
| Two-crossing cycle | 131,556 distinct cut-edge pairs across 387 sets with both sides connected; includes 23,616 shared-inside-endpoint pairs and 5,896 shared-outside-endpoint pairs. | Pass |
| Two-crossing parity | 3,584 choices of a subset of an eight-element cut, an edge in it, and an edge outside it. | Pass |

For the grid-subset checks, the infinite complement is represented by its intersection with a one-site collar. This is sufficient for those examples because the collar boundary is connected, contains no point of `A`, and can replace excursions farther outside. The checks supplement the general mathematical audit; they are not machine-checked proofs of the Lean propositions.
