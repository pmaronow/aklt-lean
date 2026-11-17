STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| `AKLT.Blueprint.Win.PredecessorShellStatement` | TRUE | medium | Integrality pins the predecessor radius to the floor of the real cutoff. |
| `AKLT.Blueprint.Win.SeedSeparationStatement` | TRUE | easy | Every far-volume radius is strictly greater than two. |
| `AKLT.Blueprint.Win.FiniteDepthStatement` | TRUE | medium | A finite volume has nonempty exterior and finite, attained, Lipschitz depth. |
| `AKLT.Blueprint.Win.BoundaryMembershipStatement` | TRUE | medium | The union of closed unit sup-balls, minus the set, is its distance-one exterior boundary. |
| `AKLT.Blueprint.Win.ChainBoxStatement` | TRUE | easy | The finite support has finitely many endpoints. |
| `AKLT.Blueprint.Win.DiagonalEliminationStatement` | TRUE | hard | Triangle corrections remove every diagonal and preserve even incidence. |
| `AKLT.Blueprint.Win.ColumnFluxStatement` | TRUE | hard | Summing even incidences in a half-plane cancels internal edges in characteristic two. |
| `AKLT.Blueprint.Win.TailSupportStatement` | TRUE | easy | The box bounds columns; zero flux makes the lower tail vanish. |

All eight leaves are true and self-sufficient as written. No corrected statement or additional premise is needed. Difficulty estimates concern Lean formalization from the existing definitions. The two hard leaves require careful finite-support and incidence bookkeeping, although their mathematical arguments are elementary. The machine-readable records, including a two-line route per leaf, are in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_WIN_02/verdicts.jsonl).

The audit used repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, and the supplied manuscript sources. The repository was only read. No proofs were written and no sub-agents were launched.

The statements and definitions checked were:

- Shell leaves: [NodesShell.lean:66](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:66) and [NodesShell.lean:73](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:73), against `l:shellgeom` in [sec5-window.tex:112](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:112).
- Topology leaves: [NodesTopology.lean:37](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTopology.lean:37) through `TailSupportStatement`, against `l:thicken` in [app-topology.tex:169](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:169) and `l:boundaryconn` in [app-topology.tex:10](/home/ubuntu/aklt/manuscript-v2/app-topology.tex:10).
- Geometry definitions: `Plane`, `latticeDist`, `supDist`, `Adjacent`, `setDistance`, `boundaryDepth`, `square`, `shellSpacing`, `shellRadius`, `farVolume`, and `shell` in [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8).
- Boundary and chain definitions: `StarAdjacent`, `starBall`, `rawBoundary`, `LatticeEdge`, `EdgeChain`, `edge`, `triangle`, `IsTriangle`, `triangleSpan`, `ChainStar`, `ChainNN`, `ChainEven`, `ChainInBox`, `horizontal`, and `tailCoefficient` in [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:20).
- Relevant library semantics: the complete order on `ENat`, infimum attainment, `ENat.toNat`, endpoint membership in `Sym2`, exact `Finsupp.support`, `Finsupp.single`, `Submodule.span`, and characteristic two in `ZMod 2`.

**Per-leaf findings and routes**

`PredecessorShellStatement` — TRUE, medium. Put `t=((i:ℝ)-1)*shellSpacing u`. Being in the square but outside `farVolume` bounds the integer radius of `x` above by `t`. A far-volume witness within distance one has integer radius greater than `t` and at most one larger. Consequently the old radius is `⌊t⌋`, exactly the shell indexed by the integer `i-1`. The absence of `ShellSetup`, an exterior-seed premise, or a size threshold is harmless. Empty far volumes cannot satisfy the distance premise.

Route 1: Extract a far-volume point within distance one from the extended-natural infimum and use the sup-distance triangle inequality.  
Route 2: Apply the integer floor bounds and rewrite the cast of `i-1` to obtain membership in the predecessor shell.

`SeedSeparationStatement` — TRUE, easy. The stated hypotheses give `((i:ℝ)-1)*shellSpacing u ≥ 2`, and every far-volume point has strictly larger radius. This uses neither the location of `y` nor connectivity. An empty far volume has distance `⊤`.

Route 1: Bound each far-volume point's distance from `y` strictly above two, using symmetry of `supDist`.  
Route 2: A set-distance bound of one would yield a conflicting witness; the empty case has infinite distance.

`FiniteDepthStatement` — TRUE, medium. Since `Plane = ℤ × ℤ` is infinite and `G` is a `Finset`, its exterior is nonempty. Natural-valued distances attain their infimum. Distance zero means equality with an exterior point, and the ambient Manhattan triangle inequality yields the final bound for every `x,y`. No containment or connectivity hypothesis is needed. For `G=∅`, all depths are zero.

Route 1: Choose an exterior point beyond a finite coordinate bound, then establish finiteness, attainment, and the `toNat` identity.  
Route 2: Use separation for the zero-depth equivalence and a nearest exterior point to `y` for the Lipschitz inequality.

`BoundaryMembershipStatement` — TRUE, medium. `starBall` includes its centre and all eight star-neighbours. Removing `U` removes the possible zero-distance sites, leaving exactly exterior sites with minimum sup-distance one. If `U=∅`, `rawBoundary U` is empty and its set-distance is `⊤`, so both sides of the equivalence are false. No nonemptiness or connectivity premise is missing.

Route 1: Expand the union, difference, and coordinate intervals to obtain an exterior site with a witness at sup-distance at most one.  
Route 2: Exclude distance zero and use attainment to equate this condition with set-distance exactly one.

`ChainBoxStatement` — TRUE, easy. The support of a `Finsupp` is finite even though `LatticeEdge` is infinite. Each unordered pair has at most two endpoints. A maximum of their absolute coordinates, enlarged to one, supplies the required integer radius. No adjacency restrictions are needed; loops and nonlocal edges are allowed, and the zero chain admits `R=1`.

Route 1: Form the finite union of endpoint sets of edges in `c.support` and bound their absolute coordinates.  
Route 2: Enlarge the bound to one and unfold `ChainInBox`.

`DiagonalEliminationStatement` — TRUE, hard. The support restriction excludes loops and makes every non-NN edge a unit diagonal. A triangle through either intermediate axial corner contains that diagonal and two NN edges. Adding its boundary cancels the diagonal and preserves evenness. The finite sum of corrections is in `triangleSpan`; characteristic two identifies the required difference with that correction. The zero chain is covered. The source comment's word “unique” is unnecessary: there are two valid triangle choices, and the statement requires only existence.

Route 1: Choose a triangle correction for each diagonal in the original support and sum these finitely many generators.  
Route 2: Add the correction to `c`; verify NN support and even incidence, and identify `c-d` with the span element.

`ColumnFluxStatement` — TRUE, hard. Sum the even-incidence equations over supported vertices in the half-plane with first coordinate at most `i`. Internal edges occur twice; crossing NN edges occur once and are exactly the horizontal edges in column `i`. The endpoint box places their row indices in the inclusive interval `[-R,R]`. Columns outside the box and the zero chain also satisfy the identity.

Route 1: Sum over the finite set of supported endpoints in the half-plane, then interchange finite incidence sums.  
Route 2: Cancel double contributions in `ZMod 2` and identify the remaining terms with the displayed column flux.

`TailSupportStatement` — TRUE, easy. An explicit witness is `P = (Finset.Icc (-R) R).product (Finset.Icc (-R) R)`. Outside its column interval, `ChainInBox` forces every horizontal coefficient to zero. For rows above the box the tail is empty; below it the tail is the full column flux and hence zero. The endpoint `j=-R` is correctly retained in `P`, since the strict test `j<r` can leave a nonzero tail there. The explicit zero-flux premise suffices without `ChainNN` or `ChainEven`.

Route 1: Choose this finite product box and use support membership to rule out nonzero horizontal terms outside its columns.  
Route 2: Split outside rows into `j>R` and `j<-R`; use an empty tail in the first case and the full zero column sum in the second.

**Lean traps checked**

- `setDistance` is an infimum in `ℕ∞` over a subtype. Its empty-set value is `⊤`; infima of natural-valued distances over nonempty sets are attained. No finite `Fintype` instance for the exterior is required.
- `ENat.toNat ⊤ = 0`. Establish finite depth before transferring statements to `ℕ`; the finiteness clause in `FiniteDepthStatement` supplies exactly this fact.
- Shell cutoffs use `ℝ`; shell radii and the index subtraction use `ℤ`; metric values use `ℕ`. Rewrite casts explicitly when comparing floors. These leaves contain no division or truncated natural subtraction.
- `Sym2` identifies the two orientations of an edge and allows loops. Endpoint membership counts a loop once in `ChainEven`. `ChainStar` and `ChainNN` exclude loops where the degree arguments require their absence; `ChainBox` and `TailSupport` remain valid with loops.
- `ChainEven` sums over the exact nonzero support, which can change after additions. To preserve evenness, justify incidence additivity using a common finite support bound or a linear incidence map.
- `Finset.Icc (-R) R` is an inclusive integer interval. `tailCoefficient` uses the strict condition `j<r`; do not drop the bottom boundary row from the support witness.
- All chain coefficients, sums, differences, and span operations use `ZMod 2`. The cancellation of two copies is valid there.
- Classical decidability is available in the noncomputable definitions and can be introduced locally by writers. The eight elaborated leaves are closed propositions: no implicit instance or hypothesis was silently dropped. There are no rational coercions in these leaves.

**Validation**

Lean `v4.35.0-rc2` successfully inspected the two existing modules, printed all eight closed statements and key unfolded definitions with explicit instances, and checked the relevant `ENat`, `Sym2`, `Finsupp`, and characteristic-two interfaces. Only one Lean process was used. The source is [scratch/Inspect.lean](/home/ubuntu/aklt/reports/TS_WIN_02/scratch/Inspect.lean), with output in [scratch/lean_inspection.txt](/home/ubuntu/aklt/reports/TS_WIN_02/scratch/lean_inspection.txt). This inspection does not prove the leaves.

The independent [finite-case checks](/home/ubuntu/aklt/reports/TS_WIN_02/scratch/small_case_checks.py) passed; their exact counts are in [small_case_results.json](/home/ubuntu/aklt/reports/TS_WIN_02/scratch/small_case_results.json):

| Check | Coverage |
| --- | --- |
| Shells | 10,878 configurations with two translates, `u=0,…,6,16,17`, and `i=2,…,8`; 105,712 qualifying predecessor points and 2,316 empty far volumes. |
| Seed separation | 1,372 configurations satisfying the spacing premise, all with nonempty far volumes. |
| Finite depth | All 512 subsets of a 3×3 grid; 320,000 ordered Lipschitz comparisons using exact exterior-distance searches. |
| Boundary membership | 25,088 queries, including the empty set and sites beyond the possible boundary. |
| Chain boxes | 8,194 instances, including the zero chain, a loop, and a nonlocal edge. |
| Diagonal elimination | All 4,096 even star chains on a 3×3 grid; verified NN support, evenness, and the finite triangle correction. |
| Column flux | All 512 even NN chains on a 4×4 grid, tested in two containing boxes; 10,240 column queries. |
| Tail support | 1,024 boxed zero-flux chains without assuming NN support or evenness, including loops, diagonals, and nonlocal edges; 73,728 queries outside the proposed support box. |

The shell checks compare integer fourth powers and use integer square roots, avoiding floating-point errors at cutoff or floor boundaries. Negative controls detect the nonzero flux of a single horizontal edge, its persistent lower tail when the zero-flux premise is removed, and a seed at distance one when the spacing premise is removed. These finite searches support the definition and edge-case audit; the verdicts rest on the general routes above. None of the eight statements is true merely because its premises are contradictory or its quantified type is empty.
