STATUS: COMPLETE

All eight assigned leaves are TRUE as written and self-sufficient. No missing premise, counterexample, unintended vacuity, or statement repair was found. The difficulty ratings include the expected Lean bookkeeping. Repository inspected: branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`.

| Leaf | Verdict | Difficulty | Basis |
| --- | --- | --- | --- |
| [AKLT.Blueprint.Win.SignedSideExclusionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:82) | TRUE | hard | The three signed-depth cases exclude every proposed coincidence. |
| [AKLT.Blueprint.Win.SquareIntersectionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:87) | TRUE | medium | Four sides times at most two perpendicular intersections. |
| [AKLT.Blueprint.Win.RawLayerCountStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:94) | TRUE | medium | Positive sphere radii and the supplied intersection bound give at most 48. |
| [AKLT.Blueprint.Win.NearSeriesStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:108) | TRUE | easy | Seventeen initial terms followed by a summable geometric tail. |
| [AKLT.Blueprint.Win.RawWeightSumStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:114) | TRUE | medium | The near layers and far cardinality have exactly the supplied bounds. |
| [AKLT.Blueprint.Win.ThickDepthStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:133) | TRUE | medium | A cross changes exterior distance by at most one. |
| [AKLT.Blueprint.Win.CutSeparationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:138) | TRUE | easy | The raw boundary blocks edges between the two pieces. |
| [AKLT.Blueprint.Win.OriginalPositivityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesRemoval.lean:10) | TRUE | hard | The retained lattice factors form a valid all-U finite spin network. |

The full JSON records are in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_WIN_06/verdicts.jsonl). Each record has a two-line proof route; these are directions for a writer, not supplied proofs.

The definition trace includes the ambient lattice, both distances, neighbour sets, bonds, original legs, ENat set distance and depth, decay, squares, shells, windows, exceptional indices, and the scale threshold in [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:5). For the taper leaves it also includes every relevant definition in [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:12): ShellSetup, CutSetup, starBall, cross, rawBoundary, thicken, squareDepth, radialOffset, taper, cutRaw, cutVolume, nearCost, coord, SignedUnit, NoCoincidence, sphere, tailCost, NoBond, and SeparatingCut. The actual side-intersection antecedent in [ParallelClearance](/home/ubuntu/aklt/repo/AKLT/Defs/Specification.lean:31) was checked separately.

For positivity, the trace includes [FiniteFactsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Common.lean:32), [FiniteSpinNetwork and its Valid, weight, and partition definitions](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:10), and the normalized finite-event definitions occurring in that premise. The target sums and pin assignments are in [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:8). The underlying Vec3, dot, normSq, UnitVector, explicit twelve-letter icosahedron vectors, Status, SpinLetter, spinVector, and spinWeight were read in [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8). In particular, the generic all-U site weights are exactly zero at None and 1/12 at every Some letter.

For the geometric leaves, write s=shellSpacing u, T=s/12, and k=shellRadius u i. Expanding CutSetup gives u>=390^4, s>=390, u=s^4, 2<=i<=s, and distance one from y to the physical square. Consequently each coordinate of y differs from that of a by at most u+1, and 2s-1<=k<=s^2. Thus k-T>0, u-31-T>0, s/3-2T=s/6>=65, and 2u+2-2T>32. These are consequences of the leaf's own hypotheses. CutScalesStatement and FiniteDepthStatement are definitions of other obligations, not silently available theorems; the elementary scale and distance facts used here can be derived directly. RawLayerCountStatement explicitly receives the square-intersection assertion, and RawWeightSumStatement explicitly receives the depth, counting, and series assertions it needs.

**SignedSideExclusionStatement: TRUE; hard.** Paper label `l:cutgeom`; corresponding argument starts at [sec5-window.tex:574](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:574).

CutSetup gives s>=390, u=s^4, k=floor(i*s)>=2*s-1 and |y_axis-a_axis|<=u+1. If an original radius-k supporting line has its fixed coordinate inside the physical square, its varying-coordinate interval meets the square (k>=1), so ParallelClearance really applies. The signed depths of the shifted line differ by at most j. Original depths inside, beyond the chosen side, or beyond the opposite side yield respectively shifted depth >=s/3-j>32+j, <=j<30+j, or >=2*u+2-j>32+j. None equals the quantified h.

Proof route: Derive the scale bounds and the coordinate enclosure of y directly from CutSetup; produce the actual side-intersection witness needed by ParallelClearance.  
Use the three signed-depth cases and |r-k|=j to contradict 30+j<=h<32+j under a proposed coincidence.

Lean traps: ParallelClearance is conditional on an actual side meeting the physical square. A fixed coordinate inside the square is not by itself its witness: also use the other coordinate of y lying within u+1 and k>=1 to obtain a point on the side. Keep signed depth in the outside cases; the truncated squareDepth would lose the required information. shellRadius is an integer floor of a real product, so retain k>=i*s-1 and the indicated coercions. Both signs and both Fin 2 coordinates remain explicitly quantified.

**SquareIntersectionStatement: TRUE; medium.** Paper label `l:cutgeom`; corresponding argument starts at [sec5-window.tex:618](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:618).

The two positive-radius sup-norm spheres are square boundaries. The explicit coordinate inequality excludes every pair of parallel supporting lines. Each of the four sides of the first square therefore meets only the two perpendicular sides of the second, giving at most eight lattice sites. No nonemptiness assumption on the intersection is needed.

Proof route: Cover the first sphere by its four signed coordinate sides.  
For each side, exclude parallel intersections and count at most two perpendicular intersections; use the cardinality bound for a finite union.

Lean traps: sphere uses square a r.toNat. Its positive-radius hypotheses justify recovering the original integer r from r.toNat; never silently replace an arbitrary integer by its toNat. Count distinct sites using a union bound, allowing duplicated corners. The coordinate exclusion forbids supporting-line coincidence even when the finite side segments would be disjoint; this is a sufficient stronger hypothesis.

**RawLayerCountStatement: TRUE; medium.** Paper label `l:cutgeom`; corresponding argument starts at [sec5-window.tex:574](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:574).

For fixed near offset j, the supplied height range puts integer h in {30+j,31+j}. Positive h removes the max-zero branch in squareDepth, so the site belongs to a sphere about a of radius u+1-h and a sphere about y of radius k-j or k+j. CutSetup implies k-j>0 and u+1-h>0. NoCoincidence supplies exactly the line inequalities in the explicitly supplied intersection bound. Thus even 2*2*8=32 sites suffice, and the requested 48 follows.

Proof route: Cover the filtered raw layer by the intersections indexed by the two radial signs and the allowed integer height levels, deriving both positive-radius conditions from CutSetup.  
Apply the supplied eight-point bound using NoCoincidence and bound the cardinality of the finite union by at most 48.

Lean traps: radialOffset is Int.natAbs, so offset=j gives two signed integer radius possibilities; it is not natural subtraction. squareDepth has a max-zero branch, removed here by h>=30+j>0. Before invoking the supplied sphere-intersection premise, derive positivity of k-j and u+1-h from CutSetup itself. At j=0 the two radial possibilities coincide, which only lowers the union cardinality. The half-open integer height interval actually has two levels, so 32 is also sufficient; 48 needs no correction.

**NearSeriesStatement: TRUE; easy.** Paper label `l:cutgeom`; corresponding argument starts at [sec5-window.tex:626](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:626).

The natural exponent max j 16 - 2 equals 14 for exactly j=0,...,16 and equals j-2 thereafter. The series is summable and equals theta^14 * (17 + theta/(1-theta)); theta/(1-theta) <= 1/(1-theta) for 0<theta<1 gives exactly the defined nearCost.

Proof route: Split off the seventeen indices 0,...,16 and identify the remaining series with theta^15 times the geometric series.  
Use its summability and sum 1/(1-theta), then multiply the elementary comparison by 48*theta^14.

Lean traps: The exponent max j 16 - 2 has type Nat, with subtraction performed before exponentiation. Since max j 16>=16, no truncation defect occurs. The indices j=0 through j=16 are seventeen terms, all theta^14; j=17 starts the tail at theta^15. nearCost uses ordinary natural power theta^14 and real division by 1-theta. The latter is strictly positive under the stated hypotheses. Summability is proved as part of this leaf, so tsum is being used with its intended convergent-series value.

**RawWeightSumStatement: TRUE; medium.** Paper label `l:cutgeom`; corresponding argument starts at [sec5-window.tex:626](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:626).

Split the finite raw set at t<=s/12. On the near part, monotonicity of theta^n and the supplied natural-depth bound, layer cardinalities, summability and series bound give nearCost. On the far part, theta^b<=theta^(s/12-1) by decreasing real powers; the supplied containment bounds the number of sites by (2*u+1)^2. This is smaller than the defined tailCost with its extra factor 4. Finite cutVolume has nonempty exterior, so boundaryDepth is finite; alternatively the top case contributes zero by decay.

Proof route: Group the near finite sum by radialOffset and dominate its nonnegative finite layer sum by the given summable infinite series.  
Use the far depth bound with real-power antitonicity and the cardinality of square a u, then combine the two bounds.

Lean traps: boundaryDepth has type ENat; top.toNat is zero, whereas decay at top is explicitly zero. Establish finiteness from the finite volume, or split the top case before using the depth exponent. Near powers have natural exponents, while tailCost uses Real.rpow at the real exponent s/12-1. Convert the natural power to real power and use its decreasing direction for 0<theta<1. The finite-layer comparison with tsum uses both the supplied summability and nonnegative summands. The square cardinality is a natural number cast to reals; the factor 4 in tailCost leaves slack.

**ThickDepthStatement: TRUE; medium.** Paper label `l:cutgeom`; corresponding argument starts at [sec5-window.tex:641](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:641).

Membership in thicken X0 supplies a centre x in X0 with latticeDist z x <= 1. Distance to the exterior is one-Lipschitz, so depth(z) >= depth(x)-1 >= 13; positive depth implies z in G. The exterior of every finite G in the infinite lattice is nonempty, so depth is finite. X0 empty and G empty cause no failure.

Proof route: Unpack the union of crosses and use the triangle inequality against every exterior site.  
Take the infimum to obtain depth(z)>=13, and rule out z outside G using its zero exterior distance.

Lean traps: The depth numerals 14 and 13 live in ENat. One can argue against every exterior site before taking the infimum, avoiding unjustified ENat subtraction; alternatively first establish finite depth. thicken is a finite union of five-point nearest-neighbour crosses, including each centre, rather than a union of nine-point star balls. No hypothesis X0 subset G or connectivity of X0 is missing: membership in G follows from the positive depth assumption.

**CutSeparationStatement: TRUE; easy.** Paper label `l:cutgeom`; corresponding argument starts at [sec5-window.tex:657](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:657).

The two displayed differences partition (F\B)\X and are disjoint. An edge from the U piece to the outside piece puts its outside endpoint in rawBoundary U, hence X, a contradiction. The U-to-F-exterior buffer gives the first piece's exterior restriction and B's exterior restriction; symmetry of adjacency and the B-neighbour buffer exclude edges from the other piece to B.

Proof route: Expand SeparatingCut and discharge its inclusions, disjointness, and union identity by finite-set membership.  
For the three NoBond conclusions use rawBoundary U subset X, NoBond U F-complement, and the B-neighbour buffer, with adjacency symmetry.

Lean traps: rawBoundary U is (U.biUnion starBall) minus U. Although starBall includes its centre, an endpoint outside U of a crossing nearest-neighbour edge belongs to this raw boundary. NoBond uses coerced sets and the full ambient complement of F. Its ordered arguments require adjacency symmetry when using the buffer around B to prove NoBond G2 B. The assertion also covers empty pieces and disconnected U; no connectedness assumption is needed.

**OriginalPositivityStatement: TRUE; hard.** Paper label `l:finitefacts`; corresponding argument starts at [sec5-window.tex:175](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:175).

Let H=G\Y and reindex its finite subtype by Fin H.card. Give every surviving site status U, orient each retained lattice bond by increasing new index, and enumerate only original legs of G whose tails survive as pins. Surviving bonds and original exterior legs use distinct members of the four physical neighbour slots, so this network is Valid. The explicitly assumed FiniteFactsStatement gives pinned and free positivity. Its Option IcoLetter sums equal the stated IcoLetter sums because every U none atom has weight zero; the empty network has one configuration and partition sum one. Y need not be a subset of G.

Proof route: Build the reindexed all-U FiniteSpinNetwork on G\Y, checking ordered distinct bonds and at most four incident retained bonds plus original pins per site.  
Identify its pinned/free partitions with the lattice sums by removing zero-mass None configurations, then apply the supplied finite-facts positivity, also at n=0.

Lean traps: FiniteSpinNetwork.Valid requires bonds ordered by the new Fin n indices, not by their original east/north orientation; reorient them and use symmetry of dot. Pins must remain originalLegs G with surviving tails, not originalLegs (G minus Y), which would introduce pins at holes. The generic sum uses SpinLetter=Option IcoLetter, but the target uses twelve IcoLetter labels: discard configurations with a None at any U site, since their product site weight is zero. Finset subtypes and function spaces over them carry Fintype instances; there is no Fintype Plane assumption. When n=0 the function space is a singleton, so neither partition is an empty sum. Points of Y outside G have no effect.

The upstream positivity argument is [Lemma l:finitefacts in sec2-moments.tex](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126); the removal application also occurs at [sec5-window.tex:278](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:278). No MomentsStatement or restriction on permitted removals is needed for this positivity bridge.

The setup is inhabited at the intended scale. For example, a=(0,0), u=390^4, y=(u+1,0), and i=2 have s=390 and k=780; the shell stays much farther than s/3 from every square corner, and its original sides that meet the square have the required parallel clearance. Empty intersections, the duplicated radial choice at j=0, empty thickening, empty cut pieces, and zero surviving spin sites were also considered. These cases do not make the universal statements unintentionally vacuous.

A single local inspection module, [inspect.lean](/home/ubuntu/aklt/reports/TS_WIN_06/inspect.lean), compiled successfully with Lean 4.35.0-rc2 against the repository's existing compiled modules. It contains only imports and print/check/synth/eval commands. Its [output](/home/ubuntu/aklt/reports/TS_WIN_06/inspect.log) confirms all eight declarations are closed Props with no silently dropped ambient instance arguments, confirms ordinary natural power in nearCost and real power in tailCost, and evaluates the natural exponents at j=0,16,17,18 as 14,14,15,16. It also confirms that the function space of spin assignments over an empty Finset subtype has cardinality one. Classical decidability is available for the finite filters and unions; no additional mathematical premise or Fintype instance for the ambient infinite plane is required. All arithmetic here is real/integer/natural as declared; there is no rational-division coercion defect.

Exact Python spot checks in [checks.py](/home/ubuntu/aklt/reports/TS_WIN_06/checks.py), with [output](/home/ubuntu/aklt/reports/TS_WIN_06/checks.log), covered 1,792 admissible small square pairs, 19,683 original/removed/surviving patterns on a 3-by-3 lattice patch, and 63 admissible large-scale signed-side configurations with 72,576 coordinate inequalities. All checks passed. They supplement the definition and argument audit; they do not constitute general proofs. No proof declarations were written, no sub-agents were launched, and the repository was not modified.
