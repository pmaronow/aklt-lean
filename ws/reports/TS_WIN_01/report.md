STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| [`ShellScaleStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:10) | TRUE | medium | The natural threshold gives every stated real scale bound. |
| [`CloseCornerStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:19) | TRUE | medium | The exterior ring has at most one corner at distance strictly below u. |
| [`ExceptionalLocalizationStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:25) | TRUE | medium | The exceptional filter supplies the index range and the required witness. |
| [`RadiusGapStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:33) | TRUE | easy | The floor gap works for all signed integer indices. |
| [`ExceptionalCountStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:38) | TRUE | easy | The three explicit premises force at most one exceptional index. |
| [`SideCornerWitnessStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:49) | TRUE | hard | A failed parallel clearance supplies a corner witness. |
| [`NearShellCountStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:55) | TRUE | hard | Eight perpendicular side-strip intersections each contain at most l sites. |
| [`ShellInclusionStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesShell.lean:61) | TRUE | easy | The floor radius passes the strict far-volume filter. |

All eight names are in `AKLT.Blueprint.Win`. Each statement is true as written and self-sufficient. No corrected statement or additional premise is required. No leaf is globally vacuous; the allowed large-square setups exist and the exceptional-witness case can occur.

Reviewed repository `main` at commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The comparison is with [Lemma l:shellgeom](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:27), its argument at lines 40–123, and [Definition d:shells](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:10). The exact elaborated statements and relevant definitions are saved in [lean-inspection.txt](/home/ubuntu/aklt/reports/TS_WIN_01/checks/lean-inspection.txt). Their printed types are closed Props: there are no dropped instance arguments or ambient mathematical hypotheses.

The complete project-definition dependency chain was read. With s denoting `shellSpacing u` and k_i denoting `shellRadius u i`, its conventions are:

| Definition | Meaning relevant to this audit | Source |
| --- | --- | --- |
| `Plane`, `supDist` | Integer coordinate pairs; maximum of the two natural absolute coordinate differences. | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) |
| `setDistance` | Infimum in ENat over the subtype of the supplied Set; the empty set has distance infinity. | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:58) |
| `square`, `squareCorners` | Products of inclusive integer intervals and endpoint Finsets, translated by a. The square is always nonempty; corner entries merge at u=0. | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:74) |
| `shellSpacing`, `shellRadius`, `lastShellIndex` | Real sqrt(sqrt(u)); integer floor(i*s); integer floor(s)+1. | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:83) |
| `farVolume`, `shell` | Square filters for distance >(i-1)*s and integer distance =k_i. | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:92) |
| `nearShell` | Shell filtered by sup-distance at most l to the lattice complement of the original square. | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:102) |
| `exceptionalIndices` | Integer Icc 2 (floor(s)+1), filtered by a shell point at corner distance strictly below s/3. | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:112) |
| `geometryThreshold` | Natural fourth power of max(16,6*(l+1)). | [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:119) |
| `ShellSetup` | l>=1, u>=geometryThreshold(l), and the exterior seed has sup-distance exactly one from the square. | [Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:12) |
| `ParallelClearance` | Both coordinate axes and both independent signs; only sides with an actual shell point in the square are tested. Their exterior gaps u+1-delta*(b-a_axis) are at least s/3. | [Specification.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Specification.lean:31) |

Standard-library square-root and floor conventions were checked locally as well: Real.sqrt returns the nonnegative root on these inputs, and Int.floor is the signed floor, including at negative indices. The real divisions in the leaves have fixed nonzero denominators 2 or 3. There are no rational-valued quantities or variable denominators in these statements.

**`ShellScaleStatement` — TRUE; medium.**

Writing s=sqrt(sqrt(u)) and N=max(16,6*(l+1)), u>=N^4 implies s>=N and s^4=u. For s>=16, s^2+4*s/3<u and s^2+s<u/2; floor(s)>s-1>2*s/3. All quantities in these inequalities are real after coercion; the threshold is a natural fourth power. The hypothesis l>=1 is consistent (e.g. l=1,u=16^4).

Two-line proof route:  
Use nonnegativity and the two Real.sq_sqrt identities to obtain s^4=u and transfer the natural threshold to s>=max(16,6*(l+1)).  
Bound the lower-degree polynomials for s>=16 and use Int.sub_one_lt_floor for the strict floor inequality.

Lean traps: The threshold and its fourth power are in N, whereas s and all displayed divisions are in R. Cast the threshold before polynomial reasoning. Real.sqrt is nonnegative; its square identity needs nonnegative input, available from the natural u and the inner square root. The final floor has type Z and is coerced to R for comparison; it is not Nat.floor or integer division.

**`CloseCornerStatement` — TRUE; medium.**

The finite nonempty square and distance-one hypothesis put y on the lattice ring outside it. After translation and a signed coordinate permutation, y=(beta,-u-1) with -u-1<=beta<=u+1. The upper corners have distance 2*u+1, and the two lower corners cannot both have distance <u. For u=0 squareCorners is a singleton Finset (and its close-corner filter is empty), so the omitted positivity assumption is harmless.

Two-line proof route:  
Extract the coordinate description of the distance-one exterior ring from the ENat infimum over square a u; normalize by translation, sign changes, and a coordinate swap.  
Exclude the upper corners and use the separation 2*u between lower corners to apply Finset.card_le_one, handling u=0 separately.

Lean traps: setDistance is an ENat infimum over the Set-coercion of a Finset, not a real metric distance. The square is nonempty even at u=0, and a distance-one witness can be extracted using finite-infimum attainment (or ENat.iInf_eq_natCast_iff). squareCorners is a Finset: its nominal four entries collapse to one at u=0. The point domain Plane=Z*Z has no Fintype instance.

**`ExceptionalLocalizationStatement` — TRUE; medium.**

Exceptional membership itself supplies 2<=i<=floor(s)+1, a shell point x, and a corner c with d_inf(x,c)<s/3. Since s>=0, k_i=floor(i*s)<=s^2+s. The triangle inequality gives d_inf(c,y)<s^2+4*s/3<u, and its reverse form gives |d_inf(c,y)-k_i|<=d_inf(c,x)<s/3. No exterior-seed hypothesis is needed for this leaf.

Two-line proof route:  
Unpack exceptionalIndices and shell, then combine i<=floor(s)+1 with floor(s)<=s and s>=0 to bound k_i<=s^2+s.  
Use the sup-distance triangle and reverse-triangle inequalities to obtain both the close-corner bound and the retained radial error.

Lean traps: Unfold exceptionalIndices before using the index bounds: its Icc endpoints are integers. supDist is natural-valued, the shell equality casts it to Z, and the radial error is an absolute value in R. Use signed or real differences for the reverse triangle inequality. The definition itself supplies shell and corner membership; an exterior-seed premise is unnecessary.

**`RadiusGapStatement` — TRUE; easy.**

For any integers i<j, including negative indices, j>=i+1 and s>=16>0 imply floor(j*s)-floor(i*s)>=floor(s). The strict floor bound floor(s)>s-1>2*s/3 yields the claimed real difference. shellRadius is integer-valued: this subtraction is ordinary signed subtraction after coercion, never truncated natural subtraction.

Two-line proof route:  
Use floor monotonicity and Int.le_floor_add to bound floor(j*s)-floor(i*s) below by floor(s), using j-i>=1.  
Apply Int.sub_one_lt_floor and s>=16 to obtain floor(s)>2*s/3; cast the integer inequality to the real comparison in the statement.

Lean traps: i and j range over all of Z. Monotonicity with nonnegative s and floor superadditivity remain valid for negative indices. Lean prints the conclusion as a difference of two real casts of integer radii, so there is no truncated natural subtraction. All occurrences of division by 3 are real division.

**`ExceptionalCountStatement` — TRUE; easy.**

The first premise forces all close corner witnesses from the second premise to be the same element of squareCorners.filter. If i<j were both exceptional, their radial errors around that corner would give k_j-k_i<2*s/3, contradicting the third premise. All three ingredients are explicit premises; there is no need to assume or invoke another unproved leaf. Finset.card_le_one also handles an empty exceptional set.

Two-line proof route:  
Apply Finset.card_le_one to the exceptional Finset and use Finset.card_le_one on the close-corner filter to identify the two supplied corners.  
For distinct indices order them in Z, add the two strict absolute-value error bounds, and contradict the assumed radius gap.

Lean traps: Convert each witness into membership of the close-corner filter before applying Finset.card_le_one. Order distinct indices in Z, and keep both radial errors and their sum in R. No Fintype instance for Plane or Z is needed; both cardinalities are Finset cardinalities. This leaf assumes the gap/localization facts explicitly, rather than assuming the global ShellSetup.

**`SideCornerWitnessStatement` — TRUE; hard.**

ShellSetup supplies the exterior-ring condition and enough scale to derive s>=16, k_i>=s, and k_i<=s^2+s<u/2. With y=(beta,-u-1), the bottom horizontal side misses the square and the top side has exterior clearances k_i and 2*u+2-k_i. A vertical side can fail clearance only at the exterior half-plane next to its corresponding bottom corner: its lowest shell point has corner distance clearance-1<s/3 and is the required exceptional witness. Both side signs and both exterior signs in ParallelClearance are covered, including beta=+/- (u+1).

Two-line proof route:  
Derive the scale bounds from ShellSetup and normalize the distance-one seed; eliminate horizontal sides and the opposite exterior half-plane of either vertical side.  
For the remaining failed clearance, take the lowest point of that vertical shell side in the physical square and its adjacent bottom corner; their distance is clearance minus one.

Lean traps: Negating ParallelClearance requires classical quantifier reasoning, including the existential that says the side actually meets the square. Both signs epsilon and delta are independent; delta ranges over the two exterior half-planes for each axis. The clearance is the integer u+1-delta*(b-a_axis), subsequently cast to R. Retain the +1 when converting it into a distance to a corner, and derive the scale bounds from ShellSetup rather than treating another leaf as a hypothesis.

**`NearShellCountStatement` — TRUE; hard.**

The setup implies s/3>l. For a point inside the square, distance to its lattice complement is min(u+1-|x_1-a_1|,u+1-|x_2-a_2|). Every shell point lies on at least one of its four radius-k_i sides, and ParallelClearance excludes near-layer strips parallel to that side. Each of the two perpendicular exterior strips intersects that side in at most l integer sites, giving at most 4*2*l=8*l after allowing corner repetitions. The complement is a Set of physical lattice points; counting an l+1-wide strip would be an off-by-one error.

Two-line proof route:  
Express the exterior distance of an interior square point as the minimum of its four integer side gaps, and use s/3>l with ParallelClearance to exclude parallel strips.  
Cover nearShell by the eight perpendicular side-strip intersections; count each integer interval by at most l and apply a finite-union cardinality bound.

Lean traps: nearShell uses the ambient sup-distance to the complement of the original square as a Set, with a bound in ENat. For an interior point the nearest exterior lattice sites are one step beyond an edge, so a width-l strip contains l integer coordinate values. Use finite interval counts and a union bound, allowing shared shell corners to be counted repeatedly; do not enumerate the infinite Plane with Fintype. Classical decidability is available for real and Set membership filters.

**`ShellInclusionStatement` — TRUE; easy.**

For s>=2, floor(i*s)>i*s-1>(i-1)*s. Hence every shell member has exactly the radius required to pass the strict farVolume filter and already belongs to the physical square. Neither an upper trial-index bound nor an exterior-seed premise is needed. All index arithmetic is signed integer or real arithmetic, with the distance cast through Z to R; empty shells give ordinary subset cases rather than global vacuity.

Two-line proof route:  
Use Int.sub_one_lt_floor and s>=2 to get floor(i*s)>(i-1)*s, keeping the real and integer casts explicit.  
Unpack shell membership to retain square membership and rewrite its distance equality, then apply the defining farVolume filter.

Lean traps: shell uses a Z-valued floor equality, while farVolume compares a real threshold with the natural distance coerced to R. Rewrite via explicit casts and keep (i-1) in signed or real arithmetic. farVolume has a strict comparison, but the strict floor lower bound and s>=2 provide sufficient margin. No upper index bound or exterior-site assumption is required.

**Nonvacuity and boundary cases.** Take l=1, u=16^4=65536, a=(0,0). The seed y=(0,-65537) satisfies ShellSetup, and i=2 has shell radius 32 and parallel clearance. For the seed y=(-65504,-65537), the same shell has a left side at x=-65536, exterior clearance 1<16/3, and contains the lower left corner (-65536,-65536); hence the failed-clearance antecedent and exceptional-index conclusion are both realized. RadiusGap has consistent premises at this u for all signed indices, and ExceptionalCount can therefore have all three premises satisfied with a nonempty exceptional set. At u=0 the CloseCorner filter is empty and corner duplication is handled by the Finset definition. Empty shells in some other parameter cases are ordinary cases of true universal statements.

**Validation.** [Inspect.lean](/home/ubuntu/aklt/reports/TS_WIN_01/checks/Inspect.lean) imported the existing compiled statement module and completed with exit code 0 using Lean 4.35.0-rc2. It contains only printing commands and three concrete Finset evaluations; no proofs were written. The real coercions, independent signs, Fin 2 axis quantifier, and closedness of all eight Props agree with the source.

[check_geometry.py](/home/ubuntu/aklt/reports/TS_WIN_01/checks/check_geometry.py) completed with `PASS`; [geometry-results.json](/home/ubuntu/aklt/reports/TS_WIN_01/checks/geometry-results.json) records the counts. It uses exact integer fourth roots and fourth-power comparisons, with no floating-point floors or root comparisons. The interval model was cross-checked against explicit small shell sets, near sets, and exterior distances. Checks included 13,776 exterior-ring close-corner configurations, 46,700 arbitrary-seed localization configurations, 3,015 adjacent radius gaps at negative and positive indices, 25,056 side-witness configurations, 41,352 near-shell counts satisfying clearance, and 90 complete exceptional-index ranges. Sample volumes included exact fourth powers and their immediate neighbors, the minimal geometry threshold, and 390^4 for l=64. The inclusion checks also used u=16 and indices up to 1,000,000, consistent with that leaf's weaker hypotheses.

These finite checks support the mathematical assessment; they do not certify the universal leaves. Difficulty estimates concern Lean implementation. The main work is coordinate normalization and finite geometric counting, both of which follow from the definitions and the stated hypotheses. No sub-agents were launched and no repository files were modified. All generated files and the package symlink are in this report directory; the symlink targets the existing read-only package directory.
