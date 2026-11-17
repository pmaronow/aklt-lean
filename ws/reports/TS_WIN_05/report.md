STATUS: COMPLETE

| Leaf in `AKLT.Blueprint.Win` | Verdict | Difficulty |
|---|---|---|
| `RadialPathsStatement` | TRUE | medium |
| `SquareExteriorStatement` | TRUE | medium |
| `ComplementEscapeStatement` | TRUE | hard |
| `WindowBufferStatement` | TRUE | medium |
| `RawRangeStatement` | TRUE | easy |
| `RawDistanceObstructionsStatement` | TRUE | medium |
| `RawDepthArithmeticStatement` | TRUE | easy |
| `RawHeightStatement` | TRUE | easy |

All eight statements are true as written and self-sufficient. No missing premise or statement correction was found. This is a truth audit with proof routes; no Lean proofs were written.

**Sources and definition closure.** Reviewed repository `main` at commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The exact statements are in [NodesTaper.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:24). The paper argument is [sec5-window.tex, Lemma l:cutgeom](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:359), especially lines 419–572. Read the following definition chains rather than relying on the statement docstrings:

| Definition source | Definitions inspected |
|---|---|
| [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:12) | `ShellSetup`, `CutSetup`, `StarAdjacent`, `JoinedIn`, `ConnectedIn`, `starBall`, `rawBoundary`, `squareDepth`, `radialOffset`, `taper`, `core`, `cutVolume`, `cutRaw`, `NoBond`. |
| [Geometry.lean: lattice and distance](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) | `Plane`, `latticeDist`, `supDist`, `Adjacent`, `setDistance`, `boundaryDepth`. |
| [Geometry.lean: square and shells](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:74) | `square`, `squareCorners`, `shellSpacing`, `shellRadius`, `lastShellIndex`, `farVolume`, `shell`, `nearShell`, `window`, `exceptionalIndices`, `geometryThreshold`. |
| [Mathlib ENat](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Data/ENat/Basic.lean:117), [ENat infima](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Data/ENat/Lattice.lean:66), [relation closure](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Logic/Relation.lean:386) | `ENat.toNat`, finite natural-valued infima, and `Relation.ReflTransGen`, including its unrestricted reflexive constructor. |

Use `C = square a u`, `s = shellSpacing u`, `k = shellRadius u i`, `T = s/12`, `rho(z) = supDist z y`, `h = squareDepth a u`, `t = radialOffset y u i`, `U = taper a y u i`, `F = farVolume a y u i`, `B = window a y u 64 i`, and `G = cutVolume a y u i`. The definitions give exactly the paper's integer geometry: `h = max(0,u+1-supDist(z,a))`, `t = |rho-k|`, and `U = {t <= T, h >= 32+t}`. Positive `h` already forces membership in `C`.

**Self-sufficiency and nonvacuity.** `CutSetup` contains the exterior-seed hypothesis and `u >= geometryThreshold 64 = 390^4`. Consequently `s >= 390`, `u = s^4`, and `k = floor(i*s)` with `2 <= i <= s`. The scale estimates used in the routes, including `k-T-1 > (i-1)*s` and `u+1-T > 32`, follow from these hypotheses. They do not require assuming the separate, open `CutScalesStatement`. Likewise, finite boundary depth follows from the definitions, without assuming the separate, open `FiniteDepthStatement`.

The setup is consistent: take `a=(0,0)`, `u=390^4`, `y=(0,-u-1)`, and `i=2`. Then `s=390`, `k=780`, and no shell site is within `130` of a square corner, since its first coordinate has absolute value at most `780`. The site `(0,-u+779)` belongs to the core and window. The site `(0,-u+812)` is raw: its offset is `33 > T=32.5`, and its vertical neighbour of offset `32` lies in `U`. Thus neither the setup nor the raw-site quantifiers are vacuous. The real arithmetic premises are consistent as well, for example at `(s,t,h,b)=(390,0,30,30)`.

**RadialPathsStatement — TRUE; medium.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:25); paper lines 441–461. The radial offset is a natural absolute difference. From a tapered site, an inward star-step when rho>k or an outward nearest-neighbour step when rho<k reduces it by exactly one; squareDepth drops by at most one, so both taper inequalities persist until the offset is zero. All scale and exterior-seed facts needed here follow from CutSetup.

1. Induct on radialOffset; construct the appropriate lattice step and preserve t <= s/12 and h-t >= 32.
2. At offset zero the endpoint belongs to core; compose the steps using Relation.ReflTransGen.

Lean traps: Moving only one of two tied maximal coordinates inward need not reduce `rho`; move all tied maxima. Star adjacency permits that diagonal step. At offset zero use reflexivity.

**SquareExteriorStatement — TRUE; medium.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:31); paper lines 488–494. The complement of every finite translated integer square is nonempty and nearest-neighbour connected, including radius zero. Coordinate paths connect every exterior point to the common exterior row a.2+u+1.

1. Give an exterior witness, and connect each exterior site to (a.1+u+1,a.2+u+1) by coordinate segments remaining outside the square.
2. Reverse one path and concatenate in JoinedIn to obtain the required pairwise connectivity.

Lean traps: `ConnectedIn` includes `S.Nonempty`; pairwise connectivity alone does not finish the leaf. The common exterior point supplies that witness. The case `u=0` is valid, and all square endpoints are integers after casting `u`.

**ComplementEscapeStatement — TRUE; hard.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:35); paper lines 494–512. CutSetup makes y an exterior site and gives u large enough to exclude the square centre from the shallow-depth case. The three paper cases admit nearest-neighbour escape paths: rho>k+T, rho<k-T, or h-t<32. The first two preserve radial failure, and in the third h-t cannot increase along a coordinate ray away from a.

1. Use a reflexive path if already exterior; otherwise split into the two radial failures and the shallow-depth failure.
2. Use an outward ray from y, an inward path toward exterior y, or an outward ray from a, and concatenate the finite nearest-neighbour steps.

Lean traps: The conclusion uses nearest-neighbour adjacency, which the paper’s three constructions provide. Inward steps can leave `rho` unchanged when maxima tie; use decreasing lattice distance to `y` for termination. In the shallow-depth case `z=a` is excluded by `u+1-T>32`; an outward maximal-coordinate ray then decreases `h` exactly one per step inside `C`. Boundedness gives finite exit times for outward rays.

**WindowBufferStatement — TRUE; medium.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:41); paper lines 514–529. Window sites have t=0 and integer depth h>=65, so their nearest neighbours have t<=1 and h>=64. A taper site and every star neighbour have h>=31 and rho>=k-s/12-1>(i-1)s. These consequences of CutSetup give the far-volume buffer, and every raw-boundary point is outside the window because it is outside the taper.

1. Derive s>=390 and the strict clearance k-s/12-1>(i-1)s from the threshold and floor bound; use one-Lipschitz h and t.
2. Convert window depth >64 to h>=65; obtain all four buffer assertions, then use the star-neighbour witness and raw exclusion to get cutRaw subset cutVolume.

Lean traps: The window removes depth **at most** `64`, leaving integer depth at least `65`. A raw witness can be diagonal, so the last inclusion needs the bounds for star neighbours; `NoBond` itself concerns nearest neighbours. The same inequalities establish the stronger star-neighbour bounds.

**RawRangeStatement — TRUE; easy.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:50); paper lines 523–558. A raw point x is outside the taper and has a taper witness v at sup-distance one. Thus t(x)<=s/12+1, h(x)>=31 and h(x)>=30+t(x). If t(x)<=s/12, the square filter already holds, so failure of taper membership forces h(x)<32+t(x).

1. Unpack rawBoundary to get v in taper with supDist x v=1; transfer the two taper bounds using Lipschitz estimates.
2. In the near case, use h(x)>0 for square membership and negate the remaining taper inequality to obtain the strict upper height bound.

Lean traps: `starBall` includes its centre, but `rawBoundary` subtracts `U`, so the witness has distance exactly one. The height inequalities here are in `ℤ`, while the range comparison is in `ℝ`. Establish positive height before using failure of the taper filter to obtain its strict upper bound.

**RawDistanceObstructionsStatement — TRUE; medium.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:59); paper lines 531–548. For G=F\B, its exterior is B union C^c union (C\F). Lipschitz bounds give sup-distance obstructions max(t,65-h), h, and s-1-t respectively, and lattice distance dominates sup-distance. The use of ENat.toNat is safe: G is a Finset contained in the square, so an explicit square-exterior site gives finite boundaryDepth. No additional finite-depth premise is needed.

1. Bound the lattice distance from x to each of the three parts of G^c, using window depth >=65 and k>=(i*s)-1.
2. Take the infimum; use an exterior-square witness to show boundaryDepth is finite before converting its value with ENat.toNat.

Lean traps: `ENat.toNat top = 0`; conversion must follow finiteness. The site `(a.1+u+1,a.2)` is outside `G`, so it supplies a finite upper bound for `boundaryDepth G x`. Empty `B` or `C \ F` would make that individual set-distance infinite and causes no failure of the obstruction argument.

**RawDepthArithmeticStatement — TRUE; easy.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:68); paper lines 550–572. The displayed hypotheses suffice over all real s,t,h,b; integrality is unnecessary. In the near case each obstruction is at least max(t,16)-2 and at least 14. In the far case the global premise h>=30+t and t<=s/12+1 make each obstruction at least s/12-1>=31.5. Thus the minimum lower bounds transfer to b.

1. Split t<=s/12 from t>s/12, and bound all three entries of the minimum below by the requested case bound.
2. Use h<32+t in the near case and the unconditional h>=30+t in the far case; combine with s>=390 and the given minimum<=b.

Lean traps: `max t 16 - 2` is real subtraction, not truncated natural subtraction. The separate, unconditional premise `30+t<=h` is present and supplies the far-case height control. Division by `12` is real division by a nonzero constant. No integrality premise is required.

**RawHeightStatement — TRUE; easy.** [Statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTaper.lean:77); paper lines 523–525 and 563–565. For a raw point x with star-neighbour v in the taper, h(x)>=h(v)-1>=31+t(v)>=30+t(x). This is unconditional in t(x); it does not depend on the near-range premise.

1. Choose the taper witness in rawBoundary and establish the one-step Lipschitz bounds for squareDepth and radialOffset.
2. Combine h(v)>=32+t(v), h(x)>=h(v)-1, and t(v)>=t(x)-1 in integer arithmetic.

Lean traps: Avoid subtracting one from natural `radialOffset` before casting. Keep the estimates as additive inequalities or move them to `ℤ` first. This bound is unconditional in the offset; the near-range premise is unnecessary.

**Other Lean checks.** These are closed propositions with concrete `Plane = ℤ × ℤ`; no instance hypothesis is silently dropped. `Plane` is infinite and needs no `Fintype` instance: squares, tapers, and raw boundaries are explicit `Finset`s, whereas the exterior is a `Set`. The real-valued filters are defined under `classical`; a writer can use `classical` when unfolding membership without adding a premise. `shellSpacing` has no integer rounding, and `shellRadius` uses integer floor. Keep natural offsets, integer heights/radii, real comparisons, and extended-natural distances distinct. `JoinedIn` reflexivity does not itself assert endpoint membership; the leaves supply the necessary membership separately.

**Validation.** [scratch/audit_checks.py](/home/ubuntu/aklt/reports/TS_WIN_05/scratch/audit_checks.py) passed; [checks.json](/home/ubuntu/aklt/reports/TS_WIN_05/scratch/checks.json) records the counts. It checks 150 exact rational arithmetic samples, including fractional offsets and heights, and 96 admissible translated geometries at `u=390^4`, `390^4+1`, `391^4-1`, and `396^4`, with indices `2`, `3`, and `floor(s)`. Those geometry samples include 4,968 taper sites, 7,344 raw sites (4,032 near and 3,312 far), and 552 window sites. Fourth-root floors and comparisons use exact integer arithmetic, and boundary depths are computed from distances to the exterior, the inner closed square, and clipped window segments. These finite checks support the definition review and paper routes; they are not exhaustive or kernel-checked proofs. No Lean process or sub-agent was launched, and no repository file was modified.
