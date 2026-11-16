STATUS: PASS
BLOCKING: 0

References below use the supplied paper directory, `lean/AKLT/Defs/`, and the permitted Mathlib source tree. All five declarations are in `Pattern.lean`. I read that entire file and its local import chain: `Trails.lean`, `Domain.lean`, `PinModel.lean`, `Moment.lean`, and `Geometry.lean`. The judgments concern only the five assigned declarations.

DECL: templateSites PASS

Paper: `sec6-walks.tex:488–492` (Definition `d:pattern`) defines the template as all plane sites with ambient taxicab distance at most two. The ambient distance convention is explicit in `sec2-moments.tex:20–21`.

Lean: `Pattern.lean:9`, using `Geometry.lean:8–11,74–76`, denotes exactly
`{(a,b) ∈ ℤ × ℤ : |a| + |b| ≤ 2}`. `square (0,0) 2` is the product of the two inclusive integer intervals `[-2,2]`. Filtering it does not truncate the intended ball: every site of taxicab distance at most two already lies in that square. The result consists of the passage site, its four neighbours, the four corners, and the four tips: thirteen distinct sites.

Mathlib meanings checked: `Finset.Icc` includes both endpoints (`Mathlib/Order/Interval/Finset/Defs.lean:280,301`; the integer instance is `Mathlib/Data/Int/Interval.lean:29–44`); `Finset.product` is Cartesian product (`Mathlib/Data/Finset/Prod.lean:46–61`); `Finset.filter` means membership in the original finset together with the predicate (`Mathlib/Data/Finset/Filter.lean:52,127`). `Int.natAbs` is integer absolute value with a natural result (`Mathlib/Data/Int/NatAbs.lean:14–16,35–39`). Coordinate subtraction and the square's bounds are computed in `ℤ`, before taking absolute values. There is no truncated natural subtraction, periodic quotient, or division here.

DECL: templateTips PASS

Paper: `sec6-walks.tex:492` specifies `(±2,0),(0,±2)`; their covering status and special bond rule are at `sec6-walks.tex:506–509`.

Lean: `Pattern.lean:12` lists precisely these four distinct integer points, all belonging to `templateSites`. In a `Finset`, literal braces denote successive insertions and a singleton, so ordering is immaterial and repetition would not introduce multiplicity (`Mathlib/Data/Finset/Insert.lean:66–74,348–365`). The negative coordinates are integer negatives. This declaration supplies the geometric sites; `Covered` supplies their U status, and `bonds` uses exactly the non-tip endpoint's keep decision for a tip bond (`Pattern.lean:54,60–64`). Thus using these sites as covering tips does not impose an unintended global tip consistency condition.

DECL: templateCorners PASS

Paper: `sec6-walks.tex:492–494` specifies the four independent-sign points `(±1,±1)` and two external slots at each corner.

Lean: `Pattern.lean:15` lists all four sign combinations exactly once. These are four distinct sites in the radius-two taxicab template, disjoint from the tips and nearest neighbours. The same `Finset` insertion/singleton meanings checked above apply; there is no ordering or multiplicity requirement. The two slots per corner are represented by `externalSlot`, and their use is independent of the corner's external kept directions (`Pattern.lean:85–87`), as required at `sec6-walks.tex:510–512`.

DECL: externalSlot PASS

Paper: `sec6-walks.tex:493–494,510–512` requires the two outward bonds at every corner and the three outward bonds at every tip, giving twenty separately assigned slots.

Lean: `Pattern.lean:18–24` is a bijective enumeration of those site/direction pairs. With `Compass.step` as defined in `Geometry.lean:25–29`, its entries are:

| Zero-based indices | Site | Directions in order |
| --- | --- | --- |
| 0–1 | `(1,1)` | E, N |
| 2–3 | `(-1,1)` | N, W |
| 4–5 | `(-1,-1)` | W, S |
| 6–7 | `(1,-1)` | S, E |
| 8–10 | `(2,0)` | E, N, S |
| 11–13 | `(0,2)` | E, N, W |
| 14–16 | `(-2,0)` | N, W, S |
| 17–19 | `(0,-2)` | E, W, S |

For every entry `(x,d)`, `x + d.step` lies outside the template. Conversely every nearest-neighbour bond from the template to its complement appears exactly once. Distinct slots can share an outside endpoint; the site/direction pairs remain distinct, so their fields are independent. No inward bond is included.

Mathlib meanings checked: `![...]` constructs a function on a finite index type by successive `Matrix.vecCons` operations, with the first entry at zero and successive entries at successive indices (`Mathlib/Data/Fin/VecNotation.lean:53–76,128–140`). Thus the domain is exactly the twenty indices 0 through 19, without a default or omitted entry. Pair addition is coordinatewise (`Mathlib/Algebra/Notation/Prod.lean`, `Prod.instMul` and its generated additive counterpart). The paper fixes no slot order, so this ordering adds no mathematical restriction. The consumers use one independent `m j` for each index and retain all slots at every nonremoved site (`Pattern.lean:76,85–87`).

DECL: PatternData PASS

Paper: `sec6-walks.tex:495–518` specifies an out-neighbour and local status/kept-set data, subject to the covered-pattern rules. `PatternData` (`Pattern.lean:27–30`) is the auxiliary raw carrier; the mathematical class is represented by `π : PatternData` together with `π.Covered`, not by the carrier alone.

The field types are appropriate. `Compass` has exactly E,N,W,S (`Geometry.lean:17–22`), and `Status` has exactly U,D,X (`Moment.lean:50–54`). Coercing `templateSites` to a type gives the subtype of plane points belonging to that finset, so each field assigns data to exactly thirteen sites (`Mathlib/Data/Finset/Defs.lean:101–105,159–180`). Membership proofs do not create additional sites. `Finset Compass` represents any subset of the four incident directions, including external directions at corners and tips. In `keptAt`, the image under `d ↦ x + d.step` converts these directions to neighbouring sites (`Pattern.lean:37–38`; `Mathlib/Data/Finset/Image.lean:279–294`). That map is injective, so a two-element kept set really means two distinct incident bonds.

I checked the carrier against its defining predicate and consumers:

- `Covered` excludes south as outgoing and requires its endpoint to be nonremoved. Since there are exactly four compass constructors, this is precisely the paper's marked E,N,W neighbour. The passage is U with exactly E,N,W kept (`Pattern.lean:42–49`; paper `sec6-walks.tex:495–501`).
- The arrival is X or D with two kept bonds excluding the passage. Each other neighbour is U, X, or D with two kept bonds including the passage. Corners are U, X, or D with two kept bonds; all non-tip U sites other than the passage keep all four directions (`Pattern.lean:44–53`; paper `sec6-walks.tex:498–505`). There are respectively four, five, and eight meaningful local choices, as also described in `sec8-inputs.tex:33–38`.
- Tips are U. Mutual keep decisions are required only between adjacent, nonremoved, non-tip sites. Present tip bonds ignore the tip's own kept field and depend on the other endpoint (`Pattern.lean:54–64`; paper `sec6-walks.tex:505–509`). No condition from an ambient volume, boundary, or protected layer is added to this local carrier.
- Removed-site kept fields and tip kept fields are inert. Normalizing them to empty sets at X sites and all four directions at tips preserves coveredness, active sites, present bonds, outgoing type, and both local functionals. Every paper pattern has such a representative; every covered raw datum represents a paper pattern. These extra encodings therefore neither enlarge nor restrict the mathematical pattern class used by the statements.
- `LocalPatternBound` and the headline local inequality quantify over raw data with the explicit `π.Covered` premise (`Pattern.lean:100`; `lean/AKLT/Blueprint/Top/Response.lean:14–15`). The network-matching consumer likewise requires a covered witness and matches kept sets only at nonremoved non-tip sites (`Response.lean:69–75`). Invalid raw data are not silently admitted as patterns.

Finiteness introduces no extra hypothesis: finset subtypes have their own finite enumeration (`Mathlib/Data/Fintype/Sets.lean:226–249`), subsets of a four-element type are finite (`Mathlib/Data/Fintype/Powerset.lean:22–27`), and functions between finite types are finite (`Mathlib/Data/Fintype/Pi.lean:134–137`). The universal quantifier over `PatternData` does not require a separately supplied `Fintype PatternData` instance. There is no scalar trace-mass field or hidden division in the carrier.

Non-blocking remarks:

- A Python check of the literal site/slot lists confirmed thirteen template sites, four tips, four corners, and exactly twenty distinct outward slots with no missing or extra pair. An independent enumeration of the covered local choices, after normalizing inert fields, gave 106101 consistent assignments, 184914 assignments marked by an E/N/W out-neighbour, and 123339 marked by N/E. These agree with `sec8-inputs.tex:46–50` and rule out an empty covered class. For an explicit witness of each outgoing type, take arrival X, all other sites U, passage kept E,N,W, and all other kept sets full.
- The carrier contains redundant raw encodings because X-site and tip kept sets are unused. Its literal cardinality should not be identified with the paper's canonical enumeration counts; this has no effect on the reviewed semantics.
- The imported partition ratios, natural-index subtractions, and inverses do not enter these five definitions. The geometric square uses integer subtraction. The template, compass, status, and slot index types are nonempty; a covered pattern also always has an active passage site and four active tips. No Lean process was launched; the findings use source inspection and the finite Python checks. Inputs were not modified.
