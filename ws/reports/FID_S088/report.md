STATUS: PASS
BLOCKING: 0

DECL: DirectionWord PASS

`AKLT/Defs/Trails.lean:24` represents exactly a length-`n` sequence of absolute lattice directions. The paper defines a trail by its nearest-neighbour vertex sequence in `paper/sec6-walks.tex:655–672`; the equivalent direction alphabet is explicit in `paper/app-input-contracts.tex:20–33`, with all positions in ℤ² (`:9–10`). In `AKLT/Defs/Geometry.lean:8,17–36`, `Plane` is ℤ × ℤ, and `Compass.step` bijectively assigns east, north, west, south to (1,0), (0,1), (−1,0), (0,−1). Thus a word and a specified start uniquely determine the paper's vertex sequence, and conversely. There is no spatial or symmetry quotient and no unintended restriction on words before the trail predicate is imposed.

Mathlib meaning checked: `Fin n` indexes exactly the naturals below `n` (`Mathlib/Data/Fin/Basic.lean:38–48`); equality ignores the bound proof (`:118–125`). The finite function instance enumerates all functions, without identifying different words (`Mathlib/Data/Fintype/Pi.lean:28–45,133–143`). Consequently there are 4^n words, including exactly one empty word at `n = 0`.

DECL: wordVertex PASS

`AKLT/Defs/Trails.lean:27–28` is the correct auxiliary vertex map for the vertex sequence in `paper/sec6-walks.tex:657–669` and the cumulative-displacement formula in `paper/app-input-contracts.tex:24–26`. For `0 ≤ j ≤ n`, it gives exactly

`wordVertex u w j = u + Σ_{0 ≤ k < j} (w k).step`.

In particular, the zeroth vertex is `u`, and for every `i : Fin n`, the vertex at `i.val + 1` equals the vertex at `i.val` plus `(w i).step`. Each consecutive displacement is therefore a nonzero nearest-neighbour unit vector.

Mathlib meaning checked: `∑ i : Fin n` sums over all elements of `Fin n`, with excluded summands equal to the additive identity (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:26–31,63–69`). Product addition and zero are coordinatewise (`Mathlib/Algebra/Notation/Prod.lean:33–47,65–82`, through their additive declarations); ℤ² is an additive commutative group, so the unordered finite sum is the same cumulative displacement as the ordered path sum. Both the comparison `i.val < j` and `i.val + 1` use natural numbers, without modular `Fin` arithmetic. For `j ≥ n` the result remains the endpoint. This is a harmless totalization: `wordBond` uses indices at most `n`, and the vertex-list, departure-count, closed-trail and prefix consumers use the intended bounded indices.

DECL: wordBond PASS

`AKLT/Defs/Trails.lean:31–32` gives exactly the departure bond `{v_i, v_{i+1}}` in the distinct-unoriented-bond definition (`paper/sec6-walks.tex:657–660`; also `paper/sec6-walks.tex:50–55`). Since `i.val < n`, both vertex indices are in the actual path. The displacement identity above shows that the endpoints differ, so the finite set always has two elements; no collapsed singleton or loop is possible.

Mathlib meaning checked: `{a,b} : Finset Plane` is an extensional unordered pair, with `{a,b} = {b,a}` (`Mathlib/Data/Finset/Insert.lean:412–420`). Repeating an endpoint would collapse a pair (`:406–407`), but unit compass steps exclude that case. Hence equality of these finite sets is precisely equality of physical unoriented bonds, including traversal in the opposite direction.

DECL: IsTrail PASS

`AKLT/Defs/Trails.lean:35–36` matches Definition `d:weights` exactly (`paper/sec6-walks.tex:655–672`). `Function.Injective (wordBond u w)` says that equal bonds have equal departure indices, equivalently that distinct departures use distinct unoriented bonds. Nearest-neighbour adjacency is already guaranteed by the word representation. The second conjunct excludes exactly `w(0) = incoming.reverse` when `n ≥ 1`; `Compass.reverse.step` is the negative of the original step (`AKLT/Defs/Geometry.lean:25–36`). For positive `n` there is exactly one index with value zero, so the universal implication neither adds nor loses a first-step condition.

Mathlib meaning checked: injectivity is pairwise inequality at distinct indices (`Mathlib/Logic/Pairwise.lean:47–50`), applied here to unordered finite-set bonds, not to vertices. Vertex revisits and closed trails remain allowed. Every later immediate reversal repeats the preceding unoriented bond and is therefore already excluded, as the paper explains at `paper/sec6-walks.tex:668–672`.

The virtual incoming bond is not inserted into the used-bond collection. It can be traversed later, exactly as required by `paper/sec6-walks.tex:659–660` and `paper/app-input-contracts.tex:61–63`. For example, from `(0,0)` with incoming east, the word north, west, south, east is admitted: its final bond is the virtual incoming bond and all four actual bonds are distinct. At `n = 0`, both conjuncts hold over the empty index type, giving the intended empty trail (`paper/sec6-walks.tex:665,684–691`). Arbitrary plane starts and designated directions remain available; finite-network admissibility and stopping conditions are appropriately separate predicates.

DECL: wordIncoming PASS

`AKLT/Defs/Trails.lean:39–40` implements the paper's explicit convention: incoming direction is the designated `a` at departure zero, and `v_i − v_{i−1}` at every later departure (`paper/sec6-walks.tex:668–669`). At `i.val = 0` it returns the designated direction. Otherwise it returns `w(i.val − 1)`, whose step equals that vertex difference by the cumulative-displacement formula.

The subtraction is on ℕ, with its usual truncation, but the else-branch hypothesis implies `1 ≤ i.val`. Thus the predecessor is genuine and satisfies `i.val − 1 < i.val < n`; there is no underflow, wrapping, default direction or additional hypothesis. The `omega` proof supplies only the `Fin n` bound, and the bound proof does not affect the index (`Mathlib/Data/Fin/Basic.lean:124–125`). At length zero no departure index exists.

The sign convention also agrees with its consumers: `wordStraight` compares outgoing and incoming directions directly (`AKLT/Defs/Trails.lean:43–44`), while `responseNeighbours` removes `v_i − incoming.step`, the arrival site (`AKLT/Defs/Kernel.lean:25–27`). At the canonical kernel start, incoming west equals `u − c`, and subtracting its step recovers the centre, as specified in `paper/sec7-recursion.tex:516–524`.

Non-blocking remarks:

- Read `Trails.lean` and its complete AKLT import chain (`Domain.lean`, `PinModel.lean`, `Moment.lean`, `Geometry.lean`) in full; inspected the relevant consumers and Mathlib operations cited above. Judgments are restricted to the five assigned declarations.
- These declarations contain no division, infinite sums, finiteness assumptions on the plane, or hidden network-instance hypotheses. Their finite indices and the explicit four-element `Compass` instance provide the required word enumeration. The unbounded natural argument of `wordVertex` is intentional endpoint clamping, not an additional mathematical restriction.
- No blocking discrepancies or requested changes. This was a source-level semantic review; no Lean processes were launched and no inputs were modified.
