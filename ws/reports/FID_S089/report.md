STATUS: PASS
BLOCKING: 0

DECL: wordStraight PASS

`AKLT/Defs/Trails.lean:43–44` agrees with the straight/turn rule in Definition `d:weights`, `paper/sec6-walks.tex:661–669`. The paper calls a departure straight precisely when its outgoing displacement equals its incoming displacement; the incoming displacement is the designated direction at index zero and `v_i - v_{i-1}` thereafter.

`DirectionWord n` is `Fin n → Compass`. The four constructors have distinct steps `(1,0)`, `(0,1)`, `(-1,0)`, `(0,-1)` (`Geometry.lean:17–29`), so equality of compass labels is exactly equality of these displacements. `wordVertex` is the actual prefix sum in `ℤ × ℤ`, with componentwise addition (Mathlib `Algebra/Notation/Prod.lean:33–35,65–76`, including the generated additive instances). Thus the previous word letter is the paper's incoming displacement, without a sign reversal. `wordIncoming` (`Trails.lean:39–40`) returns `incoming` at zero; only in its nonzero branch does it use `i.val - 1`. Natural subtraction cannot truncate there: `i.val ≠ 0` implies `1 ≤ i.val`, and the predecessor is a valid index below `n`. `Bool.decide_iff` (Mathlib `Data/Bool/Basic.lean:71`) makes the returned Boolean true exactly for the stated equality. The `Fin n` argument excludes the terminal arrival and supplies no departure when `n = 0`. Reversal is excluded separately by the trail predicate, as in the paper; it is not an additional straight case on valid trails.

DECL: departureCount PASS

This auxiliary definition (`Trails.lean:47–48`) represents exactly the previous-departure count needed by `d:weights` (`paper/sec6-walks.tex:661–662`) and the dead-neighbour rule in `d:kernel` (`paper/sec7-recursion.tex:521–525`). Its value is

`#{j : ℕ | j < min i n and v_j = x}`.

Mathlib `Data/Finset/Range.lean:52–65` gives `j ∈ range k ↔ j < k`; `Data/Finset/Filter.lean:127–128` gives the conjunction with the filtering predicate; `Data/Finset/Card.lean:47–48` counts the resulting indices. Consequently repeated departures from one site count separately, rather than being collapsed into one visited vertex. For `i ≤ n`, the count is precisely over `0 ≤ j < i`. In particular, at a departure `i : Fin n`, `min i.val n = i.val`, so neither the current departure nor any future departure is included.

At `i = n` it counts all existing departures `0,…,n-1` and excludes the endpoint `v_n`. This is also the correct auxiliary object for `Automaton.windowKind` (`Automaton.lean:42–44`): the paper tests whether `z_m` equals a vertex in `{z_0,…,z_{m-1}}` (`paper/app-input-contracts.tex:20–32`). `deadAt` uses the actual multiplicity to test two previous departures (`Kernel.lean:20–22`). For `i > n`, the clamp counts only the word's actual departures, avoiding fictitious repetitions of the clamped endpoint. No finiteness assumption on the infinite plane is required: the counted set consists of finitely many natural indices.

DECL: wordRevisit PASS

`Trails.lean:51–52` is true exactly when there exists `j < i.val` with `v_j = v_i`. This follows from the preceding count interpretation, Mathlib `Finset.card_pos` (`Data/Finset/Card.lean:78`), and `Bool.decide_iff` (`Data/Bool/Basic.lean:71`). It is exactly the earlier-departure criterion in Definition `d:weights`, `paper/sec6-walks.tex:661–662`, reiterated at `paper/sec7-recursion.tex:521` and `paper/app-input-contracts.tex:8–10`.

The first departure is always a first visit because its count is zero. The virtual incoming direction creates no counted departure. A terminal arrival receives no revisit factor, since it is outside `Fin n`; if a later extension departs from that site, all earlier actual departures are then considered. A return to the start is correctly detected through index zero. The definition depends on the full word prefix, with neither a memory cutoff nor a spatial quotient. There is no network-status test that could incorrectly classify an initially `D` site as a lattice revisit.

DECL: trailWeight PASS

`Trails.lean:55–56` is the product specified by Definition `d:weights`, `paper/sec6-walks.tex:655–665`. A revisit contributes exactly `1/5`, regardless of its direction. Every other departure contributes `x_s/3` or `x_t/3` according to the checked straightness rule. `passageFactor` is the reciprocal of `localThreshold`, hence gives `1000/961` and `200/187`, matching the fixed thresholds at `paper/sec6-walks.tex:538–539` and the reciprocals at `paper/app-input-contracts.tex:3–5`.

The return type forces both conditional branches, the division operations, and the product into `ℚ`. These are exact rational fractions, not natural-number division. Mathlib `Data/Rat/Defs.lean:122–130` supplies ordinary rational inversion and division. Every denominator here is nonzero: `3`, `5`, and both fixed thresholds are positive. Thus totalized division at zero cannot alter any value. Mathlib's bare `∏ i` means `Finset.prod Finset.univ` (`Algebra/BigOperators/Group/Finset/Defs.lean:183–190`); here the inferred index type is `Fin n`, so there are exactly `n` factors. At `n = 0`, `Fintype.prod_empty` in the same file (`:753–754`) gives `1`, as the paper requires. Casting this rational weight to `ℝ` in `OpenTrailBound` preserves its arithmetic (Mathlib `Data/Rat/Cast/CharZero.lean:63–64`).

The weight is total on direction words; admissibility is enforced by `IsTrail` at its trail-sum uses (`Trails.lean:35–36,68–69`; `Computational.lean:9–11`; `Automaton.lean:63–66`). Its injective unordered endpoint pairs impose distinct unoriented bonds, and its initial nonreversal clause is conditional on an actual first index. The virtual incoming bond is not inserted into the used-bond set, so a later traversal of it remains possible, as required by `paper/sec6-walks.tex:657–660`. These domains introduce no missing or extra trail restriction.

DECL: trailBaseWeight PASS

`Trails.lean:59–60` is exactly the coefficient `3^{-n}(3/5)^{rev(w)}` in Definition `d:kernel`, `paper/sec7-recursion.tex:540–551`, and the finite H3 sum at `:598–603`. With `r` the number of revisit departure indices, its finite rational product is

`(1/3)^(n-r) * (1/5)^r = (1/3)^n * (3/5)^r`.

Here `0 ≤ r ≤ n` because revisits form a subset of `Fin n`; any displayed `n-r` is therefore nontruncating. The Lean definition itself uses neither subtraction nor negative natural powers. As for `trailWeight`, all factors are exact rational numbers, the denominators are nonzero, and the empty product is `1`.

This is the correct coefficient before exposure products: `closedContribution` and `kernelLengthCoefficient` multiply it by the separate exposure sum (`Kernel.lean:95–108`), whose indices are first departures (`:72–74,89–93`). No passage factor has been accidentally included at a revisit or counted twice in the base. Multiplying the base by the passage factors at all first departures recovers `trailWeight`, precisely the identity at `paper/sec7-recursion.tex:654–656`. The base does not need a designated incoming direction: it depends only on revisit counts; direction-dependent factors belong in the exposure product.

Non-blocking remarks:

- Read the complete target file and its local import chain `Domain → PinModel → Moment → Geometry`, and inspected the relevant downstream kernel, automaton, computational definitions and interfaces. The plane is `ℤ × ℤ`, with no quotient. `Compass` explicitly enumerates all four directions; the standard finite-function instance (Mathlib `Data/Fintype/Pi.lean:133–136`) makes direction words finitely enumerable without restricting their contents. No additional hypothesis or instance parameter changes the five declarations' domains.
- `trailBaseWeight` is the lattice kernel coefficient, not the evolving-network coefficient for every possible initial status assignment. The paper explicitly distinguishes these when an initially `D` site has its first lattice departure (`paper/sec7-recursion.tex:819–831`); the current definition and its uses respect that distinction.
- An independent Python comparison using sequential vertices and exact fractions checked all 4,180 admissible trail/incoming-direction cases of lengths zero through six at the fixed start `(3,-2)` against the displayed Lean formulas. Checks included clamped count indices beyond the endpoint, empty products, a square ending at the start without a terminal departure factor, and `E,N,W,S,W` with incoming `E`, which later uses the virtual incoming bond and has one revisit factor. This was a semantic sanity check, not Lean execution; no Lean compilation was performed. No inputs were modified.
