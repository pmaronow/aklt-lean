STATUS: PASS
BLOCKING: 0

DECL: destinations_10 PASS

This is an auxiliary fragment of the successor table for Proposition `p:automaton10`, whose class-row format is specified in `paper/app-input-contracts.tex:382–388` and whose reconstruction obligations are at `paper/app-input-contracts.tex:402–417`. It has no separate mathematical counterpart in the paper. At `lean/AKLT/Defs/Automaton10Data.lean:1585`, it is the low 15,704 bits of the packed successor table. I regenerated successor rows from the supplied representatives, lattice bonds, and raw-to-class map, and checked equality of the entire fragment with the corresponding bits of those regenerated rows.

The representation stores successor class `b` as the natural number `b + 1`, reserving zero for the paper's inadmissible sentinel `-1`. The fragment contains 1,308 complete 12-bit lanes and the low eight bits of lane 1,308 (class 327, direction E). That lane regenerates to 704; its remaining four bits come from `destinations_9`. This split reconstructs the correct value. These are exact `ℕ` literals, with no machine-word overflow or signed interpretation.

DECL: destinations PASS

The assembled integer at `lean/AKLT/Defs/Automaton10Data.lean:1587`, decoded by `destinationCode` at lines 1615–1616, supplies exactly the successor component of the rows in `paper/app-input-contracts.tex:385–388`. Its eleven fragments occupy successive, disjoint bit ranges. Mathlib's `Nat.shiftLeft_eq_mul_pow` (`Mathlib/Data/Nat/Size.lean:18`) states that `x <<< n = x * 2^n`; consequently these shifts and additions concatenate the fragments without truncation or carries between them.

I decoded all 14,964 lanes, indexed by `4*a + directionCode d`, and compared every row with the geometry of its representative. I also checked all 240,368 raw-window/direction pairs against the same rows. Zero occurs exactly for inadmissible directions, and every admitted successor is exactly `1 + π(ωd)`, with values in `1..3741`. This verifies the actual successor and admissibility rules of `paper/app-input-contracts.tex:24–34` and the comparisons required at lines 408–417, preserving absolute E,N,W,S labels. In `supplied.successor`, natural subtraction by one is exact on every admitted edge and `% 3741` changes no valid class. Its value on a zero lane is an unused totalization, excluded by `allowed`.

DECL: edgeKinds_0 PASS

This auxiliary high fragment at `lean/AKLT/Defs/Automaton10Data.lean:1589` encodes the kinds specified in `paper/app-input-contracts.tex:385–388`; it has no independent paper counterpart. It contains exactly 8,192 two-bit lanes, corresponding to all four directions of classes 1693 through 3740. I checked its full integer value against the upper 16,384 bits of the independently regenerated kind table.

Two-bit natural lanes encode straight, turn, and revisit as 0, 1, and 2, matching the paper, and encode its inadmissible `-1` as 3. Revisit is tested first, using membership of the endpoint among earlier departure vertices, rather than an arrival or a repeated bond (`paper/app-input-contracts.tex:9–11,31–33`). All lanes agree with this rule. The fragment is an exact natural number, with no sign extension or coercion changing its bits.

DECL: edgeKinds_1 PASS

The low fragment at `lean/AKLT/Defs/Automaton10Data.lean:1591` encodes all four direction kinds for classes 0 through 1692, under the row and sentinel conventions in `paper/app-input-contracts.tex:385–388`. Its 13,544 bits are exactly 6,772 complete two-bit lanes. I regenerated all these lanes and checked equality of the entire fragment, including every inadmissible sentinel. The split between the two kind fragments falls on a class boundary, so no lane or direction label is shifted or omitted. Although `supplied.kind` totalizes code 3 as `.revisit`, `allowed` is false on exactly those lanes; this totalization cannot create a revisit edge. Admitted kinds are always below 3.

DECL: edgeKinds PASS

The assembly at `lean/AKLT/Defs/Automaton10Data.lean:1593` is precisely `edgeKinds_0 * 2^13544 + edgeKinds_1`, by the Mathlib shift identity cited above. The low fragment is strictly below `2^13544`, so the two fragments neither overlap nor introduce carries. `kindCode` at lines 1618–1619 extracts two-bit lanes in the same class/E,N,W,S order as the destination table.

All 14,964 decoded kinds equal the regenerated representative rows. Sentinel 3 occurs in exactly the 5,544 zero-destination lanes; the remaining lanes consist of exactly 2,516 straight, 5,032 turning, and 1,872 revisit edges, as asserted in `paper/app-input-contracts.tex:367–373,416–417`. Across all raw words I additionally checked kind invariance for every direction, successor-class invariance on every admitted direction, and final-direction agreement on every admitted non-revisit direction, covering the hypotheses at `paper/app-input-contracts.tex:315–325`. Thus this integer supplies the intended finite labelled kind table.

Non-blocking remarks:

- I read the complete target file and its transitive AKLT imports: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. The five declarations are auxiliary data definitions, with no hypotheses or quantifiers of their own; their consumers restrict classes to `Fin 3741`, directions to the four constructors of `Compass`, and meaningful raw words to distinct-bond windows.
- `Plane` is `ℤ × ℤ`; compass steps and reversals match the paper's signed displacements. `wordBond` is a two-element `Finset`, so equality ignores orientation, as confirmed by `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`). `RawWindow` is injectivity of these bonds, allowing vertex revisits. `departureCount` uses earlier indices, giving precisely the paper's departure convention.
- `lane` uses natural-number division and remainder: division by `2^(width*index)` discards lower bits, and remainder modulo `2^width` selects the lane. Both divisors are positive. `Fin.val` supplies an ordinary natural index. `List.finRange` enumerates each `Fin m` exactly once (`Mathlib/Data/List/FinRange.lean:29–44`); for `i : Fin 10`, `10 - 1 - i.val` does not truncate unexpectedly, so word coding agrees with the most-significant-first formula at `paper/app-input-contracts.tex:377–381`.
- Exhaustive regeneration produced the paper's counts at every depth from one through ten, including 60,092 raw windows. All 1,048,576 raw-code lanes have the correct validity sentinel, and all 3,741 representatives are valid and map to their own class. Hence the finite domains and surjectivity are substantive. No valid raw class or admitted successor is altered by the modulo operations. The default kind and successor on inadmissible directions do not contribute edges or transition weights.
- Validation is reproducible with `python3 audit_tables.py`; numerical evidence is in `audit_evidence.json`. It reads all 786 literal fragments and checks the assembled values using exact arithmetic. No Lean processes were needed. The external text archive was outside the supplied inputs; this review verifies the complete mathematical reconstruction contract, rather than asserting a byte-for-byte archive identity.
