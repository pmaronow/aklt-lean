STATUS: PASS
BLOCKING: 0

DECL: representatives_1 PASS

This private natural-number literal (`AKLT/Defs/Automaton10Data.lean:1555`) is an auxiliary storage fragment of the representatives in Proposition `p:automaton10`, `app-input-contracts.tex:367–419`, especially the representative requirements at lines 404–405. It occupies bits 42052 through 58435 of `representatives`, intersecting the 20-bit codes for classes 2102 through 2921. Its bit length is exactly 16384, so it fits its allocated field. I checked the actual literal, its placement, and every affected decoded representative, including both split boundary codes. Each is a bond-distinct length-ten window and maps to its own class. The relevant Mathlib meaning is natural-number shift, `n <<< k = n * 2^k` (`Mathlib/Data/Nat/Size.lean:18`); there is no fixed-width overflow or implicit truncation.

DECL: representatives_2 PASS

This literal (`AKLT/Defs/Automaton10Data.lean:1557`) supplies bits 25668 through 42051, intersecting classes 1283 through 2102. It has exactly 16384 bits. It is another auxiliary fragment of the representative data required by `app-input-contracts.tex:383–405`, rather than a separate mathematical assertion. Using the same Mathlib natural-number shift meaning, I checked that its bits are placed without overlap or a gap and that all affected 20-bit codes, including the codes shared with neighboring fragments, satisfy the paper's representative requirements. No extra condition on the windows or their initial directions is introduced.

DECL: representatives_3 PASS

This literal (`AKLT/Defs/Automaton10Data.lean:1559`) supplies bits 9284 through 25667, intersecting classes 464 through 1283, and has exactly 16384 bits. Its role is the same representative storage specified by `app-input-contracts.tex:383–405`. Natural-number addition and the Mathlib shift identity above concatenate disjoint fields here. I checked both partial boundary codes and all intervening codes against independently generated raw windows and the supplied class map. Every decoded representative is valid and has its own class number; there is no reversal of the representative order or of the directions within a word.

DECL: representatives_4 PASS

This literal (`AKLT/Defs/Automaton10Data.lean:1561`) occupies the lowest 9284 allocated bits, intersecting classes 0 through 464. Its actual bit length is 9282; the two leading zero bits are correctly retained by the explicit shift of the following fragment by 9284. Thus no bit is lost at the class-464 boundary. The paper counterpart is again the representative-per-class contract in `app-input-contracts.tex:369–371,383–405`. Natural-number literals and arithmetic preserve this field exactly. Every affected representative passes the raw-window and class checks. In particular, representative code zero denotes ten eastward steps, not an empty or degenerate window.

DECL: representatives PASS

The assembly at `AKLT/Defs/Automaton10Data.lean:1563` is exactly

```
r₀ * 2^58436 + r₁ * 2^42052 + r₂ * 2^25668 + r₃ * 2^9284 + r₄,
```

where `rᵢ` is `representatives_i`. The allocated fragment widths are 16384, 16384, 16384, 16384, and 9284, totaling 74820 = 3741 * 20 bits. Each fragment fits, so the additions cause no carries into adjacent fields. The consumer `representativeCode` extracts lane `a.val` for every `a : Fin 3741` (`Automaton10Data.lean:1596,1613`). This yields exactly 3741 distinct codes, all below `4^10 = 1048576` (minimum 0, maximum 1042000). Every code independently regenerates a raw window and has `rawClassAt code = a.val`, before any modulo operation. Consequently these are actual representatives proving coverage of all classes, as required at `app-input-contracts.tex:404–405,415–416`.

I also checked their use by `supplied.representative` and `supplied.arrival` (`Automaton10Data.lean:1623–1629`) and by `Automaton10StatementV2` (`AKLT/Blueprint/Top/ComputationV2.lean:13–26`). For all 60092 independently generated raw windows and all four absolute directions, the representatives agree on admissibility and kind; admitted successors have the stored class; and non-revisit transitions have the representative's final direction. The regenerated quotient edge counts are 2516 straight, 5032 turning, and 1872 revisit edges. These match `app-input-contracts.tex:315–341,367–419`. Thus this auxiliary object supports the intended quotient, including the incoming-direction condition.

The following semantic checks apply to all five declarations and their consumers:

- `ℕ` literals, shifts, sums, products, division, and remainder are exact natural-number operations. `lane packed 20 a` is the base-`2^20` digit at index `a`. Its divisor `2^(20*a)` and modulus `2^20` are positive, so division-by-zero totalization cannot affect any representative.
- Codes within each lane use the paper's most-significant-first word convention (`app-input-contracts.tex:377–380`), even though class zero occupies the least significant lane of the packed integer. `directionCode`/`direction` give E,N,W,S the numbers 0,1,2,3, consistently with `app-input-contracts.tex:219,385–388`. `decodeWord 10 code` uses exponent `10-1-i.val`; for `i : Fin 10` this is exactly 9 through 0, so natural subtraction never changes an intended negative exponent into zero. The final direction is `code % 4`.
- `DirectionWord 10` is the full function type `Fin 10 → Compass` (`Trails.lean:24`). `List.finRange` enumerates each index once, with its value as position (`Mathlib/Data/List/FinRange.lean:29–43`), so `encodeWord` matches the displayed paper sum. The code bound ensures encoding and decoding lose no digits. The default branch of `direction` is only reached with digit 3.
- The lattice is `ℤ × ℤ`, with the four specified signed unit steps (`Geometry.lean:8,25–36`). `RawWindow` is injectivity of the map from step indices to `Finset` endpoint pairs (`Automaton.lean:9–10`; `Trails.lean:27–32`). These are unoriented bonds: Mathlib has `{x,y} = {y,x}` (`Mathlib/Data/Finset/Insert.lean:419`). Unit steps ensure distinct endpoints. Revisit detection counts precisely departures at indices 0 through 9, matching `app-input-contracts.tex:21–34`; it does not count the current endpoint merely as an arrival.
- The domains are nonempty, finite, and exhaustive. `Fin 3741` supplies exactly the stated class indices; the four-constructor `Compass` instance lists all directions. Finite function spaces and subtypes have the usual meanings (`Mathlib/Data/Fintype/Pi.lean:134–136`; `Mathlib/Data/Fintype/EquivFin.lean:179,195–196`). `Fintype.ofFinite` selects an enumeration of the actual raw-window subtype, not of a supplied list. No finiteness assumption restricts the words under review.
- The projection's `% 3741` cannot conceal a bad representative: every representative has an already valid class number equal to its index. Likewise, the successor's truncated subtraction is used on positive destination codes on admitted edges. The literal definitions contain no hypotheses or quantifiers to weaken, strengthen, or render vacuous. Their consumers check every class. `noncomputable` and `private` do not change their mathematical values.

Non-blocking remarks:

The complete target file was read programmatically, including all numerical literals and assembly expressions. Its local import chain (`Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, `Geometry`) was read for context. Only the five assigned declarations are judged here.

The reproducible finite audit is `check_representatives.py`; its successful output is `check_results.json`. It checked all 1048576 raw code slots, independently generated all 60092 raw windows, and made 240368 raw-window/direction comparisons. No Lean processes were used; these checks are audit evidence, not a Lean correctness proof.

The paper specifies the archive's representative contract but does not print the hexadecimal fragments. The original `windows_m10_min.txt` archive is outside the permitted inputs, so its byte-level identity and the checksum in the Lean docstring were not independently authenticated. The literal data's mathematical representative and quotient properties were checked directly, with no discrepancy found.
