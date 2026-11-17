STATUS: PASS
BLOCKING: 0

DECL: rawClass_655 PASS

`AKLT/Defs/Automaton10Data.lean:1325` is auxiliary packed data for the supplied map of `p:automaton10`, rather than a separate paper statement. In the actual assembly at line 1551, its 16384 bits begin at bit 1835004 and touch word codes 152917–154282. Every bit agrees with the invalid-word marker 3741 (`0xe9d`), including partial boundary lanes. Every touched word begins E,W under the paper's most-significant-first convention (`app-input-contracts.tex:377–388`). Such a word repeats its first unoriented bond and is excluded by `d:memory-automaton` (`app-input-contracts.tex:24–29`). Checked Mathlib meanings: exact `ℕ` arithmetic and shifts, natural quotient/remainder lane extraction, and unordered `Finset` bonds; details below. This is correct padding outside the paper map's domain.

DECL: rawClass_656 PASS

`AKLT/Defs/Automaton10Data.lean:1327` supplies 16384 bits at bit offset 1818620, touching codes 151551–152916. Its entire literal, including the split lanes, matches marker 3741. All these codes decode to words beginning E,W, hence have equal first and second `Finset` bonds and fail `RawWindow`. This matches the domain restriction in `app-input-contracts.tex:24–29` and the coding of `p:automaton10` at `app-input-contracts.tex:377–388`. The exact natural-number and unordered-bond semantics checked below give the intended dense-table extension, with no valid raw window assigned a sentinel by this segment.

DECL: rawClass_657 PASS

`AKLT/Defs/Automaton10Data.lean:1329` supplies 16384 bits at bit offset 1802236, touching codes 150186–151551. Every literal bit and every assembled boundary lane matches marker 3741. All touched words begin E,W and repeat the initial unoriented bond, so none belongs to the paper's raw domain (`app-input-contracts.tex:24–29`, with code convention at lines 377–388). Under Mathlib's exact natural shifts, division/remainder and unordered `Finset` equality, this segment correctly records invalid words and does not alter the quotient on raw windows.

DECL: rawClass_658 PASS

`AKLT/Defs/Automaton10Data.lean:1331` supplies 16384 bits at bit offset 1785852, touching codes 148821–150186. Its bits and the complete assembled lanes they touch all give marker 3741. Each code has initial directions E,W, violating distinctness of unoriented bonds exactly as required by `app-input-contracts.tex:24–29`; the decoding agrees with lines 377–388. The checked natural arithmetic and `Finset` meanings introduce no truncation, orientation distinction or accidental valid state. This is the appropriate auxiliary padding for the supplied map.

DECL: rawClass_659 PASS

`AKLT/Defs/Automaton10Data.lean:1333` supplies 16384 bits at bit offset 1769468, touching codes 147455–148820. All bits, including both partial-lane boundaries, match marker 3741. Every touched code starts E,W and therefore repeats the bond between `(0,0)` and `(1,0)`. The paper excludes precisely this repetition (`app-input-contracts.tex:24–29`), with absolute direction order and coding fixed at lines 377–388. Exact `ℕ` lane extraction and unordered `Finset` bonds consequently give correct invalid-word padding for this auxiliary declaration.

Non-blocking remarks and shared semantic checks:

The paper map is defined on the 60092 raw windows, with class values 0–3740 (`app-input-contracts.tex:367–406`). These five private constants have no individual paper counterpart. Lean extends that map to all `4^10` codes using an out-of-range sentinel. `Automaton10StatementV2` explicitly requires `rawClassAt code ≤ 3741` and `rawClassAt code < 3741 ↔ RawWindow (decodeWord 10 code)` (`AKLT/Blueprint/Top/ComputationV2.lean:13–17`). Each reviewed lane satisfies this requirement: its marker is 3741 and its word is non-raw.

`ℕ` is unbounded, so the hexadecimal literals and additions have no machine overflow. `Nat.shiftLeft_eq_mul_pow` identifies `x <<< n` with `x * 2^n` (`Mathlib/Data/Nat/Size.lean:18`). I parsed the actual assembly and checked that all segment slots abut without overlap or carries. `lane` uses natural Euclidean division and remainder (`Automaton10Data.lean:1596`); its divisors are positive powers of two. Thus width 12 extracts a genuine base-4096 digit. The reviewed literals' rotating hexadecimal patterns are the expected phases of repeated 12-bit `0xe9d`, rather than byte-aligned entries.

`DirectionWord 10` is `Fin 10 → Compass`; direction codes are 0=E, 1=N, 2=W, 3=S. For every `i : Fin 10`, the natural exponent `10-1-i.val` is nonnegative without unintended truncation. Consequently encoding and decoding use exactly the paper's digit order (`Automaton10Data.lean:1598–1609`). All touched codes lie within the E,W prefix interval 131072–196607.

`Plane` is `ℤ × ℤ` with componentwise addition. `wordBond` is a two-element `Finset` of consecutive vertices (`AKLT/Defs/Trails.lean:24–32`); `Finset.pair_comm` confirms that reversing its endpoints preserves equality (`Mathlib/Data/Finset/Insert.lean:419`). For E,W, bonds at distinct indices 0 and 1 coincide, contradicting `Function.Injective` in `RawWindow` (`AKLT/Defs/Automaton.lean:9–10`). This verifies invalidity geometrically, without relying on a stored state list or a finiteness assumption.

`supplied.project` reduces the sentinel modulo 3741 to class 0 only to totalize non-raw words (`Automaton10Data.lean:1621–1624`). Correctness is quantified over raw words, and its representatives must themselves be raw (`Automaton.lean:78–84`). The reviewed padding therefore creates no spurious raw state or vacuous quotient obligation. These declarations contain no hypotheses, quantifier choices, rational division or sign conventions beyond the checked coding.

Reproducible check: `python3 check_raw_classes.py` passed, comparing all 81920 assigned literal bits and all 6828 distinct touched lanes, including neighboring boundary bits. The whole target file and its AKLT import chain were read for context. No input was modified and no Lean process was launched. These verdicts concern only the five assigned declarations.
