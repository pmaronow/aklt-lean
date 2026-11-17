STATUS: PASS
BLOCKING: 0

DECL: rawClass_765 PASS

This private literal is an auxiliary fragment of the supplied class map, not a separate paper assertion. Its intended object is the map in `paper/app-input-contracts.tex:367–419` (`p:automaton10`), with word coding specified at lines 376–388. In `AKLT/Defs/Automaton10Data.lean:1545,1551`, its 16,384 bits are inserted at bit offset 32,764. They touch the 12-bit class lanes for word codes 2730–4095, including partial lanes at the boundaries; they must not be treated as an independently aligned array.

Checked the exact natural-number interpretation: hexadecimal literals have type `ℕ`, addition is unbounded natural addition, and `<<< n` multiplies by `2^n` (`Mathlib/Data/Nat/Size.lean:18`, `Nat.shiftLeft_eq_mul_pow`). The adjacent fragments do not overlap or cause carries. Exhaustive decoding and reconstruction found correct validity markers and quotient behavior for every affected lane, including all 201 valid raw windows touched by this fragment. Thus it supplies the right data for `rawClassAt` and `supplied`.

DECL: rawClass_766 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:1547`) serves the same supplied-map contract, `paper/app-input-contracts.tex:367–419`, rather than a separately stated mathematical definition. Its 16,384 bits start at offset 16,380 in `rawClass`, touching codes 1365–2730. The final four bits contribute to the lane shared with `rawClass_765`; the differing shift amounts correctly preserve that boundary.

Checked `ℕ` arithmetic and the shift-as-multiplication meaning from `Mathlib/Data/Nat/Size.lean:18`; there is no machine-width truncation. The complete reconstruction checked all touched lanes, including 90 valid raw windows, against distinct unoriented bonds, absolute direction labels, kinds, successor classes, and required final directions. No discrepancy was found.

DECL: rawClass_767 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:1549`) is the low fragment of the supplied map in `paper/app-input-contracts.tex:367–419`. It occupies the lowest 16,380 allocated bits, exactly 1,365 class lanes, for codes 0–1364. Its actual bit length is 16,375; the omitted leading zero bits are ordinary zero padding, not missing entries.

Checked that the hexadecimal literal denotes an exact natural number and that division and remainder in `lane` extract its low-to-high 12-bit fields. These are natural Euclidean operations with positive power-of-two divisors. All 1,365 lanes match raw-window validity; all 330 valid windows in this range pass the quotient comparisons. In particular, codes 0 and 1 map to classes 0 and 1, while code 2, which reverses the first bond, has invalid marker 3741. The fragment has the intended meaning under the paper's most-significant-first word code.

DECL: rawClass PASS

The assembled natural number (`AKLT/Defs/Automaton10Data.lean:1551`) correctly represents the paper's raw-to-class map, completed with an invalid-word marker outside its domain. The matching paper locations are `paper/app-input-contracts.tex:21–35` (`d:memory-automaton`), lines 315–341 (`l:automaton-quotient`), and lines 367–419 (`p:automaton10` and its reconstruction contract).

Evaluated the full assembly expression with exact integer arithmetic, checking all 768 fragments, their offsets, bounds, and absence of overlap/carry. The 1,048,576 decoded lanes all lie in 0–3741. Exactly 60,092 lanes are below 3741, and these are exactly the independently generated bond-distinct length-ten words; the other 988,484 lanes equal 3741. The depth-one through depth-ten counts are precisely 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092, as in paper lines 395–399.

Checked the consumers' mathematical meanings. `DirectionWord 10` is `Fin 10 → Compass`; `List.finRange` enumerates each index once (`Mathlib/Data/List/FinRange.lean:29–30`). Since `i.val < 10`, the natural subtraction `10-1-i.val` is the intended exponent 9 minus the zero-based index. The E,N,W,S codes 0,1,2,3 and displacements agree with paper lines 22–34 and 377–386. All encoding/decoding divisors are positive. `wordBond` is a finite unordered pair of distinct lattice vertices, so injectivity means precisely no repeated unoriented bond. `departureCount` at time ten counts times 0–9, giving the paper's revisit test, with revisit taking priority over straight/turn.

Every raw word and all four absolute directions were checked against its representative: identical admissibility and kind, correct admitted successor class, and identical final direction whenever an admitted non-revisit edge exists. All 3,741 classes occur, and all representatives are valid and map to their own classes. Regenerated quotient edges number 2,516 straight, 5,032 turning, and 1,872 revisit, exactly paper lines 372–373. The finite types enumerate actual words and directions; no stored-state list or additional correctness assumption is used to generate the raw domain.

The `% 3741` in `supplied.project` does not change any valid class number. It only totalizes invalid words, which the paper's domain excludes. Likewise, successor subtraction by one is exact on every admitted edge, whose stored destination lies in 1–3741; its truncated-zero behavior on forbidden edges is irrelevant. The positive class count prevents division-by-zero or empty-domain readings. The explicit coverage and correctness conjuncts in `AKLT/Blueprint/Top/ComputationV2.lean:13–26` prevent the totalizations from making the intended checks vacuous.

DECL: representatives_0 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:1553`) provides the high fragment of the supplied representative table required by `paper/app-input-contracts.tex:369–371,383–388,402–417`. Its 16,384 bits are inserted at offset 58,436 in the 74,820-bit table. The boundary is inside class 2921's 20-bit code: this fragment supplies its highest four bits and all codes for classes 2922–3740, touching 820 representatives altogether.

Checked the exact `ℕ` shift/addition meaning (`Mathlib/Data/Nat/Size.lean:18`) and the 20-bit Euclidean lane extraction. The fragment fits its allocated range with no overlap/carry. All 3,741 assembled representative codes are distinct and less than `4^10`; each decodes in the paper's most-significant-first convention to a generated raw window and maps to its own class. This includes every representative touched by this fragment. Consequently the representatives witness surjectivity without an extra hypothesis or a reduced domain, and decoding modulo four cannot conceal an out-of-range representative code.

Non-blocking remarks:

- Read the entire data file, processing every literal and assembly expression, and its complete local import chain: Automaton, Kernel, Trails, Domain, PinModel, Moment, Geometry. Only the five assigned declarations are judged here.
- Reproducible exhaustive arithmetic checks are in `check_data.py`; `check_data.out` records a successful run with no coverage, representative, row, successor, kind, or arrival errors. These are independent Python checks of the definitions, not a Lean proof. No Lean processes were launched and no input files were changed.
- The permitted inputs do not include `windows_m10_min.txt` or its archive. Its byte identity and the provenance SHA-256 in the Lean comment were therefore not authenticated. The mathematical reconstruction contract stated in the supplied paper was checked exhaustively. The paper expressly makes no minimality or spatial-symmetry claim (lines 418–419), and none is needed for these auxiliary data.
