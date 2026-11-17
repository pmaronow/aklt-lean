STATUS: PASS
BLOCKING: 0

DECL: rawClass_690 PASS

This is an auxiliary literal, not a separate paper assertion. Its intended role is part of the supplied map in `paper/app-input-contracts.tex:367–388` (`p:automaton10`), checked by the reconstruction contract at `paper/app-input-contracts.tex:390–419`. The declaration is at `lean/AKLT/Defs/Automaton10Data.lean:1395`.

Its 4096 hexadecimal digits represent an exact natural number occupying bits 1261564–1277947 of `rawClass`, with bit zero least significant. It intersects the 12-bit class lanes for codes 105130–106495. These 1366 codes contain 90 raw windows and 1276 invalid words. Independent reconstruction verified every intersecting lane, including the two lanes split across chunk boundaries: code 105130 has class 356, and code 106495 has invalid-word sentinel 3741. Every affected raw window agrees with its supplied representative on admissibility, kind, successor class, and the required final direction. These are precisely the raw-window and quotient conditions of `paper/app-input-contracts.tex:21–35`, `:315–325`, and `:408–417`.

The Mathlib meaning checked is ordinary, unbounded `ℕ` arithmetic: `Nat.shiftLeft_eq_mul_pow` makes each shift multiplication by a power of two, and natural division followed by remainder extracts the indicated 12-bit lane. There is no machine-word overflow, signed interpretation, extra hypothesis, or independent assertion of correctness hidden in the literal. The shared domain and arithmetic checks below apply.

DECL: rawClass_691 PASS

This auxiliary portion of the supplied map implements `paper/app-input-contracts.tex:367–388` and its checks at `:390–419`; its Lean declaration is at `lean/AKLT/Defs/Automaton10Data.lean:1397`.

The 4096 hexadecimal digits occupy bits 1245180–1261563 and intersect codes 103765–105130. There are 222 raw windows and 1144 invalid words in that interval. All lanes satisfy the paper's independently generated raw-window domain, and all raw class assignments satisfy the representative and transition comparisons at `paper/app-input-contracts.tex:404–417`. The boundary lanes decode to class 115 at code 103765 and class 356 at code 105130; the latter is shared with `rawClass_690` and was checked after concatenation.

As for `rawClass_690`, the relevant Mathlib operations are exact natural shifts, addition, division, and remainder. The chunk starts on a lane boundary and ends inside a lane; it is correctly treated as a bit fragment rather than a standalone array of classes. No carry or boundary shift changes a class. The shared checks below apply.

DECL: rawClass_692 PASS

The corresponding paper object is the supplied raw-to-class map of `paper/app-input-contracts.tex:367–388`, with raw generation and representative checks at `:390–417`. The declaration is at `lean/AKLT/Defs/Automaton10Data.lean:1399`.

Its 4096 hexadecimal digits occupy bits 1228796–1245179 and intersect codes 102399–103764. These include 270 raw windows and 1096 invalid words. Every affected entry passed raw-domain coverage and the full representative/transition reconstruction. Code 102399, whose lane crosses the preceding boundary, has sentinel 3741; code 103764 has class 114. The leading zero hexadecimal digit is retained in determining the concatenation width: the surrounding expression shifts by the fixed allocated width, not by the numeral's actual bit length.

Mathlib's `ℕ` numeral and `Nat.shiftLeft_eq_mul_pow` give exactly this interpretation. The lane divisions have positive power-of-two denominators, and no truncation or modular reduction changes a valid class label. The shared checks below apply.

DECL: rawClass_693 PASS

This auxiliary chunk supplies the dense extension of the paper's map, whose mathematical domain is only `Ω₁₀` (`paper/app-input-contracts.tex:21–35`, `:367–384`). Its declaration is at `lean/AKLT/Defs/Automaton10Data.lean:1401`.

Its 4096 hexadecimal digits occupy bits 1212412–1228795 and intersect codes 101034–102399. Every one of these 1366 words begins E,N,W,E. The fourth step reverses the third and repeats the same unoriented bond, so none belongs to `Ω₁₀`. All intersecting lanes, including both boundary lanes, correctly decode to sentinel 3741. This is a justified invalid-domain encoding, not a vacuous replacement of any paper condition: `Automaton10StatementV2` explicitly checks that a lane is below 3741 exactly when its decoded word is raw.

The relevant Mathlib checks are exact natural bit packing and the unoriented meaning of the finite set `{u,v}`: `Finset.pair_comm` identifies `{u,v}` with `{v,u}`. Thus the reversal really violates `Function.Injective (wordBond (0,0) w)`. The shared checks below apply.

DECL: rawClass_694 PASS

This has the same auxiliary role under `paper/app-input-contracts.tex:21–35` and `:367–406`; its declaration is at `lean/AKLT/Defs/Automaton10Data.lean:1403`.

The 4096 hexadecimal digits occupy bits 1196028–1212411 and intersect codes 99669–101034. All 1366 words again have prefix E,N,W,E and repeat the third bond on the fourth step. All decoded entries are correctly 3741, including the boundary shared with `rawClass_693`. There is therefore no missing raw window, collapsed valid class, or unintended restriction on the paper's map.

As checked in Mathlib's finite-set pair lemmas, reversing the endpoints preserves an unoriented bond. Natural-number shifts and lane extraction preserve the sentinel exactly. Although `supplied.project` totalizes this sentinel by reducing modulo 3741, these words are outside the paper's domain, and the explicit raw-coverage condition prevents that totalization from disguising an invalid entry. The shared checks below apply.

Non-blocking remarks and shared semantic checks:

- Scope and context: I read the entire target file, parsing all 786 literal declarations and all four concatenation expressions, and read its project import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. I also inspected the consuming `Automaton10StatementV2` in `lean/AKLT/Blueprint/Top/ComputationV2.lean:13–26`. Only the five assigned declarations are judged here.

- Domain and geometry: `DirectionWord 10` is `Fin 10 → Compass`; `Compass` has exactly E,N,W,S, with the integer steps in the paper. `wordVertex` sums precisely the prefix with index below the supplied bound. At indices 0–10 it has no clamping discrepancy. `wordBond` is a finite set of its two distinct endpoints, and `RawWindow` requires injectivity of the bond function. It therefore forbids repeated unoriented bonds while allowing repeated vertices. The finite-set interpretation was checked in `Mathlib/Data/Finset/Insert.lean:413–420`; `Finset.range` membership is strict inequality (`Mathlib/Data/Finset/Range.lean:64`). Consequently the departure count at time ten tests exactly vertices 0 through 9, as required by `paper/app-input-contracts.tex:31–33`.

- Coding and arithmetic: `encodeWord` and `decodeWord` use E,N,W,S = 0,1,2,3 and the most-significant-first convention of `paper/app-input-contracts.tex:376–388`, not the distinct H2 convention. `List.finRange` includes each `Fin m` exactly once (`Mathlib/Data/List/FinRange.lean:29–33`). For `i : Fin 10`, the natural subtraction `10 - 1 - i.val` is exactly 9 minus the zero-based index; it never underflows. All denominators in lane and word decoding are positive powers of 2 or 4. `Nat.shiftLeft_eq_mul_pow` (`Mathlib/Data/Nat/Size.lean:18`) and the base-digit division/remainder lemmas (`Mathlib/Data/Nat/Digits/Defs.lean:444–489`) justify the bit interpretation. All concatenation positions were checked, including split lanes; no chunk overlaps or carries into another.

- Totalizations and quantifiers: valid raw labels are all strictly below 3741, so `project`'s `% 3741` leaves them unchanged. A stored positive destination is the successor class plus one, so its natural subtraction by one is exact. Destination zero and kind three encode the paper's forbidden-direction pair of minus ones; the resulting successor totalization is consulted only under admissibility. Every class has a raw representative mapping to itself. Checks range over every raw word and every absolute direction, with no assumed correctness hypothesis. They include matching kinds even for inadmissible directions, as required by `paper/app-input-contracts.tex:317–321`, and final-direction equality whenever there is an admitted non-revisit edge. No spatial symmetry or minimality assumption was introduced.

- Finiteness: the four-element compass instance and `Fin 10` enumerate the full word type; `MemoryWindow 10` is the actual raw-word subtype. `Fintype.ofFinite` chooses an enumeration of that subtype, not a smaller stored list (`Mathlib/Data/Fintype/EquivFin.lean:175–180`). Cardinality is independent of that enumeration (`Mathlib/Data/Fintype/Card.lean:67`). The fixed memory ten also avoids the unrelated totalization at memory zero.

- Reproducible check: `python3 check_data.py` completed successfully; results are in `check_data_results.json`. It regenerated the paper's depth counts 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092; checked all 1,048,576 raw-code lanes, all 3741 representatives, and all 240368 raw-word/direction combinations; and recovered the labelled edge counts 2516 straight, 5032 turning, and 1872 revisit. The assigned chunks intersect 581 distinct raw windows in total. This is independent computational evidence, not a Lean proof. No Lean process was needed and no input was modified.

- Provenance limitation: the header's archive SHA-256 was not independently verified. The verdict concerns the supplied literal data's mathematical meaning and satisfaction of the paper's reconstruction contract; it does not certify byte-for-byte archival provenance.
