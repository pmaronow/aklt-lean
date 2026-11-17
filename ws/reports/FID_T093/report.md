STATUS: PASS
BLOCKING: 0

DECL: rawClass_430 PASS

This auxiliary natural-number literal (`AKLT/Defs/Automaton10Data.lean:875`) supplies part of the map in Proposition `p:automaton10`, rather than having a separate paper definition. The relevant paper locations are `app-input-contracts.tex:21–35` (raw windows) and `app-input-contracts.tex:367–419` (the supplied quotient and reconstruction contract).

In the actual concatenation at `Automaton10Data.lean:1551`, it occupies bit positions 5,521,404–5,537,787, overlapping the 12-bit lanes for codes 460117–461482. All 1,366 overlapping words are invalid: their initial N,S steps reuse an unoriented bond. Every reconstructed lane equals the invalid-word sentinel 3741. This correctly excludes words outside the paper's domain; it does not exclude any genuine raw window. Checked the natural-number meaning of `<<<`, addition, division and remainder: these concatenate bits without fixed-width overflow and extract the intended lanes (`Mathlib/Data/Nat/Bitwise.lean:355–356`; `Automaton10Data.lean:1595–1611`). Boundary lanes were checked after assembly, including their neighboring chunks.

DECL: rawClass_431 PASS

This auxiliary literal (`Automaton10Data.lean:877`) implements the same paper map and contract (`app-input-contracts.tex:367–419`), with raw-word membership defined at `app-input-contracts.tex:24–33`.

Its assembled bit interval is 5,505,020–5,521,403, overlapping codes 458751–460116. Exactly one overlapping word is raw: code 458751, NWSSSSSSSS, maps to class 218; its supplied representative is code 1023. The other 1,365 words have sentinel 3741 and are geometrically invalid. The raw word lies on the chunk boundary: this declaration contributes its upper four lane bits, which are zero; the assembled value is 218, not the sentinel. Verified compatibility with its representative for all four absolute directions, including successor classes and non-revisit arrival. Checked ordinary `ℕ` arithmetic and `Fin 3741` indexing: `Fin.val` is the bounded natural index, and `% 3741` preserves this valid class number. No sign conversion or wraparound changes its meaning.

DECL: rawClass_432 PASS

This auxiliary literal (`Automaton10Data.lean:879`) is part of the raw-to-class map required by `app-input-contracts.tex:367–388,402–419`.

Its assembled bit interval is 5,488,636–5,505,019, overlapping codes 457386–458751. Of these 1,366 words, exactly 328 are raw and have class numbers below 3741; the other 1,038 have sentinel 3741. All raw assignments agree with their supplied representatives on admissibility, kind, successor class and required final direction. For example, code 457386, NWSSWWWWWW, maps to class 356 with representative code 1706. Checked the most-significant-first encoding against `app-input-contracts.tex:376–386`: `List.finRange 10` lists each index once (`Mathlib/Data/List/FinRange.lean:29–43`), and `10 - 1 - i.val` is the intended exponent 9−i, since `i.val < 10`. Natural subtraction therefore does not truncate an intended negative exponent. Both split boundary lanes were reconstructed with their neighbors.

DECL: rawClass_433 PASS

This auxiliary literal (`Automaton10Data.lean:881`) serves the supplied quotient contract in `app-input-contracts.tex:367–419`, using the bond and revisit conventions of `app-input-contracts.tex:24–34`.

Its assembled bit interval is 5,472,252–5,488,635, overlapping codes 456021–457386. Exactly 89 overlapping words are raw with valid class numbers, and 1,277 are invalid with sentinel 3741. All raw assignments satisfy the representative and transition comparisons. For example, code 456960, NWSSWNEEEE, maps to class 683 with representative code 6400. Checked that `RawWindow` means injectivity of the map from ten step indices to unordered two-element finite sets of lattice vertices (`Automaton.lean:8–13`; `Trails.lean:24–32`). Mathlib finite-set equality ignores order (`Mathlib/Data/Finset/Insert.lean:413–420`), so traversing an edge backward counts as reuse. Revisit detection tests the endpoint against earlier departure vertices, including the starting vertex, exactly as the paper requires. There is no spatial or rotational quotient in this membership test.

DECL: rawClass_434 PASS

This auxiliary literal (`Automaton10Data.lean:883`) supplies another portion of the map in `app-input-contracts.tex:367–419`.

Its assembled bit interval is 5,455,868–5,472,251, overlapping codes 454655–456020. Exactly 176 overlapping words are raw with valid classes, and 1,190 are invalid with sentinel 3741. Every raw assignment passes the paper's per-direction comparisons. For example, code 454655, NWSWSSSSSS, maps to class 218 with representative code 1023. Checked that lattice positions are pairs of integers, steps have the stated E,N,W,S signs, and successor words drop the oldest direction before appending the new one (`Geometry.lean:8–36`; `Automaton.lean:23–44`). Checked `Fin 10 → Compass` as the full set of length-ten words, not a selected enumeration: Mathlib's function-type `Fintype` enumerates all functions (`Mathlib/Data/Fintype/Pi.lean:133–137`). Neither finiteness nor an empty-domain interpretation removes any required checks.

Non-blocking remarks:

- Read the entire data file, including all 786 literal definitions and all four assembly expressions, and the complete AKLT import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. The five assigned declarations are closed definitions of `ℕ` literals with no hypotheses, quantifiers or correctness axioms. `private` affects name visibility, and `noncomputable` does not weaken their values.
- The exact-integer audit independently generated the paper's distinct-bond words. Counts at depths 1–10 were 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092, matching `app-input-contracts.tex:390–401`. Across all 4^10 codes, the reconstructed class is below 3741 exactly for those 60092 raw words; all other entries equal 3741.
- For context, the audit also checked all 3741 representatives, every direction at all 60092 raw words, and the 2516 straight, 5032 turning and 1872 revisit quotient edges. Representatives are genuine raw words and map to their own classes, so the quotient domain is nonempty and surjectivity is substantive. The assignment checks include kind agreement on inadmissible directions as well as every admitted successor and required final direction.
- `lane` divides and takes remainder by powers of two, which are positive. Word decoding uses positive powers of four and `% 4`, so the direction decoder receives only 0–3. Valid class numbers are unchanged by `% 3741`. Stored admitted destinations are successor class plus one, so natural subtraction by one does not truncate on admitted edges. Sentinel projection and the zero-destination totalization affect inputs outside the paper's corresponding domain; the V2 coverage and correctness conditions explicitly guard those domains (`ComputationV2.lean:13–26`). No division-by-zero, sign, indexing or totalization discrepancy was found in the assigned data.
- Chunk boundaries need not coincide with lane boundaries. The per-declaration counts above concern overlapping lanes; shared boundary words occur in both neighboring counts. All comparisons used the assembled table, avoiding an independent-chunk alignment assumption.
- Reproducible external check: `python3 audit_raw_classes.py`; detailed results are in `audit_results.json`. It verifies the paper's mathematical reconstruction contract against the Lean literals; it is not a Lean kernel proof or a byte-for-byte comparison with the external archive named in the docstring. No Lean process was launched, and inputs were not modified.
