STATUS: PASS
BLOCKING: 0

DECL: rawClass_525 PASS

This auxiliary literal is part of the supplied map in `p:automaton10` (`app-input-contracts.tex:367`, reconstruction contract at lines 376–419), rather than a separate paper definition. At `Automaton10Data.lean:1065` it is an exact natural number occupying bits [3964924,3981308) of `rawClass`. Through the 12-bit lane extractor it contributes to word codes 330410–331775, including the partial entries at both boundaries. All 183 raw words touching this chunk have valid class assignments satisfying the regenerated quotient conditions; all 1183 nonraw words have sentinel 3741. No mismatch was found.

DECL: rawClass_526 PASS

This is another auxiliary piece of the same supplied map (`app-input-contracts.tex:369`, with class bounds and representative requirements at lines 402–406). The exact `ℕ` literal at `Automaton10Data.lean:1067` occupies bits [3948540,3964924), contributing to codes 329045–330410. All 90 raw and 1276 nonraw words touching it have the required valid-class/sentinel distinction. Admissibility, kind, successor class and the conditional final-direction requirement agree with regeneration for its raw words. The entry shared with chunk 525 is decoded correctly.

DECL: rawClass_527 PASS

The exact natural-number literal at `Automaton10Data.lean:1069` occupies bits [3932156,3948540), contributing to codes 327679–329044. Its leading hexadecimal zero has no mathematical effect. All 329 raw and 1037 nonraw words touching it pass coverage and class checks. Its raw assignments satisfy the comparisons required by `app-input-contracts.tex:408–417`, including successor images and non-revisit arrivals. The partial boundary entry with chunk 528 and the boundary with chunk 526 are correctly reconstructed.

DECL: rawClass_528 PASS

This auxiliary piece implements the supplied map of `app-input-contracts.tex:367–419`. The exact `ℕ` literal at `Automaton10Data.lean:1071` occupies bits [3915772,3932156), contributing to codes 326314–327679. All 328 raw and 1038 nonraw words touching it have the correct class range or invalid-word sentinel. Regenerated absolute-direction admissibility, kinds, successors and required arrivals agree with its class assignments. Both partial boundary entries pass the same checks.

DECL: rawClass_529 PASS

The auxiliary literal at `Automaton10Data.lean:1073` occupies bits [3899388,3915772), contributing to codes 324949–326314. It is an exact natural number, with no machine-width overflow or signed interpretation. All 64 raw and 1302 nonraw words touching it pass coverage; all its raw class assignments satisfy the quotient checks in `app-input-contracts.tex:408–417` and the compatibility conditions at lines 315–341. Its shared entry with chunk 528 is correctly decoded.

Non-blocking remarks:

- I read the complete data file programmatically, including all literals and assembly expressions, and the project import chain `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Only the five assigned declarations receive verdicts here.
- Arithmetic and indexing: `Nat.shiftLeft_eq_mul_pow` (`Mathlib/Data/Nat/Size.lean:18`) gives `x <<< k = x * 2^k`. The assembly uses disjoint bit positions, so addition introduces no carries between chunks. Natural division and remainder extract base-4096 digits; the corresponding base-power identities are in `Mathlib/Data/Nat/Digits/Defs.lean:444` and `:465`. Every divisor is a positive power of 2 or 4. `List.finRange` lists each `Fin m` index once (`Mathlib/Data/List/FinRange.lean:29`); `m-1-i.val` never truncates incorrectly for `i : Fin m`. The E,N,W,S codes and most-significant-first word convention match `app-input-contracts.tex:377–388`.
- The independent Python check regenerates distinct unoriented bonds in `ℤ × ℤ`, with revisit detection by previous departures, matching `app-input-contracts.tex:21–42`. It reproduced every intermediate window count at lines 396–399. Across all 4^10 words, sentinel 3741 occurs exactly for nonraw words; every raw class lies in `Fin 3741`. All 3741 representatives are raw and map to their own classes. Every raw word agrees with its representative in admissibility and kind for all four directions, and all admitted stored kinds, successor classes and required arrivals agree. Edge counts are exactly (2516,5032,1872).
- Thus the modulo in `supplied.project` changes no raw class, and successor subtraction is applied to a positive one-based code on every admitted edge. Totalizations on invalid words or forbidden edges do not affect these checks. Finiteness comes from the actual function type `Fin 10 → Compass` and its raw-word subtype; surjectivity is witnessed by representatives, so the checks are not vacuous.
- Reproduction: run `python3 check_data.py`; detailed results are in `check_results.json`. No Lean processes were needed. The paper does not print individual archive map entries; this review verifies the literals against its complete mathematical reconstruction contract, without a separate comparison to the original archive bytes or its stated hash. Input files were not modified.
