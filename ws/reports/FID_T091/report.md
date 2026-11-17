STATUS: PASS
BLOCKING: 0

DECL: rawClass_420 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:855`) correctly supplies invalid-word markers for the dense representation of the map in `paper/app-input-contracts.tex:367–405` (`p:automaton10`). It occupies inclusive bit positions 5685244–5701627 of `rawClass`, touching word codes 473770–475135. Every such ten-direction word begins N,S and therefore repeats its first unoriented bond; it is outside the paper's domain by `paper/app-input-contracts.tex:24–26`. Exact checking of all 16384 literal bits, including partial lanes at both ends, gives precisely the corresponding bits of repeated `3741 = 0xe9d` markers. The natural-number shift and division/remainder meanings checked below ensure these are markers rather than class numbers.

DECL: rawClass_421 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:857`) occupies inclusive bit positions 5668860–5685243, touching codes 472405–473770. All these words begin N,S and fail the distinct-unoriented-bond condition of `paper/app-input-contracts.tex:24–26`. All 16384 bits equal the appropriate portions of the invalid-word marker `3741`; complete extracted lanes, including the upper lane shared with `rawClass_420`, also equal 3741. With exact `ℕ` arithmetic and 12-bit lane extraction, it correctly extends the paper's raw-only map (`paper/app-input-contracts.tex:382–405`) to a dense table without assigning any of these words a valid class.

DECL: rawClass_422 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:859`) occupies inclusive bit positions 5652476–5668859, touching codes 471039–472404. Every word begins N,S, hence is excluded by `paper/app-input-contracts.tex:24–26`. Exact natural-number bit extraction verifies all 16384 bits against repeated `0xe9d = 3741` markers, including the partial lowest lane. Thus it correctly represents absence from the raw map specified at `paper/app-input-contracts.tex:382–405`; no valid raw window or class assignment is lost.

DECL: rawClass_423 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:861`) occupies inclusive bit positions 5636092–5652475, touching codes 469674–471039. All decoded words begin N,S and reuse the first bond, contrary to `paper/app-input-contracts.tex:24–26`. All 16384 bits match the appropriate invalid-word sentinel bits. Complete 12-bit lanes at both fragment boundaries also extract to 3741. Under the checked unbounded `ℕ` shift/division/remainder semantics, this is the correct auxiliary data for the raw-only map of `paper/app-input-contracts.tex:382–405`.

DECL: rawClass_424 PASS

This auxiliary literal (`AKLT/Defs/Automaton10Data.lean:863`) occupies inclusive bit positions 5619708–5636091, touching codes 468309–469674. Every word begins N,S, so none satisfies the paper's distinct-unoriented-bond definition (`paper/app-input-contracts.tex:24–26`). All 16384 bits and every complete affected lane match the invalid-word sentinel 3741, including the upper lane shared with `rawClass_423`. This exact natural-number encoding correctly represents words absent from the supplied map's domain (`paper/app-input-contracts.tex:382–405`).

Shared semantic checks and evidence:

- These declarations are private definitions of exact natural-number literals, with no hypotheses, quantifiers, coercions, axioms, or correctness assertions. The paper does not prescribe these individual storage fragments. Their relevant counterpart is the supplied map on raw words in `p:automaton10`, together with its independently defined domain. I read the complete data file and its AKLT import chain: Automaton, Kernel, Trails, Domain, PinModel, Moment, and Geometry.
- `Nat.shiftLeft_eq_mul_pow`, `Mathlib/Data/Nat/Size.lean:18`, establishes that `x <<< k` means `x * 2^k`, with no machine-word overflow. Parsing the actual parenthesized assembly at `Automaton10Data.lean:1551` gives the bit positions above. All fragments fit their allocated widths, so addition introduces no overlapping fields or carries.
- `lane` and `rawClassAt` (`Automaton10Data.lean:1596,1611`) extract `(rawClass / 2^(12*code)) % 4096`. These are natural quotient and remainder; both divisors are positive. The digit meanings agree with `Mathlib/Data/Nat/Digits/Defs.lean:444–489`. The sentinel 3741 fits in 12 bits and lies outside the class range 0–3740.
- Encoding uses E,N,W,S = 0,1,2,3 and most-significant-first base-four digits (`Automaton10Data.lean:1598–1609`), as required by `paper/app-input-contracts.tex:219,377–386`. `Fin 10` indexes exactly 0–9; `List.finRange` enumerates each index once (`Mathlib/Data/List/FinRange.lean:29–43`). Hence the natural subtraction `10 - 1 - i.val` is exactly `9 - i.val`, without unintended truncation. The direction decoder receives a remainder below four, so its fallback means exactly south.
- `Plane` is the integer lattice, and `wordBond` is an unordered `Finset` of consecutive vertices (`AKLT/Defs/Geometry.lean:8–30`; `AKLT/Defs/Trails.lean:25–33`). In particular, `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`) identifies `{(0,0),(0,1)}` with `{(0,1),(0,0)}`. The distinct indices 0 and 1 therefore have equal bonds in every affected word, refuting `RawWindow`'s `Function.Injective` condition. This is exactly the paper's bond exclusion, with absolute directions and no spatial quotient. The classical finite enumeration of `MemoryWindow` adds no extra membership restriction.
- The consumer explicitly distinguishes sentinels: `Automaton10StatementV2` (`AKLT/Blueprint/Top/ComputationV2.lean:13–23`) requires an entry below 3741 exactly for raw words, and an entry at most 3741 for every word code. Thus these invalid codes must have value 3741. `supplied.project` subsequently maps their marker to zero by `% 3741` (`Automaton10Data.lean:1624`); this only totalizes the map outside the paper's domain. `MemoryQuotient.Correct` restricts its transition obligations to raw words (`AKLT/Defs/Automaton.lean:78–84`). No valid raw word lies in any assigned fragment. The successor's natural subtraction is in a separate table and is not used by these literals.
- `python3 check_fragments.py` passed. It parses the source assembly, checks every assigned bit against independently constructed sentinel bits, checks complete boundary lanes using neighboring fragments, and independently tests bond reuse for all 6827 distinct affected word codes. All are invalid and all extracted entries are 3741. No Lean process was needed.

Non-blocking remarks:

The sentinel is an implementation convention for a dense table; the paper lists only valid raw words. Its use here is faithful and does not make any paper assertion vacuous. This review establishes fidelity of the five assigned fragments, not correctness of the remaining quotient data. The archive named in the docstring was not read, and no inputs were modified.
