STATUS: PASS
BLOCKING: 0

DECL: rawClass_490 PASS

This is an auxiliary natural-number literal, at `AKLT/Defs/Automaton10Data.lean:995`, implementing part of the map in Proposition `p:automaton10` (`paper/app-input-contracts.tex:367–419`); the paper does not define the individual packed chunks. In the actual assembly at Lean line 1551 it occupies bits [4538364,4554748), intersecting codes 378197–379562. All 1366 intersected words are invalid and their assembled lanes equal the sentinel 3741 (`0xe9d`). In fact each starts N,N,S, repeating its second unoriented bond at step three, so their exclusion agrees with `d:memory-automaton` (`paper/app-input-contracts.tex:21–34`). This sentinel-only chunk is appropriate data, not a vacuous assertion about the raw state set.

Checked meaning: `ℕ` literals are exact unbounded naturals, and `<<<` multiplies by a power of two (`Mathlib/Data/Nat/Size.lean:18`). The literal fits its 16384-bit slot, with no carry into another slot. Actual twelve-bit extraction, including the partial lane at the upper boundary, gives exactly the intended exclusions.

DECL: rawClass_491 PASS

At Lean line 997 this auxiliary literal occupies bits [4521980,4538364), intersecting codes 376831–378196. It affects one valid word and 1365 invalid words. The valid boundary word, code 376831 (NNWSSSSSSS), has assembled class 218; this chunk supplies its high four bits, correctly zero. Every other affected lane is 3741. Thus the literal respects the raw domain and class range required by `paper/app-input-contracts.tex:382–405`. Independent regeneration also confirms its valid member agrees with its representative in admissibility, kinds, successor classes, and required final direction (`paper/app-input-contracts.tex:408–417`).

Checked meaning: natural-number shifts and addition use exact arithmetic, not fixed-width overflow. The low end of this chunk starts eight bits into a lane; extracting twelve-bit lanes from the assembled natural, rather than grouping this literal independently into triples of hex digits, preserves the boundary class. `Fin 3741` has precisely the class numbers 0–3740.

DECL: rawClass_492 PASS

At Lean line 999 this auxiliary literal occupies bits [4505596,4521980), intersecting codes 375466–376831. Of these, 300 words are raw windows and 1066 are invalid. Every valid lane lies in 0–3740 (257 distinct classes here); every invalid lane equals 3741. Every valid member passes all the representative and transition comparisons specified at `paper/app-input-contracts.tex:402–417`, including equality of raw kinds for every absolute direction and final-direction equality on admitted non-revisit transitions. This is the right portion of the map in `p:automaton10` (`paper/app-input-contracts.tex:367–374`).

Checked meaning: the exact natural literal fits its slot; assembly and division/remainder extraction preserve both partial boundary lanes (starting four bits into the lower lane and ending eight bits into the upper lane). Direction codes are E,N,W,S = 0,1,2,3, with most-significant-first word coding, as required by `paper/app-input-contracts.tex:377–388`.

DECL: rawClass_493 PASS

At Lean line 1001 this auxiliary literal occupies bits [4489212,4505596), intersecting codes 374101–375466. There are 96 valid words (96 classes) and 1270 invalid words. All lanes have the required class or sentinel range, and all valid members satisfy the paper's representative, admissibility, kind, successor, and non-revisit arrival comparisons (`paper/app-input-contracts.tex:402–417`). The upper boundary shares the valid code 375466, class 356, with `rawClass_492`; the assembled lane is correct.

Checked meaning: although this literal's significant bit length is 16383, its assembly slot is 16384 bits. The leading zero bit is harmless under exact natural-number shifts. The last partial lane is combined with the adjacent chunk before twelve-bit extraction. This agrees with the supplied class-map object of `p:automaton10` (`paper/app-input-contracts.tex:367–388`).

DECL: rawClass_494 PASS

At Lean line 1003 this auxiliary literal occupies bits [4472828,4489212), intersecting codes 372735–374100. There are 73 valid words (73 classes) and 1293 invalid words. All valid class assignments pass the full reconstruction contract, and every excluded word has sentinel 3741 (`paper/app-input-contracts.tex:402–417`). The lower boundary word, code 372735 (NNWWSSSSSS), has class 218; its high four bits supplied by this chunk are correctly zero.

Checked meaning: the literal fits its exact natural-number shift slot, whose lower boundary starts eight bits into a twelve-bit lane. Division and modulo recover the correct assembled class; there is no signed sentinel or machine-word interpretation. The literal therefore implements the intended part of the supplied quotient in `paper/app-input-contracts.tex:367–388`.

Non-blocking remarks

- Context reviewed: the entire data file, including programmatic inspection of all its literals and assembly expressions, and the complete local import chain `Automaton → Kernel → Trails → Domain → PinModel → Moment → Geometry`. Only the five assigned declarations receive verdicts.
- Domain and geometry: `DirectionWord 10` is `Fin 10 → Compass`; `Plane` is `ℤ × ℤ` with the paper's four distinct signed unit steps. `RawWindow` is injectivity of the map from indices to two-endpoint `Finset`s. `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`) confirms that reversal denotes the same unoriented bond. Unit steps make endpoints distinct. `departureCount` at time ten counts departure vertices 0 through 9, matching the revisit convention in `paper/app-input-contracts.tex:27–33`, rather than counting the terminal arrival itself.
- Coding and totalization: `List.finRange` enumerates each `Fin m` index once (`Mathlib/Data/List/FinRange.lean:29–44`). For `i : Fin 10`, the natural exponent `10 - 1 - i.val` is exactly 9 minus the index, so truncated subtraction causes no change. All divisors and moduli used in lane/word decoding are positive powers of 2 or 4; the projection modulus is the positive number 3741. Projection modulo 3741 leaves valid labels unchanged. Invalid words map to an arbitrary totalized class, but the paper's map has domain only `Ω₁₀` and the Lean correctness obligations explicitly restrict to `RawWindow`. Similarly, truncated successor subtraction at stored zero concerns forbidden directions only; admitted successors store class-plus-one. No extra hypothesis, empty domain, or division-by-zero interpretation is involved.
- Finiteness: `MemoryWindow 10` is the actual subtype of finite direction words. `Fintype.ofFinite` chooses an enumeration of that existing finite type (`Mathlib/Data/Fintype/EquivFin.lean:176–180`); it neither assumes the desired cardinality nor replaces the domain by stored rows. The five closed natural constants have no hidden instance parameters or quantified hypotheses.
- Reproducible computational evidence is in `check_data.py` and `check_results.json`. The check parses the actual shift/add expressions and checks slot bounds, independently generates windows by adjoining unused unoriented bonds as prescribed at `paper/app-input-contracts.tex:232–237,390–401`, and compares all 1,048,576 code lanes. It finds exactly 60,092 raw words, all 3741 representatives valid and mapping to their own classes, zero mismatches across all four directions for every raw word, and edge counts 2516 straight, 5032 turning, 1872 revisit. Shared boundary lanes are counted in each intersecting chunk's figures above.
- This is an exact-integer reconstruction check, not a Lean proof. The archived text file is outside the permitted inputs, so its byte identity and the docstring's SHA-256 were not independently authenticated. The paper's full mathematical reconstruction contract was checked against the supplied Lean data. No input was modified, and no Lean processes or sub-agents were launched.
