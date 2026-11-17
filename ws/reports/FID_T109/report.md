STATUS: PASS
BLOCKING: 0

DECL: rawClass_510 PASS

`AKLT/Defs/Automaton10Data.lean:1035` is an auxiliary literal for the supplied map in Proposition `p:automaton10`, paper `app-input-contracts.tex:367`, with its reconstruction contract at `app-input-contracts.tex:376–419`. It contributes bits 4,210,684 through 4,227,067 of `rawClass`, touching code lanes 350,890 through 352,255. These include 90 raw windows and 1,276 invalid words. All touched lanes agree with independently regenerated bond validity and the supplied quotient rows. For example, code 350,890 (`NNNNWWWWWW`) maps to class 356. Checked meaning: the hexadecimal literal is an exact `ℕ`, and natural left shift multiplies by a power of two; its 16,384-bit allocation begins and ends within 12-bit lanes. Both boundary fragments reconstruct correctly with the neighboring chunks.

DECL: rawClass_511 PASS

`AKLT/Defs/Automaton10Data.lean:1037` supplies another piece of the same map, specified at paper `app-input-contracts.tex:382–405` and checked against the raw model at `app-input-contracts.tex:408–417`. Its bits 4,194,300 through 4,210,683 touch codes 349,525 through 350,890: 222 raw windows and 1,144 invalid words. For example, code 349,525 (`NNNNNNNNNN`) maps to class 115. All class assignments and their representative/transition obligations pass. Checked meaning: arbitrary-precision natural arithmetic and quotient/remainder lane extraction preserve the first full lane and the final four-bit fragment; no machine-integer truncation or indexing reversal occurs.

DECL: rawClass_512 PASS

`AKLT/Defs/Automaton10Data.lean:1039` represents the map of paper `app-input-contracts.tex:367–388`, under the validity and representative conditions at `app-input-contracts.tex:402–417`. Its bits 4,177,916 through 4,194,299 touch codes 348,159 through 349,524: 311 raw windows and 1,055 invalid words. Code 348,160 (`NNNNEEEEEE`), for example, maps to class 0. Every touched valid code has a class below 3,741 and the correct row behavior. Checked meaning: the leading hexadecimal zero does not alter the natural number; the concatenation allocates the full 16,384 bits. The initial four-bit fragment and final full lane are positioned correctly.

DECL: rawClass_513 PASS

`AKLT/Defs/Automaton10Data.lean:1041` is an auxiliary piece for paper `app-input-contracts.tex:367–419`. Its bits 4,161,532 through 4,177,915 touch codes 346,794 through 348,159: 152 raw windows and 1,214 invalid words. Code 347,136 (`NNNESEEEEE`) maps to class 0, for example. Regenerated raw geometry and all associated representative, admissibility, kind, successor, and required arrival checks agree. Checked meaning: `ℕ` addition and left shift concatenate nonoverlapping bits without overflow or carry into adjacent chunks. The initial and final eight-bit lane fragments agree with the complete lane values.

DECL: rawClass_514 PASS

`AKLT/Defs/Automaton10Data.lean:1043` is another auxiliary piece for the supplied class map, whose coding is fixed at paper `app-input-contracts.tex:376–388` and whose semantic checks are fixed at `app-input-contracts.tex:402–417`. Its bits 4,145,148 through 4,161,531 touch codes 345,429 through 346,794: 96 raw windows and 1,270 invalid words. Code 345,429 (`NNNENNNNNN`) maps to class 115. All touched assignments satisfy the reconstruction contract. Checked meaning: 12-bit natural quotient/remainder lanes are indexed by the most-significant-first word code, while the packed table places lane zero at the least significant end. The first full lane and final four-bit fragment are correct.

Shared verification and non-blocking remarks:

- Read the entire data file, including all literal pieces and concatenation expressions, and its local import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Only the five assigned declarations are judged here. They are closed natural-number definitions with no hypotheses, quantifiers, instance parameters, or direct individual paper counterparts. Their intended role is to encode the particular finite witness consumed by `rawClassAt` and `supplied` (`Automaton10Data.lean:1595–1629`).

- The geometric model matches Definition `d:memory-automaton`, paper `app-input-contracts.tex:21–42`: `Plane` is `ℤ × ℤ`; E,N,W,S have the stated displacements; `DirectionWord 10` is `Fin 10 → Compass`. A bond is a `Finset` of its two endpoints. Mathlib's `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`) confirms that orientation is forgotten. Injectivity of `wordBond` means pairwise distinct bonds, while repeated vertices are permitted. Raw windows impose no designated initial incoming direction. Departure counting at index 10 covers exactly vertices 0 through 9, so an endpoint revisit is detected before straight/turn classification, as the paper requires.

- `List.finRange` enumerates each finite index once (`Mathlib/Data/List/FinRange.lean:29–43`). Consequently `encodeWord` uses digits E=0,N=1,W=2,S=3 and exponent `9-i.val`, exactly paper `app-input-contracts.tex:377–386`. Since `i.val < 10`, natural subtraction cannot underflow. All lane divisors are positive powers of two. Natural left-shift semantics are also used in Mathlib's `Nat.shiftLeft_lt` proof (`Mathlib/Data/Nat/Bitwise.lean:355–356`). The five constants are exact naturals below `2^16384`; none is a signed value or a fixed-width integer.

- `check_data.py` evaluates the actual concatenation expressions, checks absence of overlapping nonzero bits, and independently enumerates paths using distinct unoriented bonds. It obtains the paper's intermediate counts `4,12,36,108,316,916,2628,7500,21268,60092` (`app-input-contracts.tex:393–399`). Across all `4^10` codes, class values are below 3,741 exactly for raw windows; every other value is the sentinel 3,741. Thus `% 3741` in `supplied.project` changes no valid assignment and cannot conceal a bad valid class. Every class has a valid representative mapping back to itself. `Fintype.ofFinite` enumerates the actual finite subtype rather than postulating a list of states (`Mathlib/Data/Fintype/EquivFin.lean:176–180`).

- Every raw word was checked in all four absolute directions against its representative and stored row, including kind equality in inadmissible directions, successor class equality for admitted directions, and arrival equality on non-revisit edges. Successor code is the last nine digits followed by the new direction. Stored destinations encode the paper's class number plus one; zero encodes its `-1` sentinel. Hence natural subtraction of one is exact on admitted edges. The resulting edge counts are exactly 2,516 straight, 5,032 turning, and 1,872 revisit, as required at paper `app-input-contracts.tex:372–373`. All 3,741 classes are inhabited, so these checks are nonvacuous.

- Reconstructing the text witness described at paper `app-input-contracts.tex:382–388` from the decoded map, representatives, destinations, and kinds yields SHA-256 `671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785`, exactly the archive digest documented at `Automaton10Data.lean:6`. This also checks the concrete class numbering. No external archive file was read.

- All checks completed with zero discrepancies; details are retained in `check_results.json`. The Python reconstruction is an external finite check, not a Lean kernel proof. The reviewed definitions claim only literal data, with correctness expressed separately by their consumer. No non-blocking fidelity defect was found.
