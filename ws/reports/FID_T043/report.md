STATUS: PASS
BLOCKING: 0

DECL: rawClass_180 PASS

This is an auxiliary literal block of the class map in Proposition `p:automaton10`, rather than a separate mathematical assertion. The relevant paper contract is `paper/app-input-contracts.tex:367` (raw windows, classes and edge counts), `:376` (most-significant-first encoding), and `:402` (coverage, representatives and regenerated rows). The declaration is at `AKLT/Defs/Automaton10Data.lean:375`.

Its 16,384 bits start at bit 9,617,404 of `rawClass` and intersect code lanes 801450–802815, including two partial boundary lanes. Of these 1,366 words, 321 are raw windows and 1,045 are invalid. Every valid entry is a class in 0–3740 and agrees with the representative's admissibility, kind, successor class and required arrival direction; every invalid entry is sentinel 3741. For example, code 801450 (`SEESWWWWWW`) maps to class 356. Checked the actual natural-number shift/add assembly and Euclidean division/remainder extraction, including the boundary shared with `rawClass_181`; no fixed-width overflow or lane misalignment occurs. The relevant Mathlib identity is `Mathlib/Data/Nat/Size.lean:18`, `n <<< k = n * 2^k`.

DECL: rawClass_181 PASS

This block (`AKLT/Defs/Automaton10Data.lean:377`) supplies the same auxiliary class map required by `paper/app-input-contracts.tex:367`, `:376`, and `:402–417`. Its 16,384 bits start at bit 9,601,020 and intersect code lanes 800085–801450. There are 43 raw windows and 1,323 invalid words in that interval. All 43 valid class assignments satisfy the regenerated quotient checks; the other lanes equal 3741. For example, code 801088 (`SEESWNNEEE`) maps to class 843.

Checked natural-number shifts as multiplication by powers of two (`Mathlib/Data/Nat/Size.lean:18`) and `lane` as extraction of an unsigned 12-bit digit. The upper boundary contributes only four bits to code 801450; combining it with `rawClass_180` gives the correct class 356. Sentinel values are outside the paper's raw domain and cannot satisfy the consumer's raw-coverage test.

DECL: rawClass_182 PASS

This block (`AKLT/Defs/Automaton10Data.lean:379`) is appropriate data for the map in `paper/app-input-contracts.tex:367–419`. Its 16,384 bits start at bit 9,584,636 and intersect code lanes 798719–800084. There are 207 raw windows and 1,159 invalid words. Every valid entry passes the class/representative and transition comparisons prescribed at `:408–415`; every invalid entry is 3741. For example, code 798720 (`SEESEEEEEE`) maps to class 0, which is a legitimate class number.

Checked the unsigned natural-number interpretation and shift identity (`Mathlib/Data/Nat/Size.lean:18`), including its partial low boundary lane, code 798719. Raw validity uses injectivity of unordered endpoint pairs, matching the paper's distinct unoriented bonds (`paper/app-input-contracts.tex:24–29`); `Finset` endpoint order is immaterial (`Mathlib/Data/Finset/Insert.lean:419`). There is no accidental exclusion of class zero.

DECL: rawClass_183 PASS

This block (`AKLT/Defs/Automaton10Data.lean:381`) is correct auxiliary padding for the raw-domain contract in `paper/app-input-contracts.tex:24–29` and `:402–406`. Its 16,384 bits start at bit 9,568,252 and intersect code lanes 797354–798719. All 1,366 affected words begin `SEEW`; their third and fourth steps immediately traverse the same bond in opposite directions. Thus none belongs to the paper's raw state set, and every assembled lane correctly equals sentinel 3741.

Checked that the repeating hexadecimal pattern is aligned as 12-bit digits after assembly, including both partial boundary lanes. Natural shifts have unbounded multiplication semantics (`Mathlib/Data/Nat/Size.lean:18`); `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`) ensures the reversed traversal really violates `RawWindow` injectivity. This block does not remove any genuine state or make the quotient checks vacuous.

DECL: rawClass_184 PASS

This block (`AKLT/Defs/Automaton10Data.lean:383`) also correctly encodes words outside the raw domain of `paper/app-input-contracts.tex:24–29`, as required by the map-coverage contract at `:402–406`. Its 16,384 bits start at bit 9,551,868 and intersect code lanes 795989–797354. All 1,366 words begin `SEEW`, so each repeats the third bond at the fourth step. Every assembled lane is 3741.

Checked unsigned natural-number packing (`Mathlib/Data/Nat/Size.lean:18`) and the upper four-bit boundary contribution shared with `rawClass_183`. Unordered-bond equality is genuine finite-set equality (`Mathlib/Data/Finset/Defs.lean:147`; `Mathlib/Data/Finset/Insert.lean:419`). The sentinel therefore describes precisely invalid words in this region, with no degenerate interpretation of valid windows.

Non-blocking remarks:

- Read the entire target file, decoding all literal blocks and parsing all assembly expressions. Read its complete local import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Inspected the direct semantic consumer, `AKLT/Blueprint/Top/ComputationV2.lean:13–26`. Only the five assigned declarations are judged here.
- The independent reconstruction in `audit_automaton10.py` exhaustively checked all 1,048,576 direction codes for raw coverage, all 3,741 representatives, and all 240,368 raw direction comparisons. It reproduced the paper's intermediate window counts and edge counts (2516 straight, 5032 turn, 1872 revisit), with zero discrepancies. Results are in `audit_results.json`. No Lean processes were launched; these are reproducible arithmetic checks, not a claimed Lean proof.
- `DirectionWord 10` is the full function type `Fin 10 → Compass`. Directions have the absolute displacements E=(1,0), N=(0,1), W=(-1,0), S=(0,-1) in `ℤ × ℤ`; no spatial quotient or virtual initial bond enters `RawWindow`. `Function.Injective (wordBond (0,0) w)` excludes exactly repeated unoriented bonds. `Finset` membership/extensional equality and pair commutativity were checked in `Mathlib/Data/Finset/Insert.lean:74`, `:365`, `:419`, and `Mathlib/Data/Finset/Defs.lean:147`.
- `encodeWord` uses every index exactly once (`Mathlib/Data/List/FinRange.lean:29`). Since `i.val < 10`, its natural subtraction `10 - 1 - i.val` is exactly 9−i, with no underflow. Encoding and decoding therefore match the paper's most-significant-first convention. Lane divisors `2^(12*code)` and moduli `2^12` are positive. All five literals are ordinary unbounded naturals, with no hypotheses, hidden coercions, sign extension, or proof assumptions.
- On raw words, `% 3741` in `supplied.project` is the identity because the extracted class is already below 3741. Invalid words map to class zero only as a totalization outside the paper's domain; `Automaton10StatementV2` separately checks that precisely those words have sentinel 3741. Likewise, stored successor zero and kind 3 encode an inadmissible direction; on admitted directions, subtracting one recovers the actual class without natural underflow. Boolean admissibility is tested as equality to `true`. Representatives witness every class, and all non-revisit arrival comparisons were checked. Thus the ambient total functions add no mathematical side condition on raw windows.
- The finite state set is the actual subtype of raw words, with its finite instance supplied by `Fintype.ofFinite`; it is not a trusted list of states. `Fintype.card` counts its elements (`Mathlib/Data/Fintype/Card.lean:39–50`), so no choice of enumeration changes the meaning. Labelled edges retain each absolute direction separately, without division by class size, as required by `paper/app-input-contracts.tex:343–356`.
- The paper specifies the reconstruction contract but does not print these hexadecimal blocks. Their suitability was checked against that complete mathematical contract. Byte-for-byte identity with the separately named archive and its SHA-256 was not independently checked, since the archive is outside the supplied inputs. The checked counts and quotient properties do not rely on the provenance comment.
