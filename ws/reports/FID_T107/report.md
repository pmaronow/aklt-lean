STATUS: PASS
BLOCKING: 0

DECL: rawClass_500 PASS

`AKLT/Defs/Automaton10Data.lean:1015`. This is an auxiliary packed-data constant, not a separate proposition in the paper. Its intended object is the supplied class map of `p:automaton10`, specified in `paper/app-input-contracts.tex:367–419`, on the raw windows of `d:memory-automaton` (`paper/app-input-contracts.tex:21–34`). The most-significant-first word coding and absolute E,N,W,S order agree with `paper/app-input-contracts.tex:376–388`.

The literal has type `ℕ`, so it is an exact nonnegative integer with no machine-width truncation. In the actual `rawClass` assembly it occupies bits 4,374,524–4,390,907, numbering from zero at the least significant bit. These bits intersect 12-bit lanes for codes 364,543–365,908; codes 364,544–365,908 are complete lanes. Independently generating paths with distinct unoriented bonds finds 270 valid words in this range, assigned to 229 classes, and 1,096 invalid words. All valid entries are below 3,741 and have the required representative, admissibility, kind, successor and conditional final-direction behavior; every invalid entry is the sentinel 3,741, including the shared boundary lane. Thus this chunk supplies the correct object for `rawClassAt`, `supplied.project` and `Automaton10StatementV2`.

The arithmetic interpretation used here is `Nat` left shift as multiplication by a power of two (`Mathlib/Data/Nat/Size.lean:18`) and natural-number division/remainder in `lane` (`Automaton10Data.lean:1596`). No division by zero occurs, and the adjacent chunks neither overlap nor produce carries into these bits.

DECL: rawClass_501 PASS

`AKLT/Defs/Automaton10Data.lean:1017`. This auxiliary chunk serves the same supplied-map contract, `paper/app-input-contracts.tex:367–419`, with domain defined at `paper/app-input-contracts.tex:24–29`. Its exact `ℕ` value occupies assembled bits 4,358,140–4,374,523 and intersects codes 363,178–364,543. All 1,366 words have prefix NNWE: the fourth step immediately reverses the third and repeats its unoriented bond. None belongs to the paper's raw domain.

Using the exact `Nat` shift and division/remainder meanings above, every contributed bit agrees with the 12-bit invalid-word sentinel `0xe9d = 3741`. Both boundary lanes were checked after assembly, rather than treating this 16,384-bit chunk as an integral number of 12-bit entries. The sentinel is outside `Fin 3741`; it is correctly excluded by the raw-coverage predicate before the quotient's totalization matters. There is no missing valid raw window or unintended raw class here.

DECL: rawClass_502 PASS

`AKLT/Defs/Automaton10Data.lean:1019`. The paper counterpart is again the auxiliary encoding of the map in `paper/app-input-contracts.tex:367–419`, on distinct-unoriented-bond words (`paper/app-input-contracts.tex:24–29`). Its assembled bit interval is 4,341,756–4,358,139, intersecting codes 361,813–363,178. Every one of these 1,366 words has prefix NNWE and is invalid because W followed by E reuses a bond.

The literal is an exact `ℕ`, not a bounded bit-vector. Applying `Nat` shift as multiplication and `lane` as floor division followed by remainder gives precisely the sentinel 3,741 throughout this interval. The low four bits of boundary code 363,178 supplied here agree with its remaining bits in `rawClass_501`. This correctly implements an absent raw-map row and introduces no condition on genuine windows.

DECL: rawClass_503 PASS

`AKLT/Defs/Automaton10Data.lean:1021`. This auxiliary value is consistent with the map reconstruction at `paper/app-input-contracts.tex:376–419` and the domain at `paper/app-input-contracts.tex:24–29`. Its assembled bits 4,325,372–4,341,755 intersect codes 360,447–361,812. Code 360,447 has prefix NNNS; the remaining codes have prefix NNWE. Respectively, N followed by S or W followed by E repeats a bond, so all 1,366 words are outside the raw domain.

Exact natural arithmetic, with shifts interpreted by `Nat.shiftLeft_eq_mul_pow` and extraction by `lane`, yields the correctly aligned sentinel bits `0xe9d` throughout. This includes the high four bits of code 360,447 shared with `rawClass_504`. The different hexadecimal phase from the neighboring literals is the required consequence of splitting 12-bit entries at 16,384-bit boundaries, not a change in sentinel value.

DECL: rawClass_504 PASS

`AKLT/Defs/Automaton10Data.lean:1023`. Its role is the supplied-map encoding of `paper/app-input-contracts.tex:367–419`, whose domain excludes repeated unoriented bonds (`paper/app-input-contracts.tex:24–29`). Its assembled bits 4,308,988–4,325,371 intersect codes 359,082–360,447. All 1,366 words have prefix NNNS and immediately reverse the third step at the fourth step. Therefore all must be marked invalid.

Under the checked exact `ℕ`, shift, division and remainder meanings, every bit supplied by this literal has the correct phase for sentinel 3,741. The partially shared first and last lanes also decode correctly. Its equality as a literal to `rawClass_501` is appropriate: both offsets have the same residue modulo 12, and both intervals consist entirely of invalid words. It neither removes nor identifies any valid raw state.

Non-blocking remarks and verification details:

- Read the entire data file, processing all literal constants and the actual assembly expressions, and all its local transitive imports: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Only the five assigned declarations receive verdicts.
- `Plane` is the integer plane, and the four compass steps and reversals are the paper's absolute directions. `wordBond` is a `Finset` pair: endpoint order is immaterial (`Mathlib/Data/Finset/Insert.lean:413–420`). Its injectivity therefore means distinct unoriented bonds, without a spatial quotient. Departure counting uses indices 0 through 9, excluding the endpoint at time 10, exactly as the revisit test at `paper/app-input-contracts.tex:31–33` requires.
- `DirectionWord 10` is the full function type `Fin 10 → Compass`. `List.finRange` includes each index once (`Mathlib/Data/List/FinRange.lean:28–33`), and the exponent `10 - 1 - i.val` is exactly `9 - i.val` for these indices: natural subtraction does not collapse any intended exponent. The coding and decoding are inverse on codes below `4^10`. All powers used as divisors are positive. `Fin 3741` contains exactly classes 0 through 3,740; the finite subtype instance for raw windows enumerates the actual predicate and imposes no additional hypothesis.
- Modulo 3,741 in `supplied.project` leaves every valid raw entry unchanged. The sentinel maps to zero only on words outside `RawWindow`, as permitted for this total auxiliary function. On admitted edges the destination is between 1 and 3,741, so destination-minus-one has no natural-subtraction underflow; the zero case only totalizes inadmissible edges. The direction fallback is never used outside 0–3 after decoding. Memory-zero conventions are irrelevant at fixed memory ten. These totalizations do not make the consumers vacuous.
- `audit_tables.py` independently regenerates the paper's unused-bond recursion (`paper/app-input-contracts.tex:232–237,390–401`) and evaluates the literal assembly with exact integer arithmetic. It reproduced counts 4, 12, 36, 108, 316, 916, 2,628, 7,500, 21,268, 60,092. All 1,048,576 raw-code lanes satisfy the validity/sentinel test. All 3,741 representatives are valid and map to their own classes. Every raw word agrees with its representative on admissibility and kind in all four directions; all 169,092 admitted raw edges have the stored successor and kind, with the required final direction on all 162,372 non-revisit edges. Quotient edge counts are 2,516 straight, 5,032 turning and 1,872 revisit, as in `paper/app-input-contracts.tex:372–373`. This also checks the paper's kind-compatibility condition on inadmissible directions, beyond the admitted-edge check in Lean's `Correct` consumer. Results are recorded in `audit_results.json`.
- Verification was computational and semantic, not a new kernel-checked Lean proof. The referenced `windows_m10_min.txt` archive is not among the permitted inputs, so its byte identity and the docstring's archive checksum were not independently authenticated. The auxiliary-data verdicts rest on the decoded table satisfying the independently reconstructed mathematical contract. No minimality requirement was inferred: the paper explicitly disclaims one at `paper/app-input-contracts.tex:418–419`.
