STATUS: PASS
BLOCKING: 0

DECL: rawClass_115 PASS

This is an auxiliary packed-data limb, not quotient class number 115. Its paper counterpart is its contribution to the supplied map in `paper/app-input-contracts.tex:367–419` (`p:automaton10`), using the raw-window definition at `paper/app-input-contracts.tex:21–34` (`d:memory-automaton`). The paper defines the map only on words with distinct unoriented bonds; its direction coding is most-significant-first, with E,N,W,S numbered 0,1,2,3 (`paper/app-input-contracts.tex:377–388`, and `:219`).

The literal at `lean/AKLT/Defs/Automaton10Data.lean:245` contributes bits [10682364,10698748) of `rawClass`, intersecting exactly word-code lanes 890197 through 891562. Every intersecting lane decodes to 3741, the invalid-word sentinel, and every corresponding word starts S,N. Its first two bonds are therefore the same set, `{(0,0),(0,-1)}`, so it is outside the paper's raw state set regardless of its remaining eight directions. Every bit of this literal agrees with the required sentinel stream, including its partial final lane.

Checked arithmetic and set meanings: the literal has type `ℕ`, an unbounded natural number; it has no machine-word overflow or sign interpretation. Natural left shift multiplies by a power of two (`Mathlib/Data/Nat/Size.lean:18`). The actual concatenation expression at `Automaton10Data.lean:1551` places the complete 16384-bit limb at the stated offset without overlap or carries. `lane` (`:1596`) uses natural-number quotient and remainder, so `rawClassAt` (`:1611`) extracts a 12-bit base-4096 digit, with strictly positive divisor and modulus. This digit-extraction meaning is also expressed by `Mathlib/Data/Nat/Digits/Defs.lean:444–460`. `RawWindow` is injectivity of the indexed `wordBond` function (`Automaton.lean:9–10`); each bond is a `Finset Plane` (`Trails.lean:31–32`). Finset pairs are unordered (`Mathlib/Data/Finset/Insert.lean:419–420`), so traversing a bond backwards really does violate injectivity.

DECL: rawClass_116 PASS

The literal at `lean/AKLT/Defs/Automaton10Data.lean:247` is another auxiliary part of the supplied map of `paper/app-input-contracts.tex:367–419`, rather than a separate paper definition. Its complete 16384 bits occupy [10665980,10682364), intersecting word codes 888831 through 890196. All these fields are exactly 3741; all these words begin S,N and repeat their first unoriented bond. Consequently none belongs to the domain specified at `paper/app-input-contracts.tex:24–29`. The sentinel correctly records their exclusion.

The same checked Mathlib meanings apply: exact `ℕ` arithmetic, shift as multiplication by powers of two (`Mathlib/Data/Nat/Size.lean:18`), quotient/remainder extraction of 12-bit digits, and unordered Finset bonds (`Mathlib/Data/Finset/Insert.lean:419`). This limb begins eight bits into a lane. The check included the shared boundary field with `rawClass_117`, rather than treating this limb as an independently aligned list of class numbers.

DECL: rawClass_117 PASS

The auxiliary literal at `lean/AKLT/Defs/Automaton10Data.lean:249` contributes bits [10649596,10665980), intersecting word codes 887466 through 888831 of the supplied map in `paper/app-input-contracts.tex:367–419`. Every intersecting field is 3741 and every word begins S,N. The repeated first bond excludes every one of these words under `paper/app-input-contracts.tex:24–29`. The entire literal is precisely the appropriate slice of the sentinel stream.

Checked the exact natural-number packing and quotient/remainder meanings described above, including shift multiplication (`Mathlib/Data/Nat/Size.lean:18`) and Finset pair symmetry (`Mathlib/Data/Finset/Insert.lean:419`). Its offset is four bits into a 12-bit lane, and both shared boundary fields were checked using the assembled table. There is no class-number truncation, sign change, or lost boundary digit.

DECL: rawClass_118 PASS

The auxiliary literal at `lean/AKLT/Defs/Automaton10Data.lean:251` occupies bits [10633212,10649596), intersecting word codes 886101 through 887466. It is the corresponding piece of the supplied map of `paper/app-input-contracts.tex:367–419`. All intersecting digits are 3741 and all decoded words begin S,N, hence fail the distinct-unoriented-bond condition at `paper/app-input-contracts.tex:24–29`. Every literal bit matches this exclusion marker, including its partial final field shared with `rawClass_117`.

Checked `ℕ` shift/addition and natural quotient/remainder digit extraction, with positive powers-of-two denominators and moduli; shift has the meaning in `Mathlib/Data/Nat/Size.lean:18`. Checked that the repeated reversed bond is equal as a Finset, using the unordered-pair meaning in `Mathlib/Data/Finset/Insert.lean:419`. Its start is aligned to a 12-bit lane; no assumption that its end is aligned was made.

DECL: rawClass_119 PASS

The auxiliary literal at `lean/AKLT/Defs/Automaton10Data.lean:253` contributes bits [10616828,10633212), intersecting word codes 884735 through 886100. These are entries in the supplied-map representation associated with `paper/app-input-contracts.tex:367–419`. Every affected word starts S,N, so none is in the raw state set at `paper/app-input-contracts.tex:24–29`. All affected table fields equal 3741, and the full 16384-bit literal equals the expected sentinel slice.

Checked unbounded natural arithmetic, shift multiplication (`Mathlib/Data/Nat/Size.lean:18`), and natural division/remainder extraction, including its initial partial field shared with `rawClass_120`. Its offset is eight bits into a lane. Checked unordered Finset bond equality (`Mathlib/Data/Finset/Insert.lean:419`), which makes the first two steps a forbidden repeated bond independently of the suffix. No unintended valid-window exclusion occurs in this limb.

Non-blocking remarks:

- Read the entire data file, processing its large literals programmatically, and the complete project import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Read the consuming `Automaton10StatementV2` and the matching paper definitions and finite reconstruction contract. Judgments above concern only the five assigned declarations.
- The sentinel 3741 fits in 12 bits and lies outside `Fin 3741`, whose values are 0 through 3740. `Automaton10StatementV2` explicitly checks `rawClassAt code < 3741 ↔ RawWindow (decodeWord 10 code)` (`ComputationV2.lean:15–17`). The supplied projection reduces the sentinel modulo 3741 to zero (`Automaton10Data.lean:1624`); this merely extends the map to invalid words. `MemoryQuotient.Correct` guards its word obligations by `RawWindow` (`Automaton.lean:78–84`), so that totalization cannot introduce a raw state or identify valid windows through any of these five chunks.
- The code exponent `m-1-i.val` is exactly `9-i.val` for `i : Fin 10`; natural subtraction does not underflow. `direction` receives a remainder below four and agrees with the paper's absolute compass directions and their signed integer displacements. The assigned literals introduce no hypotheses, quantifiers, extra finiteness assumptions, or rational division. Their use does not depend on the memory-zero totalizations elsewhere in the imported definitions.
- `check_fidelity.py` parses all 786 literal blocks and the complete `rawClass` assembly expression, verifies contiguous nonoverlapping placement of its 768 limbs, checks every assigned bit against the expected sentinel stream, extracts all intersecting lanes including shared boundaries, and independently constructs the corresponding unoriented-bond paths. It passed. No Lean processes were needed, and no inputs were modified. This is a fidelity check of these data declarations, not a proof of all the separate automaton correctness obligations.
