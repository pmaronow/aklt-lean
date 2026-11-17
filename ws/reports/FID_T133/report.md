STATUS: PASS
BLOCKING: 0

DECL: rawClass_630 PASS

This is an auxiliary packed-data fragment (`Automaton10Data.lean:1275`), implementing the supplied map of Proposition `p:automaton10`, rather than a separate paper definition. The paper defines raw windows by distinct unoriented bonds (`app-input-contracts.tex:21–34`) and supplies map rows only for those windows (`app-input-contracts.tex:367–405`). Its word code is most-significant-first (`app-input-contracts.tex:376–388`).

Evaluating the actual assembly expression at `Automaton10Data.lean:1551`, this 16,384-bit fragment occupies bit positions [2244604,2260988), counting from the least significant bit. It intersects 12-bit entries with codes 187050 through 188415, including partial boundary entries. Every bit agrees with the corresponding bits of repeated `3741 = 0xe9d` entries; the complete assembled boundary entries also equal 3741. All these codes begin with base-four digits 0,2, hence directions E,W. Their first two bonds coincide as unoriented sets, so none belongs to the paper's raw state set. The sentinel is therefore correct throughout.

The arithmetic and domain checks used here and below are: `ℕ` literals are exact unbounded natural numbers; `<<<` multiplies by a power of two (`Mathlib/Data/Nat/Size.lean:18`); and `lane` (`Automaton10Data.lean:1596`) uses natural quotient and remainder to select a 12-bit entry. Both powers of two in that extraction are positive. `DirectionWord 10` is `Fin 10 → Compass` (`Trails.lean:24`); `List.finRange` enumerates each index once (`Mathlib/Data/List/FinRange.lean:29`). Thus the coding exponent `10 - 1 - i.val` is exactly 9 minus the index, without truncated-subtraction error. `Compass.step` uses the paper's absolute E,N,W,S vectors (`Geometry.lean:26–30`). Bonds are `Finset Plane` pairs (`Trails.lean:31–32`), whose order is irrelevant by `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`). Accordingly E,W violates the injectivity defining `RawWindow` (`Automaton.lean:9–10`), independently of the remaining eight directions.

DECL: rawClass_631 PASS

This auxiliary fragment (`Automaton10Data.lean:1277`) implements the same paper map and domain (`app-input-contracts.tex:21–34,367–405`). Its actual bit interval is [2228220,2244604), intersecting codes 185685 through 187050. Exact integer checking found only the appropriate bits of the 3741 sentinel, with all complete assembled entries, including shared boundary entries, equal to 3741. Every code has the E,W prefix and therefore repeats its first unoriented bond. The natural-number extraction, finite index range, and unordered-pair meanings checked above apply unchanged; no valid raw window is omitted.

DECL: rawClass_632 PASS

This auxiliary fragment (`Automaton10Data.lean:1279`) occupies [2211836,2228220), intersecting codes 184319 through 185684. For the supplied map restricted to raw windows (`app-input-contracts.tex:367–405`), these must all be absent: their E,W prefix repeats an unoriented bond, contrary to `d:memory-automaton` (`app-input-contracts.tex:24–29`). The literal exactly matches the required sentinel bits, including its partial first entry; every intersected assembled entry is 3741. The checked `ℕ` shift/division/remainder and `Finset` equality semantics give precisely this interpretation, with no overflow or orientation ambiguity.

DECL: rawClass_633 PASS

This auxiliary fragment (`Automaton10Data.lean:1281`) occupies [2195452,2211836), intersecting codes 182954 through 184319. Every affected word starts E,W and is excluded by the paper's distinct-unoriented-bond condition (`app-input-contracts.tex:24–29`), so the supplied-map contract (`app-input-contracts.tex:383–405`) requires no class assignment there. The complete literal equals the appropriate repeated-sentinel bits, and all intersected assembled entries equal 3741. The same exact natural arithmetic and order-independent `Finset` bond comparison establish that this is the correct auxiliary data.

DECL: rawClass_634 PASS

This auxiliary fragment (`Automaton10Data.lean:1283`) occupies [2179068,2195452), intersecting codes 181589 through 182954. All these most-significant-first codes begin E,W and thus lie outside the paper's raw domain (`app-input-contracts.tex:24–29,376–405`). Exact checking of the literal and its assembled boundary entries gives precisely sentinel 3741 throughout. The checked natural-number packing and `Finset` bond semantics introduce no additional states, missing valid states, or side conditions.

Non-blocking remarks:

- The five declarations have no standalone mathematical counterpart; they encode absent rows of the paper's partial raw-to-class table. Sentinel 3741 is outside `Fin 3741`. The consumer explicitly checks `rawClassAt code < 3741 ↔ RawWindow (decodeWord 10 code)` (`Blueprint/Top/ComputationV2.lean:15–17`). Although `supplied.project` maps the sentinel to zero by remainder, correctness is quantified over raw windows (`Automaton.lean:78–84`), so this totalization does not identify any intended raw state with class zero.
- Read the full containing file, processing all literal data and the assembly expression programmatically, and all transitive local imports: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. A Python integer check parsed all 768 raw-class chunks, verified their widths and contiguous, nonoverlapping placement, and checked every bit and intersected assembled entry for the five assigned fragments. No Lean process was needed. The verdict concerns these five declarations only; it does not assert verification of the entire archived quotient or authenticate the archive hash.
