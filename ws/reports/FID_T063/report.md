STATUS: PASS
BLOCKING: 0

DECL: rawClass_280 PASS

`AKLT/Defs/Automaton10Data.lean:575` is an exact natural-number literal used as a 16,384-bit segment of `rawClass`. The actual assembly at line 1551 places it at bit offset 7,979,004, touching word codes 664917–666282. Every bit equals the corresponding bit of the invalid-word marker 3741, including the partial final lane. All these words begin W,W,E and therefore repeat an unoriented bond. This is correct auxiliary data for the raw-window definition in `app-input-contracts.tex:24` and the supplied map whose domain is Ω₁₀ in `app-input-contracts.tex:367`. The checked natural-number packing and unordered-bond semantics are detailed below.

DECL: rawClass_281 PASS

`AKLT/Defs/Automaton10Data.lean:577` contributes 16,384 bits at offset 7,962,620, touching codes 663551–664916. Its initial bit is bit 8 of a 12-bit lane. The entire literal, including this partial lane, matches repeated markers 3741; the assembled boundary lanes also equal 3741. These words all begin W,W,E, so none belongs to Ω₁₀ (`app-input-contracts.tex:24`). Thus this is appropriate padding outside the supplied map's paper domain (`app-input-contracts.tex:369`), under the exact `Nat` packing and `Finset` bond meanings checked below.

DECL: rawClass_282 PASS

`AKLT/Defs/Automaton10Data.lean:579` contributes 16,384 bits at offset 7,946,236, touching codes 662186–663551, from bit 4 of its first lane through bit 7 of its last. Every stored bit and both assembled boundary lanes agree with marker 3741. Every affected word begins W,W,E and repeats a bond, as excluded by `app-input-contracts.tex:24`. This correctly extends the paper's map on Ω₁₀ (`app-input-contracts.tex:369`) to the total coding table. Exact natural arithmetic and unordered `Finset` equality introduce no alternative interpretation.

DECL: rawClass_283 PASS

`AKLT/Defs/Automaton10Data.lean:581` contributes 16,384 bits at offset 7,929,852, touching codes 660821–662186, starting at a lane boundary and ending at bit 3. Every bit matches marker 3741, and the partially supplied final lane also assembles to 3741. The W,W,E prefix makes every affected word nonraw under `app-input-contracts.tex:24`. The literal is consequently the right auxiliary object for the map in `app-input-contracts.tex:369`; the `Nat` and `Finset` checks below confirm the packing and rejection criteria.

DECL: rawClass_284 PASS

`AKLT/Defs/Automaton10Data.lean:583` contributes 16,384 bits at offset 7,913,468, touching codes 659455–660820, starting at bit 8 of its first lane. All its bits and the assembled boundary lanes equal the appropriate parts of marker 3741. All affected words begin W,W,E, hence fall outside Ω₁₀ (`app-input-contracts.tex:24`). The filler therefore respects the domain of the supplied map (`app-input-contracts.tex:369`), with no numerical overflow, coercion, or bond-orientation discrepancy.

The following semantic checks apply to all five verdicts. The paper numbers E,N,W,S as 0,1,2,3 (`app-input-contracts.tex:219`) and expressly uses most-significant-first coding for this certificate (`app-input-contracts.tex:376`, formula at line 380). Lean's `direction`, `directionCode`, `encodeWord`, and `decodeWord` at `Automaton10Data.lean:1598` implement that convention. For `i : Fin 10`, natural subtraction `10 - 1 - i.val` is exactly `9 - i.val`, with no truncation affecting the exponent. All touched codes are below 4¹⁰ and lie within 655360–671743, the interval with initial base-four digits 220.

For that prefix the first four vertices are (0,0), (-1,0), (-2,0), (-1,0). Bonds at zero-based indices 1 and 2 are respectively {(-1,0),(-2,0)} and {(-2,0),(-1,0)}. `wordVertex` and `wordBond` (`AKLT/Defs/Trails.lean:27` and line 31) compute exactly these vertices and finite sets. Mathlib's `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`) identifies the two bonds. Since the indices are distinct, `Function.Injective (wordBond ...)` is false, exactly as required by `RawWindow` (`AKLT/Defs/Automaton.lean:9`) and the paper's distinct-unoriented-bond condition. No assumption about later steps, incoming direction, or revisit classification is needed.

The hexadecimal literals have type ℕ, so they are exact unbounded integers. Mathlib's `Nat.shiftLeft_eq_mul_pow` (`Mathlib/Data/Nat/Size.lean:18`) states that `x <<< n = x * 2^n`. I parsed the complete assembly expression, checked the offsets of all its constituent chunks, and checked that the additions have no overlapping bits or carries. `lane` (`Automaton10Data.lean:1596`) uses natural quotient and remainder to extract 12 bits. Its denominators 2^(12*code) and 2^12 are positive. Thus there is no division by zero or fixed-width overflow, and 3741 fits in a lane since 3741 < 4096.

Marker 3741 lies outside the paper's class set {0,…,3740}; it is an auxiliary convention for words absent from Ω₁₀, not a new class. `Automaton10StatementV2` (`AKLT/Blueprint/Top/ComputationV2.lean:15`) explicitly requires a value at most 3741 and a value below 3741 exactly for raw words. All affected entries satisfy this obligation. The modulo in `supplied.project` maps these invalid entries to 0, but `MemoryQuotient.Correct` (`AKLT/Defs/Automaton.lean:78`) restricts transition obligations to raw words and separately requires raw representatives. The paper likewise quantifies its map over Ω₁₀ (`app-input-contracts.tex:316`). Consequently this totalization neither weakens a paper obligation nor adds a spurious raw state. The arbitrary finite enumeration chosen by `Fintype.ofFinite` does not alter that subtype; Mathlib defines it as a choice of an existing `Fintype` (`Mathlib/Data/Fintype/EquivFin.lean:179`).

Non-blocking remarks:

- Read the complete target file and its project import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`, plus the consuming V2 automaton statement.
- `python3 check_raw_chunks.py` passes. It checks all 81,920 assigned bits against the expected marker pattern and every touched assembled lane, and independently reconstructs the repeated bonds. No Lean processes were launched; inputs were not modified.
- The five declarations have no separate paper definition: they are private pieces of a total table implementing the paper's partial-domain class map. Their invalid-word padding is faithful to that use; no blocking or other substantive discrepancy was found in these declarations.
