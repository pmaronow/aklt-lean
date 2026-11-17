STATUS: PASS
BLOCKING: 0

DECL: rawClass_390 PASS

`AKLT/Defs/Automaton10Data.lean:795` is an auxiliary natural-number literal, not a separate paper assertion. In the assembled `rawClass` it occupies bits [6176764, 6193148), intersecting code lanes 514730–516095. Its entire 16384-bit value is precisely the corresponding slice of repeated 12-bit sentinel `3741 = 0xE9D`; every intersected lane, including both boundary lanes, decodes to 3741. All these most-significant-first base-four words begin N,S and repeat their first unoriented bond. They therefore lie outside Ω₁₀ by `paper/app-input-contracts.tex:21–34`. The supplied paper map has domain Ω₁₀ (`paper/app-input-contracts.tex:315–321,367–388`), so these sentinel entries correctly extend the table outside its domain. Checked meanings: exact `ℕ` arithmetic, natural left shift, quotient/remainder extraction, and unordered `Finset` bond equality, as detailed below.

DECL: rawClass_391 PASS

`AKLT/Defs/Automaton10Data.lean:797` occupies bits [6160380, 6176764), intersecting code lanes 513365–514730. All 16384 bits match the sentinel pattern in the correct phase, and every intersected assembled lane equals 3741. Every decoded word begins N,S, violating distinctness of unoriented bonds in `paper/app-input-contracts.tex:24–29`. These are excluded words rather than missing or misclassified raw windows; the paper's map and finite reconstruction contract concern Ω₁₀ (`paper/app-input-contracts.tex:367–405`). Exact natural shifts and division/remainder preserve this interpretation, including the lane shared with `rawClass_390`.

DECL: rawClass_392 PASS

`AKLT/Defs/Automaton10Data.lean:799` occupies bits [6143996, 6160380), intersecting code lanes 511999–513364. Its complete literal is the correctly aligned sentinel slice, and all intersected lanes equal 3741. Most-significant-first decoding gives initial directions N,S for every affected word, hence equal first and second unoriented bonds. Thus none belongs to the domain in `paper/app-input-contracts.tex:21–34,315–316`; sentinel padding agrees with the auxiliary representation of the map in `paper/app-input-contracts.tex:367–388`. Checked `ℕ` shift and lane-extraction semantics do not reverse the codes or introduce a valid class number here.

DECL: rawClass_393 PASS

`AKLT/Defs/Automaton10Data.lean:801` occupies bits [6127612, 6143996), intersecting code lanes 510634–511999. Every bit matches the appropriately phased repeated sentinel, and both partial boundary lanes also decode to 3741 in the full table. All affected words begin N,S and fail the paper's distinct-unoriented-bond condition (`paper/app-input-contracts.tex:24–29`). Consequently these entries correctly represent words absent from the paper's raw map (`paper/app-input-contracts.tex:367–405`). Natural arithmetic and unordered bond equality give exactly this exclusion, with no extra hypothesis.

DECL: rawClass_394 PASS

`AKLT/Defs/Automaton10Data.lean:803` occupies bits [6111228, 6127612), intersecting code lanes 509269–510634. The full literal equals its expected sentinel slice; every intersected assembled lane equals 3741. Each word starts N,S, so its first two unoriented bonds coincide. It is outside Ω₁₀ as defined at `paper/app-input-contracts.tex:21–34`, and needs no class assignment under the supplied-map assertion at `paper/app-input-contracts.tex:367–388`. The natural-number packing and boundary extraction correctly implement this out-of-domain padding.

Non-blocking remarks:

- Shared semantic checks: `ℕ` literals and arithmetic are exact, with no machine-word overflow. Natural `<<< s` multiplies by `2^s` (the `Nat.shiftLeft_eq` identity used in Mathlib `Data/Nat/Bits.lean:123–128` and `Data/Nat/Bitwise.lean:355–356`). The fully parenthesized assembly was parsed in full; its literal blocks are contiguous and additions introduce no carries between them. `lane` (`Automaton10Data.lean:1596`) uses natural quotient and remainder with strictly positive divisors `2^(width*index)` and `2^width`.
- `DirectionWord 10` is `Fin 10 → Compass`; the four directions have the stated integer lattice steps (`Defs/Geometry.lean:16–36`, `Defs/Trails.lean:23–32`). For N,S the vertices are (0,0), (0,1), (0,0). The first two bonds are equal because `Finset` pairs are unordered (Mathlib `Data/Finset/Insert.lean:413–420`, especially `Finset.pair_comm`), so `Function.Injective (wordBond (0,0) w)` is false. This matches the paper's exclusion exactly.
- Encoding/decoding (`Automaton10Data.lean:1598–1609`) uses E,N,W,S = 0,1,2,3 and exponent `9-i.val` at memory ten, matching `paper/app-input-contracts.tex:377–388`. Since `i : Fin 10`, the natural subtraction never truncates a negative exponent. Remainder modulo four restricts decoding to the intended four cases. No spatial or sign convention changes the N,S reversal.
- The sentinel is intentional totalization: `rawClassAt` extracts 12-bit entries; `supplied.project` reduces modulo 3741 (`Automaton10Data.lean:1611,1624`), sending sentinel entries to class zero. The paper defines its map only on raw windows. `MemoryQuotient.Correct` restricts its word comparisons to `RawWindow` (`Defs/Automaton.lean:78–84`), while `Automaton10StatementV2` explicitly requires sentinel 3741 precisely on nonraw codes (`Blueprint/Top/ComputationV2.lean:15–17`). These five chunks affect no raw window and cannot discharge those checks vacuously. The finite subtype instance does not assume the correctness of stored data.
- Read the complete data file and its local import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, `Geometry`; inspected the downstream V2 consumer. `check_data.py` independently parses every literal and packing expression, checks every bit of the assigned chunks, and checks all affected assembled lanes against geometric bond distinctness. It passed. No Lean process was needed; inputs were not modified. Findings concern only the five assigned declarations.
