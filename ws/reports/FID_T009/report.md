STATUS: PASS
BLOCKING: 0

DECL: rawClass_10 PASS

This is auxiliary literal data for the supplied projection in Proposition `p:automaton10`, not a separate mathematical assertion. The matching paper contract is `app-input-contracts.tex:367–419`, especially the raw-word/class pairs at lines 382–405 and the regeneration checks at lines 408–417. The raw object is defined at `app-input-contracts.tex:21–34`, and projection compatibility at lines 315–321.

In the actual assembly expression (`Automaton10Data.lean:1551`), this literal occupies bits [12402684, 12419068), contributing to the 1,366 lanes with word codes 1033557–1034922. Exactly 43 of those words are raw windows. Every raw word has a class in 0–3740, every other word has sentinel 3741, and all representative, admissibility, kind, successor, and required arrival comparisons pass. The literal therefore supplies the intended part of the projection.

Checked arithmetic meaning: its type is arbitrary-precision `ℕ`; hexadecimal notation specifies an exact natural number. Natural left shift multiplies by a power of two (`Mathlib/Data/Nat/Size.lean:18`), rather than truncating to a machine word. I parsed the assembly expression and checked each literal fits its allotted bit interval, so addition creates no overlapping-bit carry. The 12-bit lane extraction and word encoding have the meanings detailed in the non-blocking remarks below, including lanes crossing chunk boundaries.

DECL: rawClass_11 PASS

This is the next auxiliary piece of the same supplied projection: `app-input-contracts.tex:367–419`, with raw-window and quotient meanings at lines 21–34 and 315–321. Its assembled bit interval is [12386300, 12402684), touching word codes 1032191–1033556. Of these 1,366 lanes, 321 represent raw windows. All have valid class labels and satisfy the paper's regeneration comparisons; all remaining lanes contain sentinel 3741.

Checked the exact `ℕ` literal, natural shift/addition semantics (`Mathlib/Data/Nat/Size.lean:18`), and Euclidean division/remainder used to extract its lanes. Boundary lanes were decoded from the assembled number, including their bits from adjacent chunks. Thus neither the chunk numbering nor a partial lane introduces a change to the paper's map.

DECL: rawClass_12 PASS

The paper counterpart is again the supplied raw-word/class map and its finite contract, `app-input-contracts.tex:367–419`; its domain and compatibility requirements are at lines 21–34 and 315–321. The literal occupies bits [12369916, 12386300), touching word codes 1030826–1032191. There are 327 raw windows among these 1,366 lanes. Each has an in-range label and passes all representative and transition comparisons; every nonraw lane has sentinel 3741.

Checked exact natural-number notation, the multiplication meaning of natural left shift (`Mathlib/Data/Nat/Size.lean:18`), absence of carries between packed chunks, and 12-bit Euclidean lane extraction. The checks include both chunk boundaries and the paper's most-significant-first direction convention. This is the intended auxiliary data for the declarations consuming it.

DECL: rawClass_13 PASS

This literal supplies part of the map in `p:automaton10`, `app-input-contracts.tex:367–419`, under the raw-window and quotient definitions at lines 21–34 and 315–321. Its assembled bits are [12353532, 12369916), touching word codes 1029461–1030826. The 1,366 affected lanes contain 92 raw windows. Their labels and all required quotient comparisons are correct; the other lanes contain sentinel 3741.

Checked arbitrary-precision `ℕ` arithmetic, left shift as multiplication by a power of two (`Mathlib/Data/Nat/Size.lean:18`), nonoverlapping assembly, and division/remainder extraction, including the partial boundary lane. No change of direction order, domain, or class indexing occurs in this chunk.

DECL: rawClass_14 PASS

This is auxiliary data for the supplied projection specified at `app-input-contracts.tex:367–419`, with the underlying domain and quotient conditions at lines 21–34 and 315–321. It occupies bits [12337148, 12353532), touching word codes 1028095–1029460. Exactly 166 of these 1,366 lanes are raw windows. All valid labels and representative/transition comparisons pass, and every invalid word has sentinel 3741.

Checked the exact natural literal, natural shift/addition semantics (`Mathlib/Data/Nat/Size.lean:18`), chunk bounds, and the 12-bit Euclidean lane interpretation. The affected entries implement the intended map without overflow, truncation, or a degenerate totalization on valid words.

Non-blocking remarks:

- **Scope and context.** I read the whole data file, processing all literal values and packing expressions, and its complete AKLT import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Only the five assigned declarations are judged here. Their consumers are `rawClass`, `rawClassAt`, and `supplied` (`Automaton10Data.lean:1551,1611,1623–1629`), with explicit coverage and correctness obligations in `Blueprint/Top/ComputationV2.lean:13–26`. `private` and `noncomputable` do not add mathematical hypotheses or assume correctness.

- **Domains and geometric meaning.** `DirectionWord 10` is the full function type `Fin 10 → Compass`, with four absolute directions E,N,W,S and integer displacements (1,0),(0,1),(-1,0),(0,-1). Positions are in `ℤ × ℤ`, with coordinatewise addition and no spatial quotient. `RawWindow` requires injectivity of the ten unoriented bonds. Each bond is a `Finset` pair: membership is endpoint membership, and order is irrelevant (`Mathlib/Data/Finset/Insert.lean:365,409–413`). Unit steps ensure the two endpoints are distinct. This is precisely the paper's distinct-bond condition; it imposes no unintended initial-direction restriction. `MemoryWindow` is the subtype of all such words. Its `Fintype.ofFinite` instance enumerates that subtype, rather than selecting a supplied list (`Mathlib/Data/Fintype/EquivFin.lean:175–180`).

- **Encoding and totalization.** The paper fixes E,N,W,S as 0,1,2,3 (`app-input-contracts.tex:219`) and uses most-significant-first coding for this file (lines 376–388). `List.finRange 10` lists every finite index once (`Mathlib/Data/List/FinRange.lean:29–43`). For `i : Fin 10`, natural subtraction `10-1-i.val` equals the intended nonnegative exponent `9-i.val`. Encoding and decoding therefore give the full code domain 0–4^10−1. Lane extraction is natural Euclidean division by `2^(12*code)`, followed by remainder modulo `2^12`; both divisors are positive. There is no division-by-zero or machine-overflow interpretation. Valid labels are below 3741, so `% 3741` in `supplied.project` leaves them unchanged. Sentinel 3741 totalizes only nonraw words, which are outside the paper's map domain. Destination subtraction by one is applied to a positive stored destination whenever a move is allowed; its saturation at zero concerns only disallowed moves.

- **Full finite reconstruction.** The retained checker, `audit_data.py`, independently generates distinct-bond windows in lexicographic direction order as prescribed at `app-input-contracts.tex:232–237,390–401`. It obtains the stated counts 4,12,36,108,316,916,2628,7500,21268,60092. Across all 4^10 codes, labels below 3741 occur exactly on those 60092 raw words; all other labels equal 3741. All 3741 representatives are raw, have codes below 4^10, and map to their own classes, establishing surjectivity without an extra assumption.

- **Compatibility and nonvacuity.** For every raw word and every absolute direction, the checker compares used-bond admissibility and kind with its class representative, including kind on disallowed directions. Revisit means that the endpoint equals an earlier departure vertex, taking precedence over straight/turn, exactly as at `app-input-contracts.tex:31–33`. For each allowed move it also checks stored kind, the projected append-and-forget successor, and final-direction agreement on nonrevisit moves. These implement the quantifiers of lines 315–321 and 408–417. No arrival equality is imposed on classes with only revisit moves. The reconstructed class rows have 2516 straight, 5032 turning, and 1872 revisit edges, as at lines 372–373. There were no coverage, representative, row, or sentinel errors. Detailed results are retained in `audit_results.json`; these are executable finite checks, not a Lean proof.

- **Provenance limit.** The permitted inputs do not include the archived `windows_m10_min.txt` itself. The checks above establish the literals' mathematical reconstruction contract and their suitability for the consuming declarations; they do not independently attest byte-for-byte archive identity or the header's SHA-256.
