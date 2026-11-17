STATUS: PASS
BLOCKING: 0

DECL: rawClass_465 PASS

This private auxiliary constant (Automaton10Data.lean:945) is a slice of the supplied class map in Proposition `p:automaton10`, paper app-input-contracts.tex:367–419, especially the map and reconstruction requirements at lines 380–411. It has no separate paper counterpart. Its role is to supply bits of `rawClass`, decoded by `rawClassAt` and used by `supplied.project` (Automaton10Data.lean:1551, 1596, 1611, 1624).

The declared type is the unbounded natural numbers, so its hexadecimal literal is exact. Natural-number left shift multiplies by a power of two; it does not truncate as a machine word would (Mathlib/Data/Nat/Bitwise.lean:355–356, using `Nat.shiftLeft_eq`). Parsing the actual assembly places this slice at bit positions [4947964, 4964348). The 1366 intersecting 12-bit lanes have codes 412330–413695: 72 are raw windows and 1294 are invalid words. Exhaustive reconstruction found precisely these valid words, valid class numbers for all 72, and sentinel 3741 for all invalid words. Their class representatives, admissibility, kinds, successors and required final directions agree with the paper's rules at app-input-contracts.tex:21–35, 315–325, 408–417. No discrepancy was found, including lanes crossing slice boundaries.

DECL: rawClass_466 PASS

This exact natural-number literal (Automaton10Data.lean:947) supplies the next slice of the same map required by paper app-input-contracts.tex:367–419. In the assembled integer its allocated bit positions are [4931580, 4947964), intersecting codes 410965–412330. These 1366 lanes contain 96 raw windows and 1270 invalid words. Independent generation by distinct unoriented bonds agrees with every lane's classification. All valid images satisfy the supplied representative and transition requirements at paper app-input-contracts.tex:402–417; all invalid images are sentinel 3741.

The meaning checked is exact `ℕ` arithmetic: shifts and addition concatenate these bounded slices without overlapping carries, and `packed / 2^(12*code) % 2^12` extracts the intended lane. The divisor and modulus are positive. The quotient domain `Fin 3741` is exactly 0–3740, so projection modulo 3741 leaves each valid image unchanged. Boundary lanes were checked after assembling the complete integer, rather than interpreting this slice as independently aligned 12-bit values.

DECL: rawClass_467 PASS

This auxiliary literal (Automaton10Data.lean:949) also implements the map of paper app-input-contracts.tex:367–419. Its allocated bit positions are [4915196, 4931580), intersecting codes 409599–410964. All 1366 affected lanes were checked: 303 are raw windows, occupying 261 distinct classes, and 1063 are invalid words. Every class assignment passes the representative, labelled successor, kind and non-revisit arrival comparisons required at paper app-input-contracts.tex:408–417. Invalid words have sentinel 3741.

Its leading hexadecimal zero is harmless: a natural literal denotes its numerical value, while the surrounding shifts preserve the allocated slice width. No signed interpretation, overflow, or lost padding is introduced. The actual 12-bit extraction, including partial lanes at the slice boundaries, matches the paper's most-significant-first direction-word encoding at app-input-contracts.tex:376–386.

DECL: rawClass_468 PASS

This auxiliary natural literal (Automaton10Data.lean:951) contributes bits [4898812, 4915196), intersecting codes 408234–409599. All 1366 affected words are invalid, and every reconstructed lane is exactly 3741. This is the correct extension of the paper's map, whose domain is only the distinct-bond windows `Ω₁₀` (app-input-contracts.tex:24–29, 383–405).

These codes run from base-four 1203222222 through 1203333333. Each begins N,W,E, so its third step reverses its second step and repeats the same unoriented bond. In Lean, `wordBond` is a two-element `Finset` of vertices, and `RawWindow` requires injectivity of these bond values. `Finset.pair_comm` (Mathlib/Data/Finset/Insert.lean:419–420) confirms that reversal gives the same bond. Thus the invalid-only slice is intended, rather than a vacuous encoding of valid states. The sentinel is checked before the separate totalization to `Fin 3741`.

DECL: rawClass_469 PASS

This auxiliary natural literal (Automaton10Data.lean:953) contributes bits [4882428, 4898812), intersecting codes 406869–408234. All 1366 affected lanes are correctly sentinel 3741. Their words run from base-four 1203111111 through 1203222222 and again begin N,W,E, necessarily reusing an unoriented bond. Hence none belongs to the domain specified at paper app-input-contracts.tex:24–29, 383–405.

The `ℕ` literal, shifts and lane extraction retain the sentinel exactly, including the boundary shared with the adjacent slice. The paper supplies no class for these invalid words. The extension therefore imposes no additional mathematical condition on its class map. `Automaton10StatementV2` separately requires `rawClassAt code < 3741 ↔ RawWindow (decodeWord 10 code)` (ComputationV2.lean:15–17); these lanes satisfy that requirement.

Non-blocking remarks:

- Read the entire Automaton10Data.lean file, processing every literal and assembly expression, and all its transitive project imports: Automaton, Kernel, Trails, Domain, PinModel, Moment and Geometry. Judgments above concern only the five assigned declarations.
- The reproducible check is `python3 audit_data.py` in this directory. It reads only the supplied Lean data and uses independent lattice-path generation. It checked all 1,048,576 code lanes, exactly 60,092 raw windows, all 3741 representatives, all 14,964 stored class/direction slots, and 240,368 raw-word/direction comparisons. There were zero coverage or transition errors. The regenerated quotient has exactly 2516 straight, 5032 turning and 1872 revisit edges, matching app-input-contracts.tex:372–373. It also checked equality of raw kinds within each class for every direction, including inadmissible ones, as in the lemma at lines 317–319.
- Domain and convention checks: `DirectionWord 10 = Fin 10 → Compass`; positions are in `ℤ × ℤ`; the direction codes are E=0, N=1, W=2, S=3, with the paper's unit displacements. `List.finRange` enumerates each index once (Mathlib/Data/List/FinRange.lean:29–33). Since `i < 10`, the natural subtraction `10 - 1 - i` is precisely the intended exponent 9−i. Decoding uses positive powers of four and remainder modulo four, so its default direction case only receives 3. At memory ten, arrival is index 9 and successor drops index 0 and appends the new direction. A revisit uses earlier departure vertices at indices 0–9, with priority over straight/turn, exactly as in app-input-contracts.tex:26–33.
- Finiteness introduces no additional hypothesis or spatial quotient. `Fintype.ofFinite` chooses an enumeration of the actual subtype (Mathlib/Data/Fintype/EquivFin.lean:176–180); finite-function cardinality has its ordinary meaning (Mathlib/Data/Fintype/BigOperators.lean:139–140), and `Fin 3741` has 3741 elements (Mathlib/Data/Fintype/Card.lean:497). Quantification in the checks covers every raw word and all four absolute directions, with final-direction equality required whenever an admitted transition is not a revisit. The assigned definitions themselves are closed constants with no hypotheses or instance parameters.
- Sentinel 3741 lies outside the valid class range and below 2^12. Projection modulo 3741 and the successor's natural subtraction do not change valid data: raw images are below 3741, and admitted stored destinations are class number plus one. Invalid-word projections and inadmissible successors are totalized outside the paper's domain of use. Neither division by zero nor truncated subtraction affects a relevant entry.
- The original `windows_m10_min.txt` archive is not among the permitted inputs, so byte-for-byte archive provenance and its claimed hash were not checked. The supplied Lean map's mathematical contract was checked directly. The Python audit is independent computational evidence, not a Lean kernel proof. No Lean processes were launched and no inputs were modified.
