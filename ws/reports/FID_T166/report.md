STATUS: PASS
BLOCKING: 0

DECL: rawClassAt PASS

`Automaton10Data.lean:1611` supplies the raw-word class map required by `paper/app-input-contracts.tex:367`–`388` (`p:automaton10` and its reconstruction contract). Its argument is the most-significant-first base-four word code of `app-input-contracts.tex:377`–`380`, with E,N,W,S numbered 0,1,2,3 (`app-input-contracts.tex:219`; `Automaton10Data.lean:1598`–`1609`). `lane rawClass 12 code` uses natural-number Euclidean division and remainder to select bits 12·code through 12·code+11. Natural left shifts in the literal assembly multiply by powers of two; there is no machine-word overflow. Both powers of two in `lane` are positive, so neither division nor remainder has a zero divisor. Mathlib's `Data/Nat/Bitwise.lean:355`–`356` uses precisely this shift/power interpretation.

I evaluated every literal and assembly expression, then independently generated all bond-distinct direction words. Among all 4^10 = 1,048,576 code positions, exactly the 60,092 generated words have class values below 3741; every other position has the sentinel 3741. All valid class values lie in 0,…,3740. Thus this dense representation neither loses raw words nor admits nontrails. `rawClassAt` is an auxiliary total lookup, not a claim that every natural number codes a raw word: its values for codes outside [0,4^10) are irrelevant to its consumers, whose coverage quantifier is `Fin (4^10)` (`Blueprint/Top/ComputationV2.lean:15`–`17`).

DECL: representativeCode PASS

`Automaton10Data.lean:1613` represents the one supplied representative code per class in `paper/app-input-contracts.tex:369`–`370`, `385`, and `404`–`405`. Mathlib's `Fin 3741` means a natural number strictly below 3741, with `.val` its actual zero-based index (`Mathlib/Data/Fin/Basic.lean:16`–`25`, `77`–`78`); no finite-type arithmetic or implicit modular cast enters this lookup. The 20-bit lane accommodates exactly the word-code range 0,…,4^10−1 because 2^20 = 4^10. Its division/modulo denominators are positive.

Exhaustive checking of all 3741 lanes found maximum representative code 1,042,000 < 4^10. Every representative decodes to a generated raw window and its raw class is its own index. The following `decodeWord 10` consequently does not hide an oversized or invalid representative by truncation. This also witnesses the surjectivity demanded by the paper.

DECL: destinationCode PASS

`Automaton10Data.lean:1615`–`1616` is the natural-number encoding of the four successor entries of each class row in `paper/app-input-contracts.tex:385`–`388`. The index `a.val*4 + directionCode d` enumerates each class's E,N,W,S entries, without identifying different absolute directions. A paper successor j ∈ {0,…,3740} is stored as j+1; the paper's inadmissible successor −1 is stored as 0. This is an encoding change with the inverse explicitly applied by `supplied.successor`, not a change in the successor class numbers.

All 14,964 lanes lie in 0,…,3741. For every one of the 60,092 independently generated raw windows and all four directions (240,368 comparisons), nonzero destination is equivalent to the paper's nonreversal and unused-unoriented-bond test (`app-input-contracts.tex:24`–`30`). For all 169,092 admissible raw transitions, subtracting one gives exactly the stored class of the shifted word (d₂,…,d₁₀,d). Thus neither one-based storage nor the E/N/W/S index introduces an offset or sign error. As above, the natural-number lane has no division-by-zero case.

DECL: kindCode PASS

`Automaton10Data.lean:1618`–`1619` extracts the corresponding two-bit kind, with the same class/direction ordering as the successors. This encodes the paper's 0 = straight, 1 = turn, 2 = revisit, and −1 = inadmissible (`paper/app-input-contracts.tex:385`–`388`), using 3 for the inadmissibility sentinel. All lanes are in 0,…,3, and kind 3 occurs exactly when the destination lane is zero. There is no collision with an admitted kind.

Every admitted raw transition has the regenerated kind of `app-input-contracts.tex:31`–`33`: endpoint membership among earlier departure vertices takes precedence over the straight/turn comparison with the last absolute direction. I also checked raw kind compatibility within each class for all four directions, including forbidden directions, as required by `app-input-contracts.tex:317`–`319`. The quotient lane counts are exactly 2516 straight, 5032 turning, 1872 revisit and 5544 inadmissible, agreeing with `p:automaton10` at `app-input-contracts.tex:372`–`373`.

DECL: supplied PASS

`Automaton10Data.lean:1623`–`1629` constructs the particular memory-ten, 3741-class object described in `paper/app-input-contracts.tex:367`–`419`, with the quotient interpretation of `l:automaton-quotient` at `315`–`341`. I checked each field and its domain:

- `project` agrees with the stored zero-based class on every raw word: the checked class is already below 3741, so `% 3741` is the identity. Its extension to nonraw direction words maps their sentinel to class zero. The paper's map is defined on Ω₁₀; correctness in `Automaton.lean:78`–`84` is correspondingly restricted by `RawWindow`.
- `representative` decodes the checked 20-bit representative by the paper's most-significant-first convention. In `encodeWord`/`decodeWord`, `i : Fin 10` gives i.val ≤ 9, so natural subtraction `10-1-i.val` is exactly 9−i.val, without unintended truncation. Mathlib's `List.finRange` enumerates each finite index once and in index order (`Mathlib/Data/List/FinRange.lean:29`–`33`).
- `allowed` uses Boolean natural-number inequality, so it is true exactly for a nonzero successor lane. `kind` maps admitted codes 0,1,2 to the three intended constructors. Its default revisit value for forbidden code 3 is an unused totalization.
- On an admitted edge, `destinationCode-1` is ordinary subtraction from a positive natural and lies below 3741; the subsequent modulo changes nothing. On a forbidden edge, natural subtraction gives 0−1 = 0, so the arbitrary successor is class zero. Correctness only inspects successors of admissible edges, and the backward operators either guard by `allowed` or give such edges coefficient zero (`Computational.lean:33`–`39`; `Stationary.lean:47`–`74`, `171`–`186`). This totalization does not create a transition.
- `arrival` reads the representative code modulo four, exactly its final direction. All 162,372 admitted nonrevisit raw transitions have the same final direction as that representative. There is one class with mixed final directions; every admitted edge of that class is a revisit. This is precisely the permitted exception in `app-input-contracts.tex:320`–`321`, `337`–`341`, rather than an added final-direction assumption.

The underlying raw model has the paper's domain: `DirectionWord 10` is `Fin 10 → Compass`; `Compass.step` is the stated displacement in ℤ² (`Geometry.lean:16`–`35`); and `RawWindow` is injectivity of the unoriented `Finset` bonds (`Automaton.lean:8`–`13`; `Trails.lean:24`–`32`). Finset pair equality forgets endpoint order (Mathlib `Data/Finset/Insert.lean:419`), and repeated vertices remain permitted. `departureCount` counts indices 0,…,9, so the revisit test includes the initial vertex and excludes the current arrival (`Trails.lean:46`–`48`). No first-direction restriction, boundary condition, spatial quotient, or extra self-avoidance condition was added.

The function-space Fintype instance enumerates all functions from the finite index type (Mathlib `Data/Fintype/Pi.lean:133`–`136`), and `Fintype.ofFinite` only supplies an enumeration of the genuine raw subtype (`Data/Fintype/EquivFin.lean:176`–`180`). Neither changes the state set or supplies a correctness assumption. The explicit positive modulus 3741 makes the constructed `Fin` fields inhabited and well bounded; there is no empty-domain or zero-modulus escape. `MemoryQuotient` is data with correctness asserted separately, and `Automaton10StatementV2` explicitly requires this object's raw coverage, representative bounds, sentinel consistency, correctness and edge counts (`Blueprint/Top/ComputationV2.lean:13`–`26`).

Non-blocking remarks:

- Read the complete data file, all transitive local imports (`Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, `Geometry`), and relevant consumers. Only the five assigned declarations are judged here.
- The reproducible numerical audit is `audit_automaton.py`; its output is `audit-results.txt`. It checks all packed entries and reconstructs every raw trail and transition. All checks passed. These checks are independent finite validation, not a Lean kernel proof; no Lean process was launched.
- The permitted inputs provide the embedded literals and the paper's reconstruction contract, rather than the original `windows_m10_min.txt`. The mathematical contract was exhaustively checked; the original archive's byte-for-byte identity and the header's SHA-256 provenance were not independently authenticated. No mismatch was found.
