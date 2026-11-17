STATUS: PASS
BLOCKING: 0

DECL: rawClass_190 PASS

`AKLT/Defs/Automaton10Data.lean:395` is an auxiliary natural-number literal encoding part of the map in `p:automaton10` (`paper/app-input-contracts.tex:367–419`), rather than a separate mathematical assertion. Its 4,096 hexadecimal digits contribute bits `[9453564,9469948)` of `rawClass`, touching word codes 787797–789162. After assembly, these codes contain 89 raw windows with class numbers below 3741 and 1,277 invalid words with sentinel 3741. Every raw window in this range agrees with its class representative on all the paper's required comparisons.

The arithmetic interpretation used for this and the other four chunks is exact: `ℕ` literals are unbounded natural numbers; `<<<` multiplies by a power of two (`Mathlib/Data/Nat/Size.lean:18`, `Nat.shiftLeft_eq_mul_pow`). The fully parsed assembly at Lean line 1551 places every chunk without overlap or carry. `lane` at line 1596 uses natural-number division and remainder to extract a 12-bit class number. Both divisors are positive powers of two. Boundary lanes were checked after reassembly, so a chunk need not end on a class-number boundary. These checks establish the intended auxiliary object, without adding any hypothesis.

DECL: rawClass_191 PASS

`AKLT/Defs/Automaton10Data.lean:397` supplies bits `[9437180,9453564)`, touching codes 786431–787796. There are 331 valid windows and 1,035 invalid words among these codes; every assembled entry has the required class/sentinel interpretation. This is the same auxiliary map described in `paper/app-input-contracts.tex:382–412`, using the exact natural-number shift, division and remainder semantics described above. In particular, code 786431 straddles this chunk and `rawClass_192`; its assembled class is 218 and passes the representative and transition checks.

The consumer's `% 3741` (`Automaton10Data.lean:1624`) does not alter any valid class number. All 3,741 representatives are actual raw windows and project to their own class. Thus the map into `Fin 3741` really is surjective as required at `paper/app-input-contracts.tex:369–371`; the bounded subtype and modulo cannot conceal an out-of-range valid entry or make the assertion vacuous.

DECL: rawClass_192 PASS

`AKLT/Defs/Automaton10Data.lean:399` supplies bits `[9420796,9437180)`, touching codes 785066–786431. These include 331 valid windows and 1,035 invalid words. Both ends split 12-bit lanes; the actual shifts and additions, including the surrounding chunks, reconstruct every affected lane correctly. The relevant paper contract is `paper/app-input-contracts.tex:376–419`, particularly the raw-map coverage and class-range requirements at lines 402–406.

Checked as a closed `ℕ` definition, the literal carries no assumptions, quantifiers, machine-integer truncation, or hidden finite-instance restriction. Its consumers use ordinary natural-number arithmetic. Each valid entry has the same admissibility and raw kind as its representative for every absolute direction; each admissible successor has the stored class; and each admitted non-revisit edge has the same final direction. These are exactly the conditions of `l:automaton-quotient` at `paper/app-input-contracts.tex:315–341`.

DECL: rawClass_193 PASS

`AKLT/Defs/Automaton10Data.lean:401` supplies bits `[9404412,9420796)`, touching codes 783701–785066: 90 valid windows and 1,276 invalid words. Exact extraction and all representative/transition comparisons passed. The paper counterpart is the supplied raw-code/class map in `paper/app-input-contracts.tex:379–388`, with correctness checks at lines 402–417.

The indexing convention matches the paper: `directionCode` assigns E,N,W,S to 0,1,2,3, and `encodeWord` weights index `i : Fin 10` by `4^(9-i.val)`. `List.finRange` enumerates every such index once (`Mathlib/Data/List/FinRange.lean:29–43`; `Mathlib/Data/Fintype/Basic.lean:37–41`). Since `i.val < 10`, the natural subtraction `10-1-i.val` never underflows. The inverse decoder therefore addresses the intended most-significant-first word, not the different memory-six coding. The exact shift/division interpretation also preserves the partial upper boundary lane.

DECL: rawClass_194 PASS

`AKLT/Defs/Automaton10Data.lean:403` supplies bits `[9388028,9404412)`, touching codes 782335–783700: 201 valid windows and 1,165 invalid words. All affected lanes, including the partial lower lane, satisfy the raw coverage and quotient checks of `paper/app-input-contracts.tex:402–417` under the exact natural-number arithmetic described above.

The regenerated raw object matches `d:memory-automaton` (`paper/app-input-contracts.tex:21–42`). `DirectionWord 10` is the full function type `Fin 10 → Compass`; `Plane` is `ℤ × ℤ`. `RawWindow` requires injectivity of the unordered two-endpoint `Finset` bonds, so reversed traversal repeats the same bond (`Mathlib/Data/Finset/Insert.lean:412–420`, `coe_pair` and `pair_comm`). Unit steps prevent collapsed one-point bonds. Admissibility excludes reversal and all previously used bonds; revisits test the endpoint against departure vertices 0 through 9, before the straight/turn test. The finite subtype instance enumerates these actual raw words and does not assume a supplied state list. Thus the literal describes the intended domain and transition classes.

Non-blocking remarks:

- Read the complete data file and its project import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Only the five assigned declarations are judged here.
- The reproducible exact-integer check is `audit_data.py`; its results are in `audit_results.json`. Running `python3 audit_data.py` passes every assertion. It parses all literal data and assembly operations, independently generates raw trails, and checks all 1,048,576 code lanes. The raw counts at depths 1–10 are 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092, exactly as at `paper/app-input-contracts.tex:395–399`.
- All 240,368 raw-word/direction combinations pass admissibility and representative-kind comparison. All 169,092 admissible raw transitions pass kind, successor, and applicable arrival checks. The quotient edge counts are exactly 2516 straight, 5032 turning, and 1872 revisit (`paper/app-input-contracts.tex:372–373`). Representatives establish nonempty, surjective classes. This checks the actual use of the assigned chunks rather than trusting their names or docstrings.
- The successor's natural subtraction of one is evaluated only on positive stored destinations for admissible edges, so it cannot truncate there. Modulo leaves those valid successor classes unchanged. Invalid-word and inadmissible-edge totalizations are outside the paper's raw automaton; the V2 interface explicitly checks coverage and sentinel ranges (`AKLT/Blueprint/Top/ComputationV2.lean:13–26`).
- This is a semantic fidelity review with exhaustive Python checks, not a Lean kernel proof. The original `windows_m10_min.txt` archive is not among the permitted inputs, so its byte identity and the docstring's archive checksum were not independently authenticated. The supplied literals do satisfy the paper's full finite reconstruction contract relevant to these declarations. No blocking discrepancy was found.
