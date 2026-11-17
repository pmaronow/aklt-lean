STATUS: PASS
BLOCKING: 0

DECL: rawClass_370 PASS

Auxiliary packed data at `AKLT/Defs/Automaton10Data.lean:755`, implementing the supplied raw-window map of `p:automaton10` (`paper/app-input-contracts.tex:367–405`). Its 16,384 bits start at bit offset 6,504,444 in `rawClass` and touch word codes 542,037–543,402. Every code begins W,E, so its first two unoriented bonds coincide; it is excluded by `d:memory-automaton` (`paper/app-input-contracts.tex:21–34`). The entire literal equals the correctly aligned bits of the invalid-word marker `3741 = 0xe9d`. Mathlib's natural-number shifts and division give the stated offsets and lanes, and its unordered `Finset` bond equality makes this rejection exact; see the common checks below.

DECL: rawClass_371 PASS

Auxiliary packed data at `AKLT/Defs/Automaton10Data.lean:757`, supporting `p:automaton10` (`paper/app-input-contracts.tex:367–405`). Its 16,384 bits start at offset 6,488,060 and touch codes 540,671–542,036. All these words begin W,E and reuse their first unoriented bond, violating precisely the paper's raw-window condition (`paper/app-input-contracts.tex:24–26`). The literal is exactly the marker bit pattern, with the required eight-bit offset inside its first 12-bit lane. Full boundary lanes also equal 3741. Natural-number shift/division and `Finset` meanings were checked as below.

DECL: rawClass_372 PASS

Auxiliary packed data at `AKLT/Defs/Automaton10Data.lean:759`, supporting `p:automaton10` (`paper/app-input-contracts.tex:367–405`). Its 16,384 bits start at offset 6,471,676 and touch codes 539,306–540,671. Each word starts W,E and therefore fails the distinct-unoriented-bond requirement (`paper/app-input-contracts.tex:24–26`). Every literal bit matches marker 3741, with the required four-bit offset inside the first lane; the complete boundary lanes match too. Mathlib's exact natural arithmetic and unordered finite-set equality justify the extraction and invalidity checks below.

DECL: rawClass_373 PASS

Auxiliary packed data at `AKLT/Defs/Automaton10Data.lean:761`, supporting `p:automaton10` (`paper/app-input-contracts.tex:367–405`). Its 16,384 bits start at offset 6,455,292 and touch codes 537,941–539,306. These are all W,E-prefixed words with a repeated first bond, excluded by `d:memory-automaton` (`paper/app-input-contracts.tex:21–34`). Its complete bit pattern, beginning at a 12-bit lane boundary, correctly records marker 3741; the final partial lane was checked in the assembled table. Mathlib shift/division and `Finset` semantics are as detailed below.

DECL: rawClass_374 PASS

Auxiliary packed data at `AKLT/Defs/Automaton10Data.lean:763`, supporting `p:automaton10` (`paper/app-input-contracts.tex:367–405`). Its 16,384 bits start at offset 6,438,908 and touch codes 536,575–537,940. Every decoded word begins W,E and repeats the first unoriented bond, exactly the obstruction in `paper/app-input-contracts.tex:24–26`. The entire literal is the correctly aligned marker pattern, starting eight bits into a lane. Both complete boundary entries equal 3741. The checked natural-number and finite-set interpretations below apply without additional assumptions.

Common semantic and arithmetic checks:

- Read the complete data file, parsing all 786 hexadecimal literals and the complete `rawClass` assembly expression, and read its AKLT import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. The five assigned declarations are private definitions of exact, unbounded natural numbers. They have no hypotheses, casts, division, instance parameters, or correctness axioms. `noncomputable` does not change their values.
- In `rawClass` (`Automaton10Data.lean:1551`), all 768 fragments occupy disjoint, contiguous bit intervals. Addition introduces no carries between fragments. Mathlib's `Nat.shiftLeft_eq_mul_pow` (`Mathlib/Data/Nat/Size.lean:18`) states `m <<< n = m * 2^n`; these are ordinary natural numbers, without machine-word overflow.
- `lane` (`Automaton10Data.lean:1596`) uses natural-number quotient and remainder: division by `2^(12*code)` followed by reduction modulo 4096 extracts exactly bits `12*code` through `12*code+11`. Both divisors are positive. Checked all fragment bits and every touched full lane, including lanes shared with neighboring fragments: all 6,828 distinct affected codes have value 3741.
- The paper numbers E,N,W,S by 0,1,2,3 (`paper/app-input-contracts.tex:219`) and uses most-significant-first coding for this archive (`paper/app-input-contracts.tex:376–388`). Lean's direction maps and `encodeWord`/`decodeWord` agree (`Automaton10Data.lean:1598–1609`). `List.finRange` enumerates each `Fin m` index once (`Mathlib/Data/List/FinRange.lean:28–40`). For `m = 10`, `m-1-i.val` is exactly `9-i.val`, with no unintended natural-subtraction truncation. Every affected code lies below `4^10` and has leading base-four digits 2,0. The decoder's remainder lies in 0–3, so its default branch means precisely S.
- `Plane` is the ambient `ℤ × ℤ`, with W = (-1,0) and E = (1,0) (`Geometry.lean:8,25–29`). Hence these words have vertices `(0,0), (-1,0), (0,0)` initially. `wordBond` is a `Finset` of endpoints (`Trails.lean:31–32`); `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`) identifies the two bonds. Thus `Function.Injective (wordBond (0,0) w)` fails at the distinct indices 0 and 1 of `Fin 10`. This is the paper's unoriented-bond obstruction, independent of the remaining eight directions.
- Marker 3741 lies outside the paper's class set 0–3740. The paper's map has domain only `Ω₁₀` (`paper/app-input-contracts.tex:369,382–405`); dense-table markers outside that domain are an auxiliary representation. `Automaton10StatementV2` checks the original lane value before any modulo: value at most 3741, and value below 3741 exactly for raw windows (`AKLT/Blueprint/Top/ComputationV2.lean:13–17`). Thus every assigned entry satisfies this coverage condition. `supplied.project` maps the marker modulo 3741 to class zero, but `MemoryQuotient.Correct` restricts its raw-word obligations to `RawWindow` and requires raw representatives (`Automaton.lean:78–84`). This total extension neither changes the paper's map on its domain nor removes a coverage obligation.

Non-blocking remarks:

These five fragments have no individual paper counterpart; their role is to represent invalid-word entries in the supplied map's dense lookup table. Their correctness follows independently from the paper's raw-window definition and coding convention. The reproducible check is `audit_check.py` in this directory; it completed successfully using Python integer arithmetic. No Lean processes were run, and inputs were unchanged.
