STATUS: PASS
BLOCKING: 0

DECL: rawClass_5 PASS

`AKLT/Defs/Automaton10Data.lean:25` is an auxiliary natural-number literal, not a proposition or an independently defined class. It supplies 16,384 bits of the dense encoding of the map in Proposition `p:automaton10` (paper `app-input-contracts.tex:367–419`). Its bits occupy positions 12,484,604 through 12,500,987 of `rawClass` and touch word codes 1,040,383 through 1,041,748. Decoding the actual assembly expression and checking these entries against the paper's distinct-bond recursion and quotient contract found no discrepancy. There are 42 raw windows in this interval; their class numbers are in `0,…,3740`, and their admissibility, kinds, successor classes and required final directions agree with their supplied representatives. All other touched codes have the invalid-word sentinel 3741. For example, code 1,041,408 (`SSSWNEEEEE`) maps to class 0, whose representative is code 0.

The arithmetic meaning checked is ordinary unbounded `ℕ`, with `<<< n` multiplying by `2^n` (`Mathlib/Data/Nat/Size.lean:18`) and `lane` taking a natural quotient and remainder. This fragment begins eight bits into a 12-bit lane; checking it as a standalone list of aligned 12-bit entries would be incorrect. Its boundary lane was checked after assembly with the neighboring fragment.

DECL: rawClass_6 PASS

`AKLT/Defs/Automaton10Data.lean:27` supplies bits 12,468,220 through 12,484,603, touching codes 1,039,018 through 1,040,383. Every one of these 1,366 codes fails the distinct-unoriented-bond condition defining `Ω₁₀` (paper `app-input-contracts.tex:21–34`), and every decoded entry is the sentinel 3741. This is the correct extension of the paper's sparse class map, whose domain contains only raw windows (`app-input-contracts.tex:383–405`). It introduces no extra raw states or missing classes.

The same unbounded natural arithmetic and quotient/remainder meaning applies. The fragment starts four bits into a lane and ends eight bits into a lane; both shared lanes were checked in the assembled table. The downstream modulo maps invalid words to class 0, but correctness is restricted to `RawWindow`, and the V2 coverage clause explicitly rejects these codes as raw (`AKLT/Blueprint/Top/ComputationV2.lean:15–17`). Thus this padding does not make the intended assertion vacuous.

DECL: rawClass_7 PASS

`AKLT/Defs/Automaton10Data.lean:29` supplies bits 12,451,836 through 12,468,219, touching codes 1,037,653 through 1,039,018. All 1,366 touched codes are outside `Ω₁₀`, and all decoded entries equal 3741. As for `rawClass_6`, this faithfully pads the sparse map required by `p:automaton10`; it is not a claim that a raw class is empty. The relevant paper locations are `app-input-contracts.tex:21–34` and `app-input-contracts.tex:367–419`.

Natural shifts are exact multiplication, without machine overflow or signed interpretation. The first lane is aligned; the last is shared with `rawClass_6` and was checked after assembly. No class number on a raw word is changed by the downstream modulo.

DECL: rawClass_8 PASS

`AKLT/Defs/Automaton10Data.lean:31` supplies bits 12,435,452 through 12,451,835, touching codes 1,036,287 through 1,037,652. Its decoded entries pass the independent coverage and quotient checks specified by the paper's `p:automaton10` reconstruction contract (`app-input-contracts.tex:376–419`), using the raw-window and absolute-direction definitions at `app-input-contracts.tex:21–34`. In particular, raw entries have valid class numbers and the representative's behavior in every absolute direction; invalid entries have sentinel 3741.

The literal has the same ordinary `ℕ` and lane meaning described above. Its first lane starts eight bits before the fragment boundary and was checked with its neighbor. Its upper boundary is lane-aligned. No signed value, truncating word type, or assumed quotient correctness is hidden in this declaration.

DECL: rawClass_9 PASS

`AKLT/Defs/Automaton10Data.lean:33` supplies bits 12,419,068 through 12,435,451, touching codes 1,034,922 through 1,036,287. Its entries likewise satisfy the coverage, range and representative/transition requirements of `p:automaton10` (`app-input-contracts.tex:367–419`). The checks use the paper's actual bond-trail domain, with revisits determined by earlier departures, rather than vertex-simple walks or a symmetry quotient (`app-input-contracts.tex:21–34`). No mismatch was found.

The natural-number encoding starts four bits into a 12-bit lane and ends eight bits into a lane. Both boundary entries were checked using the complete shift-and-add expression. Natural division and remainder recover their full class numbers; no division by zero or modular identification of distinct valid class numbers occurs.

Shared semantic and computational evidence:

- Read the complete data file, processing every hexadecimal literal and the assembly expressions, and the complete AKLT import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Inspected the direct consuming V2 automaton statement and the legacy/interface context. Only the five assigned declarations are judged here.
- `DirectionWord 10` is `Fin 10 → Compass`, with all four absolute steps on `ℤ × ℤ`. `wordBond` is a two-element `Finset`, so equality ignores orientation (`Mathlib/Data/Finset/Insert.lean:413–420`); `Function.Injective` therefore enforces pairwise distinct unoriented bonds. It permits vertex revisits. There is no restriction on the initial direction of a raw window. This matches `app-input-contracts.tex:21–34`.
- `List.finRange` enumerates every finite index once (`Mathlib/Data/List/FinRange.lean:29–45`). Since `i.val < 10`, the natural exponent `10 - 1 - i.val` is exactly `9 - i.val`, without unintended saturation. E,N,W,S have codes 0,1,2,3. Thus encoding and decoding implement the paper's most-significant-first formula (`app-input-contracts.tex:377–386`), without reversing the word.
- All packed literals fit their allocated, disjoint bit intervals; assembly introduces no carries between fragments. A 12-bit lane represents every class number and sentinel 3741. Both denominators in `lane`, `2^(12*code)` and `2^12`, are positive. On raw words, `% 3741` is the identity. Admitted destination codes are positive and encode successor class plus one, so natural subtraction by one is exact on every relevant transition; the zero case is an inadmissible-edge totalization.
- The finite function-space instance enumerates all functions (`Mathlib/Data/Fintype/Pi.lean:133–137`). The subtype instance and `Fintype.ofFinite` do not select a smaller raw-state set (`Mathlib/Data/Fintype/EquivFin.lean:176–196`); subtype cardinality counts exactly the predicate's members (`Mathlib/Data/Fintype/Card.lean:395–398`).
- The independent Python check in `check_data.py` parsed and evaluated the actual Lean assembly expressions, then generated windows by extending a path with every unused unoriented bond. The counts at depths 1 through 10 were `4,12,36,108,316,916,2628,7500,21268,60092`, matching `app-input-contracts.tex:390–405`. All `4^10 = 1,048,576` codes passed the raw/sentinel coverage check. Every supplied representative was raw and mapped to its own class, proving surjectivity without assuming it.
- For every raw window and all four absolute directions, regenerated admissibility agreed with the stored row, kind agreed with the representative even on inadmissible directions, and each admissible successor had the stored class. Every admissible non-revisit transition had the representative's final direction. This checks the hypotheses in `app-input-contracts.tex:315–341` and the comparisons in `app-input-contracts.tex:408–417`, with no added uniform-final-direction condition on revisit-only classes. Edge counts were exactly 2516 straight, 5032 turning and 1872 revisit.

Non-blocking remarks:

The paper gives a sparse archive contract, not individual hexadecimal constants. These five declarations therefore have no separate paper labels; their fidelity is assessed as fragments of that particular finite map. Reconstructing the sparse archive from the decoded map and class rows produced SHA-256 `671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785`, matching the data file's recorded hash. The original archive was not among the permitted inputs, so this hash comparison is an internal consistency check; the independent mathematical reconstruction checks above provide the substantive validation.

No Lean process was run. The executable finite checks are review evidence, not a kernel-checked proof of the V2 proposition. No input files were modified.
