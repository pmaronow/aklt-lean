STATUS: PASS
BLOCKING: 0

DECL: rawClass_385 PASS

`AKLT/Defs/Automaton10Data.lean:785` defines an auxiliary packed natural-number fragment, rather than a separate assertion in the paper. Its intended object is the supplied class map of Proposition `p:automaton10` (`app-input-contracts.tex:367–388`), whose domain is the distinct-unoriented-bond words of Definition `d:memory-automaton` (`app-input-contracts.tex:21–35`). The paper specifies most-significant-first base-four word codes at `app-input-contracts.tex:376–392`.

In the actual assembly at `Automaton10Data.lean:1551`, this fragment occupies bit positions `[6258684, 6275068)`, counting from bit zero. It intersects the 12-bit lanes for word codes `521557` through `522922`. Every such word starts N,S, so its first two bonds are the same unoriented bond. None belongs to the paper's domain. Exact reconstruction checks every bit of the literal, including the partial lane at the fragment boundary: each intersecting assembled lane is `3741 = 0xe9d`, the designated invalid-word marker. Thus this fragment represents exactly the required total extension outside the paper's domain and excludes no valid window.

The following semantic checks apply to all five fragments. Their declared type `ℕ` gives exact, unbounded nonnegative integers; hexadecimal notation introduces no signed interpretation or machine overflow. Natural left shift multiplies by a power of two (`Mathlib/Data/Nat/Size.lean:18`). I checked every shift and addition in the complete packed-table assembly against concatenation of the literal hexadecimal fragments, preserving leading zeroes and the final fragment's shorter width. Consequently the offsets above and below come from the actual expression, including its shifts that are four bits shorter near the final fragment.

`lane` and `rawClassAt` (`Automaton10Data.lean:1595–1611`) use natural quotient and remainder: `packed / 2^(12*code) % 4096` extracts precisely one 12-bit lane. These denominators and moduli are positive. Mathlib's positional interpretation of natural division is also explicit in `Mathlib/Data/Nat/Digits/Defs.lean:432–451`. `List.finRange` visits every index once (`Mathlib/Data/List/FinRange.lean:29–44`). For `Fin 10`, the exponent `10-1-i.val` is exactly `9-i.val`, with values 9 through 0; natural subtraction causes no unintended truncation. Direction numbers 0,1,2,3 mean E,N,W,S in both the paper and `Automaton10Data.lean:1598–1609` / `Geometry.lean:16–36`. The decoder's final case therefore means S on every decoded digit.

The raw predicate is `Function.Injective (wordBond (0,0) w)` (`Automaton.lean:8–13`). Vertices lie in `ℤ × ℤ`, with componentwise addition; `wordBond` is the finite set of the two endpoints (`Trails.lean:23–32`). Finset insertion and its commutativity (`Mathlib/Data/Finset/Insert.lean:347–365,409–413`) make this an unoriented bond. For the N,S prefix, vertices are `(0,0),(0,1),(0,0)`, so bonds at distinct indices 0 and 1 coincide, directly refuting injectivity. This establishes invalidity independently of the stored marker.

The marker has the intended consumer meaning: `Automaton10StatementV2` explicitly requires `rawClassAt code ≤ 3741` and `rawClassAt code < 3741 ↔ RawWindow (decodeWord 10 code)` (`AKLT/Blueprint/Top/ComputationV2.lean:13–17`). It thus requires exactly `3741` on these invalid words. Although `supplied.project` reduces the marker modulo 3741 to class zero (`Automaton10Data.lean:1623–1624`), the quotient's regeneration requirements quantify over raw windows (`Automaton.lean:78–84`), matching the paper's domain. This totalization neither supplies an extra paper hypothesis nor changes a class on that domain. The five literal definitions themselves contain no quantifiers, hypotheses, division, subtraction, or instance parameters. `MemoryWindow 10` is a subtype of all finite direction words, and its `Fintype.ofFinite` instance enumerates that actual subtype, not a supplied state list (`Automaton.lean:12–17`).

DECL: rawClass_386 PASS

`Automaton10Data.lean:787` occupies bits `[6242300, 6258684)` and intersects codes `520191–521556`. Under the exact natural-number shift, quotient/remainder, and word-code meanings checked above, every affected assembled lane equals `3741`. All these words start N,S and repeat their first unoriented bond. Every fragment bit, including its partial boundary lane, matches the marker encoding. This is the correct auxiliary extension of the map whose domain and coding are specified at `app-input-contracts.tex:21–35,367–405`; it changes no value on that domain.

DECL: rawClass_387 PASS

`Automaton10Data.lean:789` occupies bits `[6225916, 6242300)` and intersects codes `518826–520191`. Exact `ℕ` assembly and lane extraction yield marker `3741` throughout. The literal's bits at both split-lane boundaries also match that encoding. Every decoded word starts N,S and fails bond injectivity at indices 0 and 1. Thus this fragment correctly fills only invalid codes outside the map in `app-input-contracts.tex:21–35,367–405`, with the intended base-four convention and no lost valid state.

DECL: rawClass_388 PASS

`Automaton10Data.lean:791` occupies bits `[6209532, 6225916)` and intersects codes `517461–518826`. The checked natural-number operations decode every affected lane as `3741`, including the lane crossing the boundary. Every word begins N,S, so its first two unoriented bonds coincide. The fragment therefore has exactly the auxiliary meaning needed for the paper's raw-window map (`app-input-contracts.tex:21–35,367–405`) and the explicit invalid-code coverage requirement of its Lean consumer.

DECL: rawClass_389 PASS

`Automaton10Data.lean:793` occupies bits `[6193148, 6209532)` and intersects codes `516095–517460`. Exact natural-number assembly, including the partial boundary lane, gives marker `3741` for every affected code. All decoded words start N,S and hence lie outside the distinct-bond domain. This correctly represents the total extension used by the Lean coverage check, without altering the paper's supplied map on its domain (`app-input-contracts.tex:21–35,367–405`).

Non-blocking remarks:

- Read the complete assigned file and its AKLT import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`; inspected the consuming interface and relevant Mathlib meanings. Only the five assigned declarations receive verdicts here.
- Reproducible exact checks are in `audit_check.py`; run with `python3 audit_check.py`. Independent generation by unused unoriented bonds reproduces the paper's counts `4,12,36,108,316,916,2628,7500,21268,60092` (`app-input-contracts.tex:390–401`). Checking all 1,048,576 assembled raw lanes confirms the range and valid-word/marker equivalence. All five assigned fragments were checked bit for bit against the expected marker pattern. No Lean processes were launched.
- These fragments have no standalone literal counterpart in the paper. Their mathematical role is fully checkable because all affected codes are invalid words; this review does not authenticate the archived file or its advertised SHA-256.
