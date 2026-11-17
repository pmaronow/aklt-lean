STATUS: PASS
BLOCKING: 0

DECL: rawClass_615 PASS

`AKLT/Defs/Automaton10Data.lean:1245` defines auxiliary packed data for the map in `p:automaton10`, not a separate paper assertion. The matching specification is `paper/app-input-contracts.tex:367–419`, especially the word coding and map coverage at lines 376–406, using the raw-window definition at lines 21–35. In the actual assembly at Lean line 1551, this 4096-digit hexadecimal natural occupies 16384 bits starting at bit 2490364. It intersects code lanes 207530–208895. Independent generation finds that all 1366 words are outside Ω₁₀, and every intersected lane is correctly marked 3741 (hexadecimal E9D). I checked the partial lanes shared with adjacent chunks. Mathlib's natural-number shift is multiplication by a power of two; natural division and remainder in `lane` extract the intended 12-bit lanes. These entries correctly totalize the map outside its paper domain.

DECL: rawClass_616 PASS

`AKLT/Defs/Automaton10Data.lean:1247` is another auxiliary chunk of the same map specified in `paper/app-input-contracts.tex:376–406`. Its 16384 bits start at bit 2473980 and intersect code lanes 206165–207530. All 1366 decoded words repeat an unoriented bond, and all their assembled lanes equal the invalid-word sentinel 3741. Exact reconstruction of this literal from those lanes agrees, including the shared boundary. Checked meaning: an arbitrary-precision `ℕ` numeral, natural left shifts, and quotient/remainder extraction, without signed or fixed-width arithmetic. Its exclusion of these words agrees with the domain at paper lines 24–29.

DECL: rawClass_617 PASS

`AKLT/Defs/Automaton10Data.lean:1249` supplies 16384 bits starting at bit 2457596, intersecting code lanes 204799–206164. Under the most-significant-first coding in `paper/app-input-contracts.tex:376–388`, all 1366 words are invalid raw windows. Their lanes all equal 3741, and reconstruction reproduces the complete literal, including its partial boundary lane. The checked natural-number shifts and division/remainder have the same meaning as for the preceding chunks; no valid window is removed. This is the correct auxiliary representation of the domain and coverage requirements at paper lines 21–35 and 390–406.

DECL: rawClass_618 PASS

`AKLT/Defs/Automaton10Data.lean:1251` supplies 16384 bits starting at bit 2441212, intersecting code lanes 203434–204799. Every one of these 1366 words is outside the distinct-unoriented-bond domain of `paper/app-input-contracts.tex:24–29`. All assembled lanes correctly equal 3741, and the exact literal reconstructed from the required sentinel bits matches. Natural-number lane extraction, including the two shared boundary lanes, is correct. Thus this auxiliary chunk faithfully supports the map-coverage contract at paper lines 390–406.

DECL: rawClass_619 PASS

`AKLT/Defs/Automaton10Data.lean:1253` supplies 16384 bits starting at bit 2424828, intersecting code lanes 202069–203434. There are 161 valid raw windows and 1205 invalid words in this interval. Each invalid lane equals 3741; every valid lane is below 3741 and satisfies the representative, admissibility, kind, successor and non-revisit-arrival checks required by `paper/app-input-contracts.tex:408–417` and `l:automaton-quotient` at lines 315–341. For example, code 202069 decodes to ESENNNNNNN and maps to class 115. Exact reconstruction, with the boundary bits included, reproduces the literal. The map's `% 3741` therefore preserves every valid class value, rather than concealing an out-of-range value.

Non-blocking remarks:

- Read the complete data file programmatically, including every literal and assembly expression, and read its entire local import chain: Automaton, Kernel, Trails, Domain, PinModel, Moment and Geometry. Only the five assigned declarations are judged here.
- Checked the relevant Mathlib meanings: `Nat.shiftLeft_eq_mul_pow` (`Mathlib/Data/Nat/Size.lean:18`); natural digit extraction (`Mathlib/Data/Nat/Digits/Defs.lean:444–489`); unordered finite pairs (`Mathlib/Data/Finset/Insert.lean:413–420`); `Fin` values and modular casts (`Mathlib/Data/Fin/Basic.lean:373–404`); and `Fintype.ofFinite` (`Mathlib/Data/Fintype/EquivFin.lean:176–180`). Bond injectivity therefore forbids repeated unoriented edges on the actual integer lattice. The finite subtype enumerates all qualifying words, without an assumed stored state list.
- At memory ten, `Fin 10` indices are 0–9, so the natural subtractions in the coding exponents and final-direction index do not truncate incorrectly. E,N,W,S have codes 0,1,2,3 and the paper's signed unit displacements. Every divisor used for extraction is a positive power of two or four. Successor subtraction decodes stored class-plus-one values only on admitted edges; zero denotes an inadmissible direction. Revisit detection counts earlier departures at indices 0–9 and takes precedence over straight/turn classification.
- The independent checker regenerated all 60092 raw windows, verified coverage over all 4¹⁰ codes, all 3741 representatives, and every raw direction comparison. It also compared raw kinds with representative kinds on forbidden directions, as required by the paper's lemma. The admitted quotient edge counts are exactly 2516, 5032 and 1872. Thus neither invalid-word totalization nor an empty domain makes these checks vacuous.
- Reproduction: `python3 review_check.py`; results are saved in `check-results.json`. These are independent integer checks, not a Lean proof. No Lean processes were launched and no inputs were modified. The archived text file and its byte-level checksum were not separately available among the permitted inputs; the review checks the supplied literals against the paper's full mathematical reconstruction contract.
