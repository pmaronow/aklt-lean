STATUS: PASS
BLOCKING: 0

DECL: rawClass_480 PASS

At `AKLT/Defs/Automaton10Data.lean:975`, this auxiliary natural-number literal supplies bits 4702204–4718587 of `rawClass`, touching word codes 391850–393215. Every bit agrees with the corresponding portion of the repeated 12-bit invalid-word marker `3741 = 0xe9d`; all 1366 intersecting decoded lanes, including boundary lanes, equal 3741. In the paper's most-significant-first direction encoding (`app-input-contracts.tex:376–388`), every such word begins N,N,S and repeats a bond. These are correctly excluded from the domain of the supplied map in `p:automaton10` (`app-input-contracts.tex:367–371`), whose raw-window domain is defined at `app-input-contracts.tex:21–35`. The natural-number packing and unordered-bond meanings checked below apply here. No blocking discrepancy.

DECL: rawClass_481 PASS

At `AKLT/Defs/Automaton10Data.lean:977`, this auxiliary natural-number literal supplies bits 4685820–4702203, touching word codes 390485–391850. Its complete 16384-bit value matches the invalid-word marker stream, and all 1366 intersecting decoded lanes equal 3741. These codes also begin N,N,S under `app-input-contracts.tex:376–388`; their repeated unoriented bond excludes them from the windows of `app-input-contracts.tex:21–35`. Thus this is appropriate padding outside the supplied map's paper domain (`app-input-contracts.tex:367–371`). The natural-number packing and unordered-bond meanings checked below apply here. No blocking discrepancy.

DECL: rawClass_482 PASS

At `AKLT/Defs/Automaton10Data.lean:979`, this auxiliary natural-number literal supplies bits 4669436–4685819, touching word codes 389119–390484. Its complete 16384-bit value matches the invalid-word marker stream, and all 1366 intersecting decoded lanes equal 3741. These codes begin N,N,S under `app-input-contracts.tex:376–388`, so each repeats an unoriented bond and fails the raw-window definition at `app-input-contracts.tex:21–35`. The data therefore correctly extend the supplied map outside its domain (`app-input-contracts.tex:367–371`). The natural-number packing and unordered-bond meanings checked below apply here. No blocking discrepancy.

DECL: rawClass_483 PASS

At `AKLT/Defs/Automaton10Data.lean:981`, this auxiliary natural-number literal supplies bits 4653052–4669435, touching word codes 387754–389119. Its complete 16384-bit value matches the invalid-word marker stream, and all 1366 intersecting decoded lanes equal 3741. Each code begins N,N,S in the paper's encoding (`app-input-contracts.tex:376–388`), violating the distinct-unoriented-bonds requirement (`app-input-contracts.tex:21–35`). Consequently the marker is appropriate outside the supplied map's domain (`app-input-contracts.tex:367–371`). The natural-number packing and unordered-bond meanings checked below apply here. No blocking discrepancy.

DECL: rawClass_484 PASS

At `AKLT/Defs/Automaton10Data.lean:983`, this auxiliary natural-number literal supplies bits 4636668–4653051, touching word codes 386389–387754. Its complete 16384-bit value matches the invalid-word marker stream, and all 1366 intersecting decoded lanes equal 3741. Again every code begins N,N,S under `app-input-contracts.tex:376–388`, hence repeats an unoriented bond and is excluded by `app-input-contracts.tex:21–35`. This is the correct off-domain extension for the map asserted at `app-input-contracts.tex:367–371`. The natural-number packing and unordered-bond meanings checked below apply here. No blocking discrepancy.

Non-blocking remarks:

- These five private definitions are pieces of a dense lookup table, with no separate paper assertion about their hexadecimal values. Their relevant counterpart is the supplied map on raw windows in `p:automaton10`, together with its reconstruction contract (`app-input-contracts.tex:376–419`). The paper specifies this map only on valid windows. None of the reviewed bits encodes a valid-window class assignment; using an invalid-word marker outside that domain is faithful.

- Checked the entire data file and its project import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. `Compass.step` uses exactly E=(1,0), N=(0,1), W=(-1,0), S=(0,-1). `RawWindow` is `Function.Injective (wordBond (0,0) w)` (`Automaton.lean:8–13`), and `wordBond` is a `Finset` of its two endpoints (`Trails.lean:26–32`). `Finset.pair_comm` (`Mathlib/Data/Finset/Insert.lean:419`) confirms that reversing endpoints gives the same bond. For N,N,S the vertices are (0,0),(0,1),(0,2),(0,1); bonds at distinct zero-based indices 1 and 2 coincide. This proves exclusion independently of the data or any enumeration instance.

- Packing uses unbounded `ℕ`, with no machine-word overflow or signed interpretation. `Nat.shiftLeft_eq_mul_pow` (`Mathlib/Data/Nat/Size.lean:18`) identifies `x <<< b` with `x * 2^b`. I parsed the complete shift-and-add assembly at `Automaton10Data.lean:1551` and checked all chunk offsets and nonoverlapping widths. The final chunk has 4095 hexadecimal digits, so the reviewed offsets must account for that shorter chunk; chunk boundaries need not align with 12-bit lanes. All boundary lanes were checked using their actual neighboring chunks.

- `lane` and `rawClassAt` (`Automaton10Data.lean:1595–1611`) use natural Euclidean division and remainder to extract a 12-bit lane. Their divisors are powers of 2 and are positive; the lane modulus is 4096. The zero-based exponent `m-1-i.val` in word encoding/decoding equals the paper's exponent `m-j` for `j=i.val+1`; for `m=10` and `i : Fin 10`, natural subtraction never truncates a negative intended exponent. Direction decoding only receives residues 0–3.

- The marker 3741 is outside the actual class domain `Fin 3741` (labels 0–3740). `supplied.project` reduces it modulo 3741 to totalize the function (`Automaton10Data.lean:1623–1624`). This cannot merge a reviewed invalid word into the paper's raw domain: correctness is explicitly restricted to `RawWindow` inputs (`Automaton.lean:78–84`), and raw successors under admissible steps remain raw (`app-input-contracts.tex:37–39`). Moreover, `Automaton10StatementV2` checks marker bounds and raw coverage before taking that modulo (`AKLT/Blueprint/Top/ComputationV2.lean:13–23`). Thus the totalization does not conceal a missing class or make the intended checks vacuous. These literals introduce no hypotheses, quantifiers, finiteness assumptions, or additional side conditions.

- Verification used an independent Python recursion adjoining every unused unoriented bond, as specified at `app-input-contracts.tex:232–237`. It reproduced all depth-1 through depth-10 counts at `app-input-contracts.tex:396–398`: 4, 12, 36, 108, 316, 916, 2628, 7500, 21268, 60092. Across all 4^10 decoded lanes, values were in 0–3741 and a value was below 3741 exactly for a generated raw window. For the five reviewed chunks, I additionally compared every literal bit with its expected marker-stream bit and checked every intersecting lane. This is an exhaustive finite check of the reviewed data, not a sample. No Lean processes were needed, and no input files were modified.
