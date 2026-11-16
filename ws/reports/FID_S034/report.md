STATUS: PASS
BLOCKING: 0

DECL: deadAt PASS

Matches Definition `d:kernel`, [paper/sec7-recursion.tex:525](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:525): a neighbour is dead precisely when it is the centre or has had two previous departures. `Kernel.lean:21–22` uses `z = kernelCentre ∨ 2 ≤ departureCount kernelStart w i.val z`, with the stipulated centre `(0,0)` and start `(-1,0)` (`Kernel.lean:9–10`).

In `Trails.lean:47–48`, the count is the cardinality of the indices `j ∈ Finset.range (min i.val n)` whose departure vertex is `z`. Since `i : Fin n`, `i.val < n`, so this is exactly `#{j < i.val : v_j = z}`. It excludes the current departure and counts departures rather than arrivals. Mathlib's `Finset.mem_range` is `j ∈ range k ↔ j < k` (`Mathlib/Data/Finset/Range.lean:64`); `mem_filter` conjoins membership and the predicate (`Data/Finset/Filter.lean:127`); `card` counts elements (`Data/Finset/Card.lean:47`). The inequality means at least two, agreeing with the paper's dead-site rule; on the intended trails there cannot be more than two prior departures at a site, by degree four and distinct unoriented bonds. There is no index subtraction or division in this definition.

DECL: responseNeighbours PASS

Matches the three neighbours other than the arrival site in Definition `d:kernel`, [paper/sec7-recursion.tex:522](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:522). The direction convention is explicit in [paper/sec6-walks.tex:668](/home/ubuntu/aklt/review/FID_S/paper/sec6-walks.tex:668): incoming direction is `v_i-v_(i-1)`, with the designated direction at zero.

`Plane` is the infinite integer lattice `ℤ × ℤ`, and `neighbours y` is the image of all four distinct compass displacements (`Geometry.lean:8,17–44`). Mathlib's product addition and subtraction operate coordinatewise (`Mathlib/Algebra/Notation/Prod.lean:65–82,112–128`, including the generated additive declarations), so `v_i - incoming.step` is the arrival site, with the correct minus sign. At zero, incoming is west, namely `u-c=(-1,0)`, and the erased site is `u-(-1,0)=c`. At a positive index, `wordIncoming` selects `w (i.val-1)` (`Trails.lean:39–40`); its natural subtraction occurs only in the nonzero branch and gives the genuine predecessor, without underflow. `wordVertex` is the sum of steps before its natural index (`Trails.lean:27–28`), so this erased site is exactly `v_(i-1)`.

Mathlib's `mem_univ` includes every compass constructor (`Data/Fintype/Defs.lean:96`), `mem_image` describes precisely the image (`Data/Finset/Image.lean:293`), and `mem_erase` removes exactly the specified point (`Data/Finset/Erase.lean:57`). Thus exactly three distinct neighbours remain. On a `ClosedTrail`, immediate reversal is excluded by distinct unoriented bonds and the initial rule (`Trails.lean:35–36`), so the actual outgoing neighbour is among them. No finite-volume or periodic interpretation is introduced.

DECL: liveOtherNeighbours PASS

This auxiliary definition is exactly the live subset of the two non-outgoing neighbours `f,g` in [paper/sec7-recursion.tex:523](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:523) and [paper/sec7-recursion.tex:527](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:527). `Kernel.lean:32–33` removes `v_(i+1)` from the three non-arrival neighbours, then retains precisely those satisfying `¬ deadAt w i z`.

For `i : Fin n`, the natural index `i.val+1` is at most `n`, so `wordVertex` yields the actual next vertex, including the final target at the last departure. There is no modular `Fin` addition and no unintended use of the clamped extension beyond `n`. Mathlib's `mem_erase` and `mem_filter` give exactly `z ∈ responseNeighbours w i ∧ z ≠ v_(i+1) ∧ ¬ deadAt w i z`. Therefore its cardinality is the number of live members of `f,g`, excluding `o`; the test for cardinality one in `pairCoefficient` has the intended meaning. `classical` supplies decidability for filtering and adds no mathematical hypothesis.

DECL: responsePairs PASS

Matches precisely the pair cases in Definition `d:kernel`, [paper/sec7-recursion.tex:527](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:527). Writing `L = liveOtherNeighbours w i` and `o = v_(i+1)`, `Kernel.lean:37` forms all two-element subsets of `{o} ∪ L`.

Mathlib's `Finset.mem_powersetCard` says `p ∈ s.powersetCard 2 ↔ p ⊆ s ∧ p.card = 2` (`Mathlib/Data/Finset/Powerset.lean:198–203`); `mem_insert` is membership in the inserted singleton or the original set (`Data/Finset/Insert.lean:365`). A `Finset` has no duplicates (`Data/Finset/Defs.lean:72–79`). Consequently two live others give exactly `{f,g}`, `{f,o}`, `{g,o}`; one gives exactly its pair with `o`; zero gives no pair. These are unordered pairs of distinct sites, each counted once.

Inserting `o` without checking its liveness is justified on the intended domain: `ClosedTrail` imposes the distinct unoriented bonds, centre avoidance, and first hit of the target used in the paper's outgoing-liveness argument at [paper/sec7-recursion.tex:560](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:560). Thus no dead outgoing site enters a kernel response pair. Distinct neighbours of the same lattice site are at distance two, as required for the subsequent pair-type classification.

DECL: pairCoefficient PASS

Matches the assignments in Definition `d:kernel`, [paper/sec7-recursion.tex:527](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:527), using the exact rational table in Lemma `l:log-mean-bounds`, [paper/sec7-recursion.tex:279](/home/ubuntu/aklt/review/FID_S/paper/sec7-recursion.tex:279). For a generated response pair, `Kernel.lean:41–44` gives:

| Live other neighbours | Pair | Coefficient |
| --- | --- | --- |
| Two | `{f,g}`, excluding `o` | `a_tau` |
| Two | `{f,o}` or `{g,o}` | `b_tau` |
| One | Its pair with `o` | `b'_tau` |
| Zero | No generated pair | No contribution |

`wordStraight` is `decide (w i = wordIncoming kernelIncoming w i)` (`Trails.lean:43–44`), so straight means continuing in the incoming direction, exactly as in [paper/sec6-walks.tex:662](/home/ubuntu/aklt/review/FID_S/paper/sec6-walks.tex:662). Mathlib's `Bool.decide_iff` identifies this Boolean with the tested proposition (`Data/Bool/Basic.lean:71`). Finset membership in `p` is ordinary site membership, and its cardinality test counts live others, not live pairs or all three neighbours.

The constants in `Trails.lean:15–21` agree entry by entry: straight `(145217,352782,340008)/10^6`, turn `(150000,357549,344661)/10^6`, in the order `(a,b,b')`. All divisions elaborate in `ℚ`, whose field instance is `Rat.instField` (`Mathlib/Algebra/Field/Rat.lean:27`); these are exact rational divisions, not natural-number quotients. The denominator is the nonzero constant `10^6`. No logarithmic-mean evaluation, zero denominator, sign change, or extra hypothesis is hidden in this coefficient assignment.

Non-blocking remarks:

- The helpers are total on direction words and departure indices, and `pairCoefficient` is total on arbitrary finite sets. The paper specifies their use at first visits of valid closed trails and on generated pairs. This broader implementation domain causes no discrepancy: `responseKappa` and `witnessKappa` sum only over `responsePairs` (`Kernel.lean:56–70`); the kernel exposure sums use `kernelOrdering`, built from `firstVisitList` (`Kernel.lean:73–108`); and kernel sums are restricted by `ClosedTrail` (`Kernel.lean:105–108,119–122`). The phase consumers also suppress response rewards on revisits through `phaseTransition` (`Stationary.lean:23–34,121–125`).
- There are no hidden finiteness assumptions on `Plane`. Neighbour sets are finite images of the explicitly enumerated four-element compass type, and direction words are finite functions `Fin n → Compass`. Mathlib's function-space `Fintype` instance enumerates all such functions (`Data/Fintype/Pi.lean:134–136`). `Fin 0` has no departure index; moreover the zero-length word cannot satisfy either canonical `ClosedTrail` endpoint condition. These conventions introduce no vacuous kernel row.
- Read the complete `Kernel.lean` and its local import chain `Trails → Domain → PinModel → Moment → Geometry`, and inspected the relevant consumers and Mathlib definitions. As a supplementary check, a Python enumeration covered all closed trails of length at most twelve: 2,796 in row B and 2,612 in row C. At all 60,468 first-visit departures, arrival signs, prefix counts, outgoing liveness, generated pairs, and exact coefficients agreed with an independent case-based transcription of the paper. Both straight/turn cases with one and two live others occurred. The zero-live-other case was checked directly from `powersetCard` of a singleton. This finite check supplements the source-level reasoning above; no Lean process was launched.
