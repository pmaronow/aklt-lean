STATUS: PASS
BLOCKING: 0

DECL: closedContribution PASS

This auxiliary definition (`AKLT/Defs/Kernel.lean:101`) is the individual summand in (H3_h), `paper/sec7-recursion.tex:598–603`; the same short-trail expression is specified explicitly at `paper/app-input-contracts.tex:898–907`.

For an ordered list of first-departure indices `[i₁, …, iₘ]`, the recursive `exposureSum` expands to

`Σₖ witnessKappa(w,iₖ) · Π_{l≤k} passageFactor(straight(w,iₗ))`.

In particular, `[i,j]` gives `xᵢ κᵢ + xᵢ xⱼ κⱼ`: the product includes the responding departure, and is a prefix in the chosen exposure order. `trailBaseWeight` contributes `3^{-(n-r)} 5^{-r} = 3^{-n}(3/5)^r`, where `r` counts departures with an earlier departure at the same site. It does not introduce an extra passage factor. This agrees with `paper/sec6-walks.tex:655–675` and `paper/sec7-recursion.tex:549–551`.

`witnessKappa` sums each live pair's coefficient times its exact type weight. This equals `Σ_{Y,s} κ_{Y,s}(i) h_Y`: every pair has exactly one type and one natural-valued shift. Consequently this aggregate needs no row-type argument X; changing X changes the shift partition, not its total. The local pair checks are detailed under `kernelLengthCoefficient` below.

The ordering matches `paper/sec7-recursion.tex:572–592`. `List.finRange n` lists each index once in increasing order (Mathlib `Data/List/FinRange.lean:29–33`, `Data/List/Sort.lean:497–498`); filtering selects precisely lattice first departures. For `n ≤ 12`, `shortOrderLE` orders the exact rational scores increasingly, places zero-reward scores last, and breaks ties by increasing index. Mathlib's `mergeSort` preserves the list's elements and sorts in the supplied relation (`Data/List/Sort.lean:323–346`). Here that relation is the total, transitive lexicographic comparison of score and index, including the separate infinity case. The denominator of every finite score is positive: both passage factors and all nonzero rewards are positive. Thus rational division by zero cannot change the ordering. For `n > 12`, the two filters preserve path order and put straight first departures before turning first departures. The dyadic h_C and cutoff 12 are exactly the paper's, with no floating-point approximation or theta dependence.

Although total on direction words, this helper is used for the closed-trail summands of `kernelPartialRow` and `firstDirectionPartialRow`, both guarded by `ClosedTrail`. Defining its value on other words adds no unintended trails to those sums.

DECL: kernelLengthCoefficient PASS

This is exactly the fixed-n inner sum defining M_{XY,s} in `paper/sec7-recursion.tex:516–547`, using the subsequently fixed orderings at lines 572–585. Its domain is the whole ambient plane, with the exact prescribed start u=(-1,0), centre c=(0,0), targets v_B=(1,0), v_C=(0,1), and incoming direction u-c=west.

`DirectionWord n = Fin n → Compass` enumerates every length-n nearest-neighbour direction sequence once. The four compass displacements are distinct unit vectors. The actual finite-function instance is Mathlib `Pi.instFintype` (`Data/Fintype/Pi.lean:133–136`), applied to `Fin n` and the explicitly complete four-element `Compass` instance. Thus the sum ranges over all 4^n words; `classical` supplies decidability, not a geometric or finiteness hypothesis. A fixed start makes words equivalent to vertex paths without translation or symmetry multiplicities.

The `ClosedTrail` guard imposes exactly distinct unoriented bonds, the prescribed endpoint, avoidance of c through the endpoint, and no earlier hit of v. `wordBond` is a two-element `Finset Plane`, so injectivity forbids repetitions in either orientation. Immediate reversal after the first step already repeats a bond; the explicit initial-reversal prohibition merely excludes the step to c, which the paper also excludes (`paper/sec7-recursion.tex:569–570`). These restrictions do not impose self-avoidance: a site may be revisited using different bonds. `wordVertex` is the sum of precisely the first j steps for `0 ≤ j ≤ n`. All vertex indices used here fall in that range; its extension beyond n is irrelevant.

Departure counts use only indices strictly before i, exactly as required at `paper/sec7-recursion.tex:521–525` and `paper/app-input-contracts.tex:872–878`. Since `i : Fin n`, `min i.val n = i.val`. The natural subtraction `i.val - 1` in `wordIncoming` occurs only in the nonzero-index branch, so it selects the preceding step without truncation error. At index zero the incoming vector is west; subtracting it from u gives c. Coordinates and their differences are integers, and `latticeDist` uses their `natAbs` values, giving ambient ℓ¹ distance as required by `paper/sec2-moments.tex:20–21`.

The response construction erases the arrival neighbour, then separates the outgoing neighbour from the two other neighbours. It declares exactly c and sites with at least two previous departures dead. The outgoing neighbour is live on every guarded closed trail, by the bond-count argument at `paper/sec7-recursion.tex:560–568`; hence its unconditional insertion creates no spurious dead pair. Mathlib `Finset.powersetCard 2` means exactly the two-element subsets (`Data/Finset/Powerset.lean:196–203`). There are three pairs when both other neighbours are live, one when exactly one is live, and none when neither is live. The coefficients are respectively a for the pair without the outgoing neighbour, b for pairs containing it in the three-pair case, and b′ in the one-pair case. The six exact rational constants match `paper/sec7-recursion.tex:279–285`.

Each such pair consists of two distinct neighbours of one lattice site, so is at distance two. `responsePairType` classifies opposite, coordinate-sharing endpoints as B and diagonal endpoints as C, agreeing with `paper/sec7-recursion.tex:36–41`. `pairShift` takes the maximum over the pair of the minimum of the two ambient endpoint distances, exactly line 534. Mathlib `Finset.sup` folds the lattice supremum from bottom (`Data/Finset/Lattice/Fold.lean:42–63`); on a nonempty two-element subset of ℕ this is the ordinary maximum. Its empty-set convention is never used for a response pair. `responseKappa` retains precisely the requested type and exact shift, and `exposureSum` then uses precisely the ordered first departures. No extra admissibility, boundary, positivity, or convergence premise restricts the paper's trail class.

DECL: shiftKernel PASS

This is M_{XY,s} from `paper/sec7-recursion.tex:541–545`, with the extended nonnegative interpretation explicitly required at lines 549 and 555–558.

The Lean sum includes n=0, whereas the paper writes n≥1. The extra term is zero: the empty word ends at u, and u is different from both prescribed targets, so no length-zero word satisfies `ClosedTrail`. Thus the index change does not alter the series.

Every length coefficient is a finite nonnegative rational: base weights and passage factors are positive, assigned coefficients are positive, and filters, finite sums, and the exposure recursion preserve nonnegativity. The rational-to-real coercion is the exact ordered-field embedding (Mathlib `Data/Rat/Cast/Order.lean:31–56`). `ENNReal.ofReal` maps a real r to max(r,0), embedded as a finite extended nonnegative real (`Basic/ENNReal/Basic.lean:230–254`). Here it therefore preserves every coefficient and discards no negative contribution or cancellation. Its compatibility with nonnegative finite addition is also explicit in `Basic/ENNReal/Real.lean:52–55`.

For ENNReal, `tsum` equals the supremum of all finite subsums, without a prior finiteness assumption: Mathlib `Topology/Algebra/InfiniteSum/ENNReal.lean:56–73` (`ENNReal.hasSum`, `ENNReal.summable`, `ENNReal.tsum_eq_iSup_sum`). Divergence therefore gives infinity rather than the fallback zero possible for a nonsummable real-valued series. This is exactly the paper's convention.

DECL: shiftedKernel PASS

For the paper's positive theta domain, this is exactly M_theta[X,Y] at `paper/sec7-recursion.tex:546`, with the same extended-series convention at lines 555–558. The operative theorem domain `q² < theta ≤ 1` is stated at lines 619–623 and retained in `AKLT/Blueprint/Top/Response.lean:51–64`; `OpenTrailBound` includes `0 < q < 1`.

The exponent `-(s : ℤ)` is the negative of an integer cast, not natural subtraction. Mathlib `zpow_neg` (`Algebra/Group/Basic.lean:430–435`) and `zpow_natCast` give `theta^(-(s:ℤ)) = (theta^s)⁻¹`. For positive theta this is a finite positive real, including value 1 at s=0, so `ofReal` preserves it exactly and division by zero cannot occur. Multiplication and the ENNReal `tsum` give the required nonnegative weighted series. A positive weight does not erase an infinite coefficient (`ENNReal.top_mul`, `Basic/ENNReal/Operations.lean:186–192`). Finiteness is left as the conclusion of the interface statement, not assumed or forced by a conversion to real numbers.

The orderings are fixed in `kernelOrdering` before theta is supplied, so there is no theta-dependent choice hidden in this definition.

DECL: kernelPartialRow PASS

This is the left-hand side of the finite-cutoff assertion (H3_h), `paper/sec7-recursion.tex:594–604`. It sums the exact `closedContribution` over every guarded closed trail at every length from 1 through R, inclusive.

Mathlib `Finset.mem_Icc` means `1 ≤ n ∧ n ≤ R` (`Order/Interval/Finset/Defs.lean:280–302`); the natural-number interval instance implements precisely this finite interval (`Order/Interval/Finset/Nat.lean:34–39`). Consequently R=0 gives the empty sum, while every positive cutoff includes its final length. There is no hidden restriction to R≤12: twelve only selects the exposure ordering within each summand. Arbitrarily long trails retain their actual lattice departure history, dead neighbours, and pair coefficients.

The rational result is exact, and its order comparison with `kernelRho * kernelWitness X` is equivalent to the same real comparison under the ordered embedding checked above. The consumer `PositiveVectorBound` quantifies independently over both row types and every `R : ℕ`, exactly the paper's two types and every nonnegative integer cutoff; it adds no hypothesis. Neither row is vacuous: for example the words N,E and N,E,E,S give valid C and B trails respectively and have positive contributions. The paper's equivalence with the full nonnegative row sum (`paper/sec7-recursion.tex:611–617`) is compatible with these definitions: finite trails per length, nonnegative terms, unique type/shift assignments, and exhaustive length cutoffs.

Non-blocking remarks:

- `shiftedKernel` is total for all real theta. At theta=0, Lean's real inverse and integer powers use their totalized zero conventions; negative theta can produce negative powers subsequently clipped by `ofReal`. These values are outside the paper's positive-parameter use. The reviewed interfaces use theta=1 or enforce `q² < theta` with positive q, so these extra-domain values do not weaken or alter the paper's assertions.
- Context read in full: `Kernel.lean` and its project import chain `Trails.lean → Domain.lean → PinModel.lean → Moment.lean → Geometry.lean`. Relevant Mathlib definitions and interface consumers were checked from the permitted sources. No input files were modified and no Lean processes were launched. This is a statement-fidelity review; it does not certify the numerical H3 bound itself.
