STATUS: PASS
BLOCKING: 0

DECL: responsePairType PASS

Paper: `sec7-recursion.tex:36` (Definition `d:pairenv`, especially lines 38–40) and `sec7-recursion.tex:532` (Definition `d:kernel`); the opposite/perpendicular interpretation is explicit in `app-input-contracts.tex:450`.

For a two-element set `{a,b}`, the bounded universal condition reduces to `a.1 = b.1 ∨ a.2 = b.2`: self-comparisons are true, and the reversed comparison is equivalent. Every response pair consists of two distinct nearest neighbours of the same departure site. Such sites have ambient distance two; sharing a coordinate means they are opposite (type B), and otherwise they are perpendicular (type C). This agrees with `HasPairType` in `AKLT/Defs/Domain.lean:117`.

Checked Mathlib's `Finset.powersetCard`: membership means precisely subset inclusion and cardinality equal to the requested number (`Mathlib/Data/Finset/Powerset.lean:198`, `mem_powersetCard` at line 202). Thus `responsePairs` supplies actual unordered two-element sets, with no duplicate endpoint or vacuous empty-pair interpretation. The other caller, `relaxedReward` in `AKLT/Defs/Stationary.lean:37`, also uses two-element subsets of neighbours. The coordinate disjunction correctly occurs inside the universal quantifiers; on these two-element inputs it expresses exactly the required classification.

DECL: pairShift PASS

Paper: `sec7-recursion.tex:517` fixes the row endpoints, and `sec7-recursion.tex:532`–535 defines `s(p) = max_{z∈p} min{d(z,u),d(z,v)}`. The distance convention is explicitly ambient ℓ¹ distance in `sec2-moments.tex:20`.

`kernelStart = (-1,0)` and `kernelTarget B = (1,0)`, `kernelTarget C = (0,1)` match the paper. The argument X selects the original row's target, as required; it does not select a new response pair's geometry. `latticeDist` in `AKLT/Defs/Geometry.lean:11` adds the natural absolute values of two **integer** coordinate differences. There is no truncated natural subtraction, network distance, or spatial quotient.

Mathlib defines `Finset.sup` as a fold of supremum with bottom (`Mathlib/Data/Finset/Lattice/Fold.lean:44`); `sup_insert` at line 62 gives the finite supremum rule. For ℕ this is maximum with initial value zero (`Mathlib/Order/Nat.lean:28`). Consequently the definition takes the maximum of the two minimum distances, in exactly the paper's order. Distances and shifts are nonnegative integers, so the ℕ codomain imposes no extra restriction or rounding. Its empty-set value zero cannot affect an actual response pair.

DECL: responseKappa PASS

Paper: `sec7-recursion.tex:522`–536 specifies the live neighbours, their coefficients, and aggregation by pair type and exact shift. The exact coefficient table is `sec7-recursion.tex:279`–285.

The sum includes each unordered response pair once, contributes its assigned coefficient exactly when both its type equals Y and its shift relative to row X equals s, and contributes rational zero otherwise. Mathlib's bounded sum is an ordinary sum over the named finite set (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:63`); it neither requires nor introduces a `Fintype Plane` instance. All pair families here are finite.

Checked the supplying definitions as well. `responseNeighbours` removes the arrival site by subtracting the incoming step. Initially this is the centre, because the incoming direction is west, namely `u-c`; later it is the preceding vertex. `departureCount` uses indices strictly before i, so `deadAt` means precisely centre or at least two earlier departures. With `i : Fin n`, the prefix clamp `min i.val n` is just i.val and `i.val+1 ≤ n`. The only natural subtraction, `i.val-1` in `wordIncoming`, occurs in the nonzero branch and is the actual preceding index.

On a true closed trail the outgoing neighbour is live, as justified in `sec7-recursion.tex:560`–570. The remaining live-neighbour count is therefore 2, 1, or 0. `powersetCard 2` yields respectively the three pairs with coefficients `(aτ,bτ,bτ)`, the sole outgoing pair with coefficient `b′τ`, or no pair. `pairCoefficient` uses the one-live-**other**-neighbour condition for `b′τ`, and its straight/turn Boolean matches the incoming/outgoing convention in `sec6-walks.tex:668`. All six rational table entries agree exactly with the paper.

The paper defines these rewards at lattice first visits. Although the Lean helper is total on all words and departure indices, its kernel use in `kernelLengthCoefficient` is restricted to `ClosedTrail X w` and `kernelOrdering w`, which contains only first visits. Thus no revisit reward or malformed word enters the kernel. The finite-set and rational operations introduce no missing side condition, extra hypothesis, or summability assumption; s ranges over ℕ exactly as the paper's nonnegative integer shift index.

DECL: kernelWitness PASS

Paper: `sec7-recursion.tex:572`–576 (Definition `d:kernel-order`) fixes `h = (1,5404319552844595/4503599627370496)` in B,C order; see also `app-input-contracts.tex:1181`.

The two branches give exactly these components. The declared codomain ℚ makes the numerals and division rational field operations, not natural-number division or floating-point arithmetic. Checked the rational field instance in `Mathlib/Algebra/Field/Rat.lean:27` and rational division in `Mathlib/Data/Rat/Defs.lean:125`–130. The denominator is the positive integer `2^52`, so division by zero is impossible. In particular, the C component retains the specified dyadic value: `6/5 - h_C = 1/22517998136852480 > 0`. Both components are positive, and no additional parameter or hypothesis changes the fixed witness.

DECL: kernelRho PASS

Paper: `sec7-recursion.tex:575`–576 fixes `ρ₀ = 993015/10^6`; its use as the adopted contraction ceiling is `sec7-recursion.tex:594`–605 and `app-input-contracts.tex:1182`.

The ℚ annotation forces rational division and a rational base for the natural power `10^6`, giving exactly `993015/1000000 = 198603/200000`. The same Mathlib rational field and division meanings cited for `kernelWitness` apply. The denominator is nonzero and `0 < kernelRho < 1`; there is no integer truncation, rounding, or degenerate zero ceiling. It is used unchanged with `kernelWitness X` in `PositiveVectorBound`, matching the paper's fixed constants.

Non-blocking remarks:

- Read the complete `Kernel.lean` and its project import chain: `Trails.lean`, `Domain.lean`, `PinModel.lean`, `Moment.lean`, and `Geometry.lean`. Relevant downstream uses and paper appendix explanations were also checked. Findings above concern only the five assigned declarations.
- The helpers have harmless total extensions outside the paper's intended inputs: for example, `responsePairType ∅ = B` and `pairShift X ∅ = 0`. Actual pair generators enforce cardinality two, and actual kernel rewards are evaluated on true trails at first visits. These extensions create no vacuous kernel interpretation. At length zero there is no departure index, and `ClosedTrail X w` is false because the fixed start differs from either target.
- A small Python check exhausted all 48 nonreversing incoming/outgoing and live-other-neighbour configurations, confirming pair counts, distance-two geometry, and opposite/perpendicular classification. Exact fraction checks confirmed the dyadic witness and contraction ceiling. No Lean process was run, and no input file was modified.
