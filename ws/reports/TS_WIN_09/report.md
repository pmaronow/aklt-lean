STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty | Finding |
| --- | --- | --- | --- | --- |
| [AKLT.Blueprint.Win.MarginalNormalizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:26) | `e:windowfactor` | **TRUE** | easy | Fibre numerators sum to the stated positive original normalizer. |
| [AKLT.Blueprint.Win.OriginalFactorizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:32) | `e:cutfactorization` | **TRUE** | hard | The disjoint pieces split every factor, retaining only original legs. |
| [AKLT.Blueprint.Win.ComponentPinsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:42) | `l:cut` | **TRUE** | medium | Retained G₁ pins end in B; retained G₂ pins end outside F. |
| [AKLT.Blueprint.Win.WindowWeightPositiveStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:53) | `l:cut` | **TRUE** | easy | Proper colouring makes every window bond at least frameBound > 0. |
| [AKLT.Blueprint.Win.WindowRewriteStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:59) | `l:cut` | **TRUE** | medium | Positive exterior-only factors cancel when the weights are normalized. |
| [AKLT.Blueprint.Win.BoundedTiltStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:82) | `l:cut` | **TRUE** | easy | Both normalizers are positive and obey the required exponential bounds. |
| [AKLT.Blueprint.Win.OverlapMinorizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesCut.lean:93) | `l:cut` | **TRUE** | easy | The shared minorization bounds the overlap; the Fintype binder is retained. |
| [AKLT.Blueprint.Win.TailExponentialStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/NodesTail.lean:10) | `t:cutMOS` | **TRUE** | medium | The tenth exponential-series term gives exactly the stated constant. |

All eight leaves are true as written and self-sufficient. No missing premises or corrections were found. Difficulty estimates refer to implementing the proof in Lean; the factorization has the most substantial finite-set and configuration reindexing.

The repository was read at commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, using Lean `v4.35.0-rc2`. The paper comparisons use [the cut lemma and its factorization equations](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:128), [the tail estimate](/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:714), [original-leg definitions and finite-network positivity](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:97), and [the actual three-frame construction](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:341).

The definition audit followed `marginalNumerator`, `SeparatingCut`, `NoBond`, `cutPins`, `componentSum`, `windowWeight`, `cutError`, `logRatio`, `tailCost` and `tailConstant` in [Win/Defs.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Win/Defs.lean:93); the probability definitions in [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:8); the configuration, boundary, weight and marginal definitions in [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:10); and the retained-leg partition sums and partition ratio in [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9). It also followed their geometric and vector definitions in [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8), [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9), and [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:34), including all clauses used from [ThreeFramesStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Quantum.lean:13).

The empty-volume and empty-window cases use the unique function from an empty site subtype to the twelve-letter alphabet. They are legitimate cases of these statements. In the overlap statement alone, an empty state type makes the probability hypotheses impossible; the full leaf still has many satisfiable instances and is not classified VACUOUS. The positivity assumptions in WindowRewrite are consistent with the paper’s finite-network positivity argument, including arbitrary removal sets.

**MarginalNormalizationStatement — TRUE; easy.** The fibres of the restriction map partition the finite configuration space, so the sum of marginalNumerator over all window configurations equals the original planeWeight normalizer. The stated strict positivity makes that denominator nonzero. No positivity of individual planeWeight values or proper-colouring hypothesis is needed. Empty windows and empty volumes are covered by their unique empty configurations.

Proof route:

1. Exchange the two finite sums and sum the equality indicator over the window configurations to recover the original normalizer.
2. Unfold planeMarginal, marginal, planeLaw and normalize; distribute division by the common nonzero normalizer through each fibre sum.

Lean traps: `marginalNumerator` sums unnormalized `planeWeight`, while `planeMarginal` sums normalized `planeLaw`. Keep these denominators distinct until the fibre-sum identity is established. Equality indicators and function extensionality may require `classical`. The map into configurations on B is total because `extendLetters` has a default; B ⊆ F ensures it is the intended restriction. No individual-weight positivity premise is missing.

Fix: None.

**OriginalFactorizationStatement — TRUE; hard.** SeparatingCut implies that G1 and G2 are disjoint subsets of G = F \ B whose union is G \ X, with no internal bond crossing the pieces. The surviving configuration type therefore splits as the product of the two component configuration types, the site-weight exponent splits by cardinality, and each retained original-leg factor belongs to exactly one piece. componentSum G H removes G \ H from the original G; it creates no leg into X. The same finite-sum factorization applies with all pin factors omitted, including empty pieces.

Proof route:

1. Reindex configurations on G \ X by configurations on the disjoint pieces; split the site cardinality, internal bonds and retained original-leg factors.
2. Apply finite sum/product distributivity, identify the componentSum definitions, and repeat after omitting leg factors for freeSum.

Lean traps: Derive G₁ ⊆ G and G₂ ⊆ G from their union equality before identifying G \ (G \ Gᵣ) with Gᵣ. `Finset Plane` supplies finite subtypes; the ambient Plane remains infinite. Reindex dependent function spaces carefully. Replacing `componentSum G H` by `pinnedSum H ∅` changes the original legs and would invalidate the intended identity. Empty components have one configuration and partition sum 1.

Fix: None.

**ComponentPinsStatement — TRUE; medium.** For a retained original leg with tail in G1, its endpoint is outside G = F \ B and cannot be outside F by SeparatingCut, so it lies in B and cutPins uses only s. For a retained leg with tail in G2, NoBond G2 B excludes B and cutPins uses only eta. Other original legs have removed tails and contribute 1. Thus both claimed independences hold term by term without a proper-colouring premise.

Proof route:

1. Use the endpoint and adjacency conditions in originalLegs and SeparatingCut to classify every retained leg on each component.
2. Unfold componentSum, pinnedSum and cutPins, compare retained factors pointwise, and discard all factors with removed tails.

Lean traps: An original leg is indexed by its tail and endpoint, and its pin assignment is a dependent function on the original finite leg set. Removed-tail factors are 1 even if their pin values change. Use adjacency from `originalLegs`, rather than treating every outside point as adjacent. The `unit` proof is used to construct the UnitVector subtype; no extra proper-colouring assumption is required for these equalities.

Fix: None.

**WindowWeightPositiveStatement — TRUE; easy.** ThreeFramesStatement explicitly supplies 0 < frameBound and frameBound <= 1 + dot(frameVector i a, frameVector j b) for distinct colours. Every internalBonds B edge is a genuine nearest-neighbour pair, so ProperPlaneColouring supplies distinct colours. The real site factor (1/12)^B.card and every bond factor are strictly positive. For B empty the weight is 1; the configuration space is still a singleton.

Proof route:

1. Extract the positive frameBound and the cross-frame lower bound, and apply ProperPlaneColouring to each internalBonds edge.
2. Multiply the strictly positive bond factors and the strictly positive real site factor, using the empty-product convention.

Lean traps: Use the cross-colour lower bound, which requires proving the colours differ on each `internalBonds` edge. A bound for arbitrary equal colours would fail at antipodal letters. The site weight `(1 / 12 : ℝ)` is real division; its power has a natural exponent. Empty B gives weight 1, not an empty configuration domain.

Fix: None.

**WindowRewriteStatement — TRUE; medium.** Fix an exterior assignment eta0 and a window assignment s0, both available as constant IcoLetter functions. Write Z(eta,s) for the full pinned sum, ZX for the removed pinned sum, Q and QX for the corresponding free sums, A(s) for component G1 at eta0, and C(eta) for component G2 at s0. The supplied independence and factorization give ZX(eta,s)=A(s)*C(eta). With w(s)=windowWeight(s)*A(s), the definition of cutError gives w(s)*exp(-cutError(eta,s))=[QX/(Q*C(eta))]*windowWeight(s)*Z(eta,s). Every factor and denominator is positive by the explicit hypotheses; the bracket depends only on eta and disappears on normalization. The free factorization equation is not a missing premise: its two free sums can be absorbed directly into this scalar.

Proof route:

1. Choose fixed boundary and window assignments, use component independence, and set w(s)=windowWeight(s)*componentSum(G,G1,cutPins(eta0,s)), which is positive.
2. Expand cutError using positive partition ratios and the given pinned factorization; the tilted weight is a positive eta-only scalar times the weight in the supplied marginal formula, so normalization agrees.

Lean traps: `Real.log` algebra must use positivity of all pinned/free sums and their ratios; log is defined even at zero, so unconditional log cancellation would be invalid. The supplied global positivity hypothesis covers component sums by taking removal set G \ Gᵣ. Its quantification over arbitrary Y is consistent: only G \ Y enters the survivor set, and the original four-direction incidence bound is preserved. Choose fixed eta₀ and s₀ using the nonempty letter alphabet. Quantifier order requires one w independent of eta. A separate free-factorization premise is unnecessary.

Fix: None.

**BoundedTiltStatement — TRUE; easy.** The explicit Fintype and Nonempty hypotheses and pointwise strict positivity of w give a strictly positive finite normalizer. The error bound gives exp(-E) <= exp(-e(s)) <= exp(E), hence the tilted normalizer lies between those multiples of the base normalizer. Dividing yields the displayed factors exp(-2E) and exp(2E), and both normalized weights have full support and sum one.

Proof route:

1. Prove both finite normalizers positive, sum the pointwise exponential bounds, and verify normalization and full support.
2. Divide the numerator bounds by the opposite normalizer bounds and combine exponentials to obtain both pointwise comparisons.

Lean traps: Keep `[Nonempty Ω]`: pointwise positivity on an empty type would otherwise hold while the partition sum is zero. `normalize` itself does not assert positivity or mass one. Prove both denominators positive before inequalities involving reciprocals, and use monotonicity of exp with the signs in `exp (-e s)`.

Fix: None.

**OverlapMinorizationStatement — TRUE; easy.** The elaborated statement uses its explicit anonymous Fintype argument in all three Probability hypotheses and in totalVariation; no finite-type instance is dropped. Summing |p-q| = p+q-2*min(p,q) gives TV = 1-sum min(p,q), and both pointwise minorization hypotheses imply sum min(p,q) >= p0*sum nu = p0. An upper premise p0 <= 1 is unnecessary because it follows by summing either minorization. The empty type cannot satisfy Probability and is only an excluded degenerate case, not a vacuity of the full leaf.

Proof route:

1. Expand totalVariation, use the pointwise absolute-value/minimum identity, and substitute the two probability sums to obtain TV = 1 - sum min(p,q).
2. Sum p0*nu <= min(p,q) and use Probability nu to conclude TV <= 1-p0.

Lean traps: Lean prints the binder as `(x : Fintype Ω)` and uses exactly x in all three Probability terms and in totalVariation. No instance is dropped. The binder is explicit, so callers pass the finite-type instance explicitly. `Probability` allows zero atoms and does not supply `[Nonempty Ω]` as a typeclass, but its mass-one clause rules out the empty type. No separate p₀ ≤ 1 premise is needed.

Fix: None.

**TailExponentialStatement — TRUE; medium.** For s=sqrt(sqrt(u)) and u>=1, s>=1 and s^4=(u:Real), so 4*(2*u+1)^2<=36*s^8. With c=-log(theta)>0 and r=c*s/12>0, the tail is at most 36*theta^(-1)*s^8*exp(-r). The exponential-series bound r^10/10!<=exp(r) gives exactly 36*theta^(-1)*10!*(12/c)^10*s^(-2), the stated tailConstant times integer power of shellSpacing. The tail exponent is a real exponent and its subtraction is not truncated natural subtraction. All inverses have positive denominators; u=1 is allowed and the excluded cases theta=0 or theta=1 are not used.

Proof route:

1. Establish s>0 and s^4=u, bound the polynomial prefactor by 36*s^8, and rewrite the real power as theta^(-1)*exp(-(-log(theta))*s/12).
2. Apply Real.pow_div_factorial_le_exp at r=(-log(theta))*s/12 and exponent 10, invert positive quantities, and cancel powers to recover tailConstant(theta)*s^(-2).

Lean traps: `shellSpacing u` is `Real.sqrt (Real.sqrt (u : ℝ))`, with no flooring. Lean elaborates the theta power with real exponent and the final s power with integer exponent -2. The squares, tenth power and factorial are natural-number operations with real coercions where needed. Establish s > 0 and -log θ > 0 before division; θ = 0, θ = 1 and u = 0 are excluded by the stated hypotheses. There is no truncated natural subtraction in the exponent.

Fix: None.

Validation used one scratch Lean process at a time, importing the existing compiled modules without building the repository. [Inspect.lean](/home/ubuntu/aklt/reports/TS_WIN_09/scratch/Inspect.lean) contains only declaration inspection, type checks and instance synthesis; [Inspect.log](/home/ubuntu/aklt/reports/TS_WIN_09/scratch/Inspect.log) records successful elaboration, both empty-domain configuration Nonempty instances, the retained Fintype binder, the power types, and the available `Real.pow_div_factorial_le_exp` lemma. Mathlib packages are linked by a symlink inside scratch.

Supplemental floating-point checks in [numeric_checks.json](/home/ubuntu/aklt/reports/TS_WIN_09/scratch/numeric_checks.json) cover three valid separating cuts (empty, one empty piece, and two nonempty pieces), both pinned and free factorization, positive-scalar rewrite algebra, and 63 tail parameter pairs. Tail checks include u = 1 and use c = -log θ with log-scale comparison to avoid overflow. These checks supplement the mathematical audit and are not formal proofs. No Lean proofs were written, no sub-agents were launched, and the repository was not modified.
