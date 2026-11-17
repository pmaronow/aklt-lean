STATUS: COMPLETE

All eight assigned leaves are **TRUE** and self-sufficient. No missing premise or corrected statement is needed. The empty-type branches forced by impossible probability hypotheses are ordinary degenerate cases; none of the eight closed statements is globally vacuous.

| Leaf in `AKLT.Blueprint.Gap` | Paper label | Verdict | Difficulty | Assessment |
| --- | --- | --- | --- | --- |
| [FibreNormalizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:16) | `l:CE` | **TRUE** | medium | The fibre contains sigma; patching any block assignment gives a positive atom. |
| [ConditionalProjectionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:24) | `l:CE` | **TRUE** | medium | Positive fibre averages are constant on fibres and give the stated projection. |
| [ConditionalVarianceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:35) | `l:CE` | **TRUE** | medium | The fibre residual has mean zero, so all relevant cross terms vanish. |
| [MaximalCouplingStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:44) | `l:finitecoupling` | **TRUE** | medium | The common diagonal part and residual product give a maximal coupling. |
| [CouplingMarginalTVStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:51) | `l:finitecoupling` | **TRUE** | medium | Diagonal mass is bounded by overlap; fibrewise triangle inequality gives contraction. |
| [MarginalCompletionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:58) | `l:finitecoupling` | **TRUE** | hard | Conditional fibre weights lift the specified coupling, including zero marginal fibres. |
| [HammingLocalizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:66) | `l:finitecoupling` | **TRUE** | easy | The pointwise Hamming estimate integrates under every full-law coupling. |
| [CommonMinorizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:74) | `l:finitecoupling` | **TRUE** | easy | The common minorant has mass t, so the overlap is at least t. |

Reviewed repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The exact statements are in [NodesFinite.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:16). The paper arguments are [app-finite.tex, l:CE](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:22) and [app-finite.tex, l:finitecoupling](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:68), Lemmas A.1 and A.2. The source definitions, rather than their comments alone, determine the verdicts.

**Definition closure inspected.** The following are all AKLT definitions reached by the eight statements; the notation below is explanatory, with `E = conditionalExpectation p U` and `m = complexMean p f`.

| Source | Definitions and exact mathematical content |
| --- | --- |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9) | `Weight Ω = Ω → ℝ`; `normalize w x = w x / ∑ y, w y`; `Probability` means every atom is nonnegative and the total is 1; `PositiveProbability` requires strict positivity and the same total. |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:24) | `expectation p g = ∑ x, p x * g x`; `totalVariation p q = (1/2 : ℝ) * ∑ x, abs(p x-q x)`; `complexMean p f = ∑ x, (p x : ℂ) * f x`; `variance p f = ∑ x, p x * Complex.normSq(f x-m)`. |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:40) | `AgreeOutside U σ τ` requires equality at every site outside the finite set `U`. `conditionalExpectation` is the complex weighted sum on that fibre divided by its complex mass. `conditionalVariance` is the real fibre average of `Complex.normSq(f τ-E f τ)`. `blockDirichlet` is the full-law sum `∑ σ, p σ * Complex.normSq(f σ-E f σ)`. |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:85) | `hamming σ τ` is the natural cardinality of the differing-site filter of `Finset.univ`. `Coupling p q` stores real mass entries, their nonnegativity, and exact first and second marginals. |
| [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:42) | `conditionOn p A` normalizes the weight `if A σ then p σ else 0`; it has no built-in positive-denominator hypothesis. |
| [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:50) | `marginal p r z = ∑ x, if r x=z then p x else 0`, using equality on the target type. |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:15) | `Config S` is the dependent product `(x : ι) → S x`; `restrict U` restricts to the subtype of sites in `U`; `AgreeOn U` requires equality on those sites; `fibre p U σ = conditionOn p (AgreeOutside U σ)`; `blockLaw` is the pushforward of that full-state fibre under `restrict U`. |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:38) | `weightedInner p f h = ∑ σ, (p σ : ℂ) * star(f σ) * h σ`, conjugate-linear in the first argument. |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:76) | `couplingCost c = ∑ σ, ∑ τ, c.mass σ τ * (hamming σ τ : ℝ)`; `disagreement c U = ∑ σ, ∑ τ, if AgreeOn U σ τ then 0 else c.mass σ τ`. |

`Complex.normSq` is the real squared modulus and `star` on complex numbers is conjugation. These leaves involve no quantum, geometric, specification, or other closed-leaf predicate despite their broad import chain.

**Individual findings and two-line proof routes.** These are routes for future writers, with no Lean proofs supplied. Difficulty estimates reflect finite-sum and dependent-type bookkeeping in Lean.

**`AKLT.Blueprint.Gap.FibreNormalizationStatement` — TRUE, medium.

For each supplied configuration sigma the exterior fibre contains sigma, so its real mass D is at least p(sigma)>0. Normalizing the restricted weight gives a probability. Every block assignment has an extension obtained by patching sigma on U; its positive atom makes the block marginal strictly positive. The complex denominator in conditionalExpectation is exactly the complex cast of D. Empty and full blocks, including the zero-site product, are valid. Lean traps: use dependent patching on the subtype U, distinguish full-state fibre (which has zero atoms off the fibre) from its strictly positive block marginal, and commute real-to-complex casts with sums and division; classical equality is needed for marginal.

Fix: none.

1. Bound the fibre mass below by p(sigma), normalize its indicator-restricted weight, and group its pushforward to the block coordinates.
2. Patch each block assignment into sigma to obtain positivity; move the nonzero real denominator through the complex finite sum to identify both means.

**`AKLT.Blueprint.Gap.ConditionalProjectionStatement` — TRUE, medium.

AgreeOutside U is an equivalence relation and every class has positive p-mass. On each class conditionalExpectation is its normalized weighted complex mean, so it is constant there and preserves 1. Grouping the original mean and weighted scalar product by these classes proves stationarity and self-adjointness. All hypotheses needed by the paper are explicit; no other named leaf is assumed. Lean traps: function equalities need extensionality, weights are real but the means and inner product are complex, star conjugates the first argument, and the class denominator must be shown nonzero before cancellation.

Fix: none.

1. Group configurations by their exterior restriction; each conditional mean is a constant normalized average on its positive-mass fibre, giving idempotence and preservation of constants.
2. Sum those fibre averages to preserve the original mean and express both inner products as the sum of fibre mass times conjugate(mean f) times mean h.

**`AKLT.Blueprint.Gap.ConditionalVarianceStatement` — TRUE, medium.

The residual g=f-E_U f has zero weighted mean on every exterior fibre. It is orthogonal to every fibre-constant function, including E_U f and E_U f-complexMean p f. Therefore the real part of the displayed inner product is the residual squared norm and the centered decomposition gives total variance. conditionalVariance is the fibre average of precisely that same residual normSq; integrating it preserves its expectation. Empty/full blocks and zero sites agree with the paper. Lean traps: blockDirichlet is defined directly as the residual norm sum, so the integrated conditional-variance equality is substantive; conditionalVariance uses E_U f at tau, which is constant on the fibre; distinguish complex orthogonality from its real-part conclusion and use Complex.normSq rather than a real square.

Fix: none.

1. Show by the finite fibre quotient that E_U f is fibre-constant, its residual has zero fibre mean, and conditional averaging preserves expectations.
2. Expand complex normSq using the vanishing cross terms, both against E_U f and after subtracting the global mean; integrate the residual fibre average to obtain the middle equality.

**`AKLT.Blueprint.Gap.MaximalCouplingStatement` — TRUE, medium.

The half-L1 definition and normalized nonnegative p,q imply TV=1-sum(min(p,q)). Let a=min(p,q) and T=sum a. For T<1 the diagonal a plus residual product (p-a)(q-a)/(1-T) has the stated marginals and residual diagonal zero. If T=1 then p=q=a pointwise, and the diagonal coupling works. This covers disjoint support, zero atoms and one-point spaces. On the empty type Probability is impossible, which is an intended degenerate instance rather than global vacuity. Lean traps: equality tests are resolved by the module-local classical instance, the half is real, and the T=1 case must not use field cancellation at a zero denominator.

Fix: none.

1. Sum abs(p(x)-q(x))=p(x)+q(x)-2 min(p(x),q(x)) and use both probability normalizations.
2. With overlap T<1 use the diagonal common part plus the normalized residual product, whose diagonal vanishes; with T=1 use the diagonal coupling p=q.

**`AKLT.Blueprint.Gap.CouplingMarginalTVStatement` — TRUE, medium.

Nonnegative coupling entries imply c(x,x)<=p(x) and c(x,x)<=q(x), while its total mass is 1. Thus its off-diagonal mass is at least 1-sum min(p,q)=TV. A finite pushforward groups signed differences by fibres, and the triangle inequality bounds its half-L1 norm by the original one. No surjectivity or positive-atom assumption is needed. Empty target types admit no map from a probability-bearing source, but the arbitrary-coupling conclusion remains substantive. Lean traps: marginal needs DecidableEq on its target, supplied here by the local classical instance; both outer and inner finite sums use Fintype.univ, and the triangle estimate must regroup the fibres without losing the real factor 1/2.

Fix: none.

1. Bound each diagonal entry by both coupling marginals, sum, and subtract the diagonal from total mass 1 using the overlap identity derived from half-L1.
2. Expand the two pushforwards, apply abs(sum)<=sum(abs) on each target fibre, and interchange sums so every source state is counted once.

**`AKLT.Blueprint.Gap.MarginalCompletionStatement` — TRUE, hard.

Write P=marginal p r and Q=marginal q r. On positive fibres define conditional weights p(x)/P(r(x)) and q(y)/Q(r(y)). The lift d(x,y)=c(r(x),r(y))*p(x)/P(r(x))*q(y)/Q(r(y)) has both full marginals and pushes forward to exactly the supplied c. If P(a)=0 or Q(b)=0, nonnegativity and the coupling marginals force the corresponding row or column of c to vanish; full weights on those fibres vanish too. Therefore zero fibres need no additional probability law, surjectivity, or strict positivity assumption. Lean traps: handle zero denominators separately (real division by zero is defined as zero), prove zero rows/columns pointwise from nonnegative finite sums, and preserve the arbitrary supplied coupling rather than replace it by a maximal one.

Fix: none.

1. Group by r-fibres and prove zero marginal mass forces every corresponding full atom and coupling row or column to be zero.
2. Lift c by the product of the two conditional fibre weights on positive fibres and zero otherwise; summing by fibres verifies both full marginals and every requested (a,b) mass.

**`AKLT.Blueprint.Gap.HammingLocalizationStatement` — TRUE, easy.

For any pair agreeing on U, all differing sites lie in Finset.univ minus U, so hamming<=card(complement U). For a pair disagreeing on U, hamming<=Fintype.card iota and the displayed weaker bound follows. Sum this pointwise estimate with the nonnegative entries of the same full-law coupling; its total mass is 1. The bound therefore holds for every coupling as quantified. The omitted Nonempty alphabet instances are not missing premises: a normalized probability on Config S already rules out an empty configuration type; zero sites instead give a singleton and both sides zero. Lean traps: U is a Finset of actual sites, disagreement concerns AgreeOn U rather than equality of whole configurations, and cast the natural cardinality bounds into the reals before summing.

Fix: none.

1. Split on AgreeOn U sigma tau: bound the differing-site filter by univ minus U in the agreement case and by all sites in the disagreement case.
2. Cast to the reals, multiply by each nonnegative c.mass, and sum; use total coupling mass 1 to obtain the constant term and the definition of disagreement for the other term.

**`AKLT.Blueprint.Gap.CommonMinorizationStatement` — TRUE, easy.

The supplied inequalities give t*nu(x)<=min(p(x),q(x)) pointwise. Summing and using sum nu=1 makes the overlap at least t, and the half-L1 overlap identity gives TV<=1-t. This directly includes t=0 and t=1, zero atoms and singleton spaces; no positive residual distribution is needed. On an empty type the probability hypotheses are impossible, as expected. Lean traps: t and all weights are real, the hypotheses are pointwise conjunctions, and the overlap identity must be derived locally rather than assumed as another unproved leaf. The bounds 0<=t<=1 are sufficient and stronger than what this short calculation needs.

Fix: none.

1. Obtain t*nu(x)<=min(p(x),q(x)) from the two pointwise minorization hypotheses and sum to get overlap>=t.
2. Derive TV=1-overlap from abs(p-q)=p+q-2 min(p,q) and the probability normalizations, then subtract the overlap bound from 1.

**Boundary cases and Lean traps.**

- The first three leaves explicitly quantify `[Fintype ι]`, `[DecidableEq ι]`, all alphabet `Fintype` instances, and `[∀ x, Nonempty (S x)]`. Lean declaration inspection confirms that the nonempty instances remain in the propositions. The leaves use `Type` (universe zero), while some underlying definitions are universe-polymorphic; this is a scope restriction, not a truth defect.
- The conditional denominator is positive because the supplied `σ` belongs to its own fibre and has positive weight. For `U = ∅`, the full-state fibre is the point mass at `σ`, the block law is the probability on the one empty block configuration, and `E_U = I`. For `U = univ`, the full-state fibre is `p` and `E_U` is the global-mean projection.
- With no sites, the dependent product still has one empty configuration. All conditional and variance conclusions have their intended singleton interpretation. If an alphabet is empty in the Hamming leaf, `Config S` is empty and its probability hypothesis is impossible; an extra `Nonempty` alphabet premise is therefore unnecessary.
- A probability on an empty state type would require `0 = 1`. This explains the empty-source branches of the coupling leaves. If a target type is empty and the source carries a probability, there is no map `r` to that target. For nonempty targets, maps need not be surjective; absent image points and other zero-mass fibres are handled by zero coupling rows or columns.
- No `DecidableEq Ω` or `DecidableEq Ξ` premise is missing. The modules install local classical decidability and a classical equality instance when elaborating the relevant definitions and propositions. A writer may need `classical` again in the proof environment. `Nonempty` supplies existence, not a chosen `Inhabited` value; dependent patching is available using the supplied configuration.
- All probability sums use actual `Fintype` enumerations, and blocks are `Finset` subsets of the site type. Subtype and dependent-function finiteness follow from the explicit instances. No unsupported conversion from a mere finite subset to a whole finite state type is involved.
- Probability masses, total variation, minorization parameters and costs are real. The conditional mean and scalar product are complex. `1/2` in total variation is real division, and the conditional complex denominator is the cast of a positive real sum. Cardinalities are natural numbers cast to reals where used in cost bounds. There is no truncated natural-number subtraction: the Hamming complement is a finite-set difference.
- At overlap 1, maximal coupling uses the common diagonal law; at overlap 0, the residual denominator is 1. Completion treats zero marginal fibres separately; no cancellation at zero is valid even though Lean defines division by zero as zero. Common minorization needs no residual construction, so both `t = 0` and `t = 1` are covered directly.
- Self-sufficiency does not require assuming another assigned statement. The overlap identity, fibre normalization, mean preservation and orthogonality used in routes are elementary consequences of the current hypotheses and may be established as local helper facts by each writer.

**Checks performed.** A single Lean 4.35.0-rc2 process loaded the compiled `NodesFinite` module and printed all eight propositions and relevant definitions with universe information. It exited successfully with `autoImplicit` and `relaxedAutoImplicit` disabled. The printed declarations were compared with the source: explicit hypotheses and quantifier order agree. This was declaration inspection, not a machine-checked proof of the leaves. See [inspect.lean](scratch/inspect.lean) and [inspect.out](scratch/inspect.out). Existing repository/package build artifacts were read via `LEAN_PATH`; the repository was not rebuilt or edited.

Independent exact-rational checks passed:

| Check | Cases |
| --- | ---: |
| Half-L1 overlap identity and maximal coupling | 251 |
| Arbitrary coupling matrices: TV lower bound | 531 |
| Pushforward maps: TV contraction | 8,456 |
| Lifting supplied marginal couplings | 25,368 |
| Common minorizations satisfying every premise | 4,617 |
| Positive product-space law/block/complex-function combinations | 297 |
| Pointwise Hamming localization | 779 |
| Integrated Hamming localization | 594 |

The coupling checks used all denominator-4 probability laws on one to three states, all maps to one to three target states, and maximal, independent, and averaged marginal couplings. The arbitrary joint-matrix checks enumerated all denominator-4 couplings on one to three states. Conditional checks used varying alphabets, nonconstant complex functions with rational coordinates, nonproduct positive weights, singleton alphabets, every block, and the zero-site product. The checks include zero atoms, non-surjective maps, zero marginal fibres, both overlap endpoints and both minorization endpoints. They support the analytic audit and do not replace its general reasoning. See [check_cases.py](scratch/check_cases.py) and [check_cases.out.json](scratch/check_cases.out.json).

The requested [verdicts.jsonl](verdicts.jsonl) contains exactly one object for each assigned full Lean name, in the requested order. Its schema, verdict values, difficulty values and two-line routes were validated. No proofs were written, no sub-agents were launched, and the repository working tree was unchanged.
