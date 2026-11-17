STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty |
| --- | --- | --- | --- |
| `DensityComparisonStatement` | `l:density` | TRUE | hard |
| `ConditionalBlockComparisonStatement` | `l:comparison` | TRUE | hard |
| `MultiplicityEstimateStatement` | `l:comparison` | TRUE | easy |
| `HammingPathStatement` | `l:contraction` | TRUE | medium |
| `LipschitzCouplingStatement` | `l:contraction` | TRUE | medium |
| `LipschitzEigenvalueStatement` | `l:contraction` | TRUE | medium |
| `ReversibleEigenvalueGapStatement` | `l:contraction` | TRUE | hard |
| `BlockAverageFormStatement` | `l:contraction` | TRUE | medium |

All names in the table have prefix `AKLT.Blueprint.Gap.` and are in `AKLT.Blueprint.Gap.NodesFinite`. All eight statements are true and self-sufficient as written. No correction or additional premise is required. None is globally vacuous. The legitimate one-configuration cases are explicitly intended by the paper. Difficulty estimates include establishing the needed facts from the definitions, without assuming any sibling `Statement` proposition.

Audited repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. Exact statements: [NodesFinite.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:176). Paper arguments: [density](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:163), [comparison](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:253), and [contraction](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:297), together with [conditional projections](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:23). Machine-readable verdicts, recorded during the audit: [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_GAP_03/verdicts.jsonl).

## Definition audit

The exact definitions reachable from these leaves were read, including the real and complex normalization conventions:

| Source | Definitions and checked meaning |
| --- | --- |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:8) | `Weight` is a real-valued function; `PositiveProbability` includes strict positivity **and mass one**; `Probability` includes nonnegativity and mass one. `normalize` divides by the actual finite sum. `expectation` and `complexMean` are weighted sums; `variance` is the weighted sum of complex squared deviations from that complex mean. |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:39) | `AgreeOutside U` fixes exactly coordinates outside `U`. `conditionalExpectation` divides a complex fibre sum by its complex mass. `blockDirichlet` is the integrated squared conditional residual; `conditionalVariance` uses the same fibre with a real denominator. `dirichlet` sums the singleton forms, with rate one per site. `PoincareLower` is the inequality for every complex function, including zero-variance cases. |
| [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:84) | `hamming` counts differing actual coordinates in `Finset.univ`. `Coupling` requires nonnegative entries and both full marginals. |
| [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:41), [FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:49) | `conditionOn` normalizes the event-filtered weight; `marginal` sums over the exact fibres of the supplied map. |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:15) | `Config S` retains dependent alphabets. `restrict U` maps to configurations on the subtype of sites in `U`; `fibre` conditions on the full exterior; `blockLaw` pushes that fibre to precisely those block coordinates. |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:37) | `weightedInner` conjugates its first argument. `blockForm` sums over labels. `blockAverage` divides the sum of full-state fibre kernels by the real cast of the number of labels. `Reversible` includes stochastic rows and detailed balance. `kernelForm` is `A` times the real part of the weighted inner product with `(I-K)f`. |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:66) | `lipschitz` is the real supremum of all edge oscillations **with zero inserted**. `kernelMean` is the real row expectation. `couplingCost` is the expected real cast of Hamming distance. |
| [Mathlib complex scalars](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Basic/Complex/Basic.lean:498) | `star` on complex numbers is conjugation; `Complex.normSq z` is `z.re*z.re + z.im*z.im`. The complex variance and quadratic form therefore split into their real and imaginary parts. |

Every conditional fibre used here contains its conditioning configuration, whose weight is strictly positive. Its real mass is consequently positive, and its complex cast is nonzero. No conclusion relies on Lean's value for division by zero.

## Leaf findings and proof routes

### DensityComparisonStatement — TRUE, hard

The supplied site laws make the product reference a positive probability. The conditional least-squares characterization gives the lower Dirichlet comparison with factor `m`; testing the constant product mean gives the upper variance comparison with factor `M`. Product tensorization then loses exactly one ratio, `m/M`. No extra relation between `m` and `M` is needed. For zero sites both forms vanish.

Route 1: Establish the conditional and constant centering minima, then apply the two pointwise density bounds.<br>
Route 2: Establish tensorization from commuting product coordinate projections, combine the inequalities, and divide by `M > 0`.

Lean cautions: `f` is complex-valued; conditional means for the two laws differ, so compare their variational minima rather than their residuals pointwise. All density factors and `m/M` are real. The zero-site product has one configuration, not an empty state space.

### ConditionalBlockComparisonStatement — TRUE, hard

For a fixed exterior, `blockLaw` is the positive conditional probability on block coordinates. Further conditioning on all block sites except one fixes exactly the original complement of that site. The supplied uniform conditional gap therefore yields the integrated block-to-single-site inequality. Summing over labels produces the stated multiplicity. Empty blocks and empty label types give zero contributions; the paper's nonempty-family condition is unnecessary for this intermediate inequality.

Route 1: Identify the conditional block law and its nested singleton conditional variance using the dependent configuration extension with fixed exterior.<br>
Route 2: Integrate the given block Poincare inequality over exteriors, sum labels, and interchange finite sums.

Lean cautions: The block index type is the subtype `↥(B a)`, and its alphabet is `S x.val`. A singleton inside this subtype must be related to the corresponding singleton in `ι`. `blockLaw` is a law on block coordinates; `fibre` is a law on full configurations. No global block-gap premise is required by this leaf.

### MultiplicityEstimateStatement — TRUE, easy

Each singleton form is nonnegative directly from the positive weights and squared norms. Multiplying the supplied natural multiplicity bound by this form and summing gives the result. No conditional-law identity is needed. Omitting explicit `Nonempty (S x)` instances is harmless: no configuration witness is used, and mass one already rules out an empty configuration space.

Route 1: Prove each singleton form is nonnegative and cast each multiplicity bound from `ℕ` to `ℝ`.<br>
Route 2: Sum the termwise inequalities, factor out the real cast of `t`, and unfold `dirichlet`.

Lean cautions: Multiplicity counts labels in `Fintype J`, so repeated block values are counted repeatedly. Cast the cardinality comparison before multiplying. Empty `J`, `t = 0`, and empty site types require no maximum or nonempty witness.

### HammingPathStatement — TRUE, medium

The set of edge oscillations is finite, and inserting zero makes it nonempty. Its real supremum is therefore the intended nonnegative maximum. Updating only coordinates where two configurations differ gives a path of exactly their Hamming distance. Zero seminorm consequently means constant on the product. With no sites or all singleton alphabets the product has one configuration and the seminorm is zero.

Route 1: Bound every edge oscillation by the finite supremum and sum along coordinate updates through the differing sites.<br>
Route 2: Use the path estimate and a configuration witness for the forward zero-seminorm implication; evaluate the constant oscillations for the reverse implication.

Lean cautions: `sSup` on `ℝ` uses conditional completeness: establish boundedness before applying `le_csSup`, and use the inserted zero for nonemptiness and nonnegativity. Hamming distance is a natural number, coerced to real in the estimate. Updates must preserve the dependent alphabet at each site.

### LipschitzCouplingStatement — TRUE, medium

The coupling marginals rewrite the difference of row means as the coupled mean of output differences. Nonnegativity of coupling masses and the Hamming path estimate bound this by `lipschitz f * couplingCost`, hence by `r * lipschitz f`. This bounds every edge of the output function. The inserted zero is bounded too because `r` and the seminorm are nonnegative. The cases `r = 0` and a singleton product are valid.

Route 1: Apply the Hamming path bound inside the coupling for each neighboring input pair and use its two full marginals.<br>
Route 2: Apply the expected-cost bound and take the supremum of all output edge oscillations together with zero.

Lean cautions: `f` and `kernelMean` are real-valued here. The existential coupling may depend on the input pair; no simultaneous selection or consistency premise is needed. Prove the scalar multiplying `couplingCost` is nonnegative before using its upper bound.

### LipschitzEigenvalueStatement — TRUE, medium

A constant function of zero `p`-mean is zero because `p` has mass one. The nonzero-value hypothesis therefore makes the eigenfunction nonconstant, with positive seminorm. Homogeneity and contraction give the stronger conclusion `|eigenvalue| ≤ r`, which implies the requested upper bound. There is no missing stochasticity, reversibility, or stationarity premise for `K` in this step.

Route 1: Exclude constant nonzero mean-zero functions and obtain a strictly positive edge maximum using product connectivity.<br>
Route 2: Use absolute homogeneity of the seminorm and the eigenfunction equation, apply contraction, and cancel the positive seminorm.

Lean cautions: The eigenfunction, eigenvalue, and mean are real. Homogeneity uses `|eigenvalue|`, including negative eigenvalues. The witness `(∃ σ, f σ ≠ 0)` is present. On a one-configuration space that witness is incompatible with mean zero, as intended; the entire leaf is not vacuous.

### ReversibleEigenvalueGapStatement — TRUE, hard

Stochastic rows preserve constants, and detailed balance gives stationarity and self-adjointness in the positive weighted real inner product. The mean-zero subspace is invariant and has a real orthonormal eigenbasis. The supplied eigenvalue bound gives the required lower bound on each eigencomponent of `A(I-K)`. Constants contribute nothing. Adding the inequalities for the real and imaginary parts gives exactly the complex conclusion. Negative eigenvalues improve this lower bound, so positivity of the operator `K` is unnecessary.

Route 1: Conjugate by the positive diagonal `sqrt(p)`, diagonalize on the invariant mean-zero subspace, and apply the supplied bound to its eigenvectors.<br>
Route 2: Expand the centered real quadratic form, eliminate constants using stochasticity and stationarity, then add the real and imaginary inequalities.

Lean cautions: `Reversible` includes row normalization; this is not merely a symmetry equation. Use the weighted inner product or its diagonal conjugate, rather than treating `K` as symmetric in the unweighted coordinates. `kernelForm` is the real part of `A⟨f,(I-K)f⟩`, not `A‖f-Kf‖²`. `A > 0` makes `c/A` legitimate. A zero-dimensional centered subspace and the endpoint `c = A` are both included.

### BlockAverageFormStatement — TRUE, medium

Every conditional row is a probability and satisfies detailed balance: equal exteriors have the same positive fibre denominator, and unequal exteriors give zero transitions in both directions. Averaging over labels preserves these properties. The explicit `[Nonempty J]` guarantees a positive averaging denominator. Multiplication by `card J` cancels that normalization, and the conditional projection identity identifies each remaining summand with the corresponding block form. Empty and repeated blocks are harmless.

Route 1: Establish positive fibre normalizers, row normalization, and detailed balance, then average over the finite nonempty label type.<br>
Route 2: Expand `card J * (I-blockAverage)` as the labelled sum of `I-E_B` and identify each quadratic form through conditional orthogonal projection.

Lean cautions: The natural `Fintype.card J` is coerced to real both in the averaging denominator and the `kernelForm` parameter. Its nonzero proof comes from `[Nonempty J]`, which Lean's printed declaration retains. Use full-state `fibre` rows for the kernel action. No nonempty-block assumption is needed: an empty block contributes the identity kernel and zero form.

## Verification and limits

[Inspect.lean](/home/ubuntu/aklt/reports/TS_GAP_03/scratch/Inspect.lean) imported the existing built module with Lean `v4.35.0-rc2` and printed all eight elaborated declarations plus the key definitions. It completed with exit code zero; [inspect.log](/home/ubuntu/aklt/reports/TS_GAP_03/scratch/inspect.log) retains the output. The finite type and alphabet instance binders, label nonemptiness for averaging, real coercions, and real/complex function types are present. No instance-dropping defect was found. Classical decidability supplies finite filters, agreement predicates, and equality on configurations; writers can use `classical` without additional hypotheses.

[finite_checks.py](/home/ubuntu/aklt/reports/TS_GAP_03/scratch/finite_checks.py) completed **23,225 exact rational assertions**; [finite_checks.json](/home/ubuntu/aklt/reports/TS_GAP_03/scratch/finite_checks.json) records counts. It used alphabet-size tuples `()`, `(1)`, `(1,1)`, `(2)`, `(3)`, `(2,2)`, `(1,3,2)`, and `(2,2,2)`. Checks covered density form comparisons, conditional gaps and their integration, multiplicities, averaging identities, Hamming bounds, explicit neighbor couplings, and spectral examples. Quadratic form inequalities were checked for all functions on each sampled finite law by exact matrix positive-semidefiniteness tests; path and Lipschitz checks used enumerated or sampled real functions. Empty and repeated blocks, empty label families where permitted, `r = 0`, `c = A`, a negative reversible eigenvalue, a non-stochastic signed kernel for the Lipschitz eigenvalue leaf, and the complex real/imaginary split were included.

These finite checks support the definition audit; they are not formal proofs of the universally quantified leaves. No proofs were written, no sub-agents were launched, and the repository was not modified. Only one Lean process was used, for the inspection module; existing repository and Mathlib build artifacts were read through `LEAN_PATH`, with the package symlink under this report's scratch directory.
