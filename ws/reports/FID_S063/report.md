STATUS: PASS
BLOCKING: 0

DECL: conditionalVariance PASS

Matches `d:framemodel`, `sec3-quantum-frames.tex:508–509`, and the explicit finite-fibre definition in `app-finite.tex:4–16`: `Var_U f = E_U |f - E_U f|²`. `AgreeOutside U σ τ` fixes precisely the coordinates outside `U`; the dependent function type is the full configuration product, not a selected subset of configurations. The numerator sums the squared residual with weights `p τ`, and the denominator is the exterior marginal mass. Using `conditionalExpectation p U f τ` inside this sum is correct: configurations agreeing outside `U` have identical fibres and therefore identical conditional means.

Mathlib checks: `Complex.normSq z` is `z.re * z.re + z.im * z.im`, is nonnegative, and vanishes exactly at zero (`Mathlib/Basic/Complex/Basic.lean:508–565`). Thus this is the squared complex modulus required by `sec1-result.tex:139–142`, not the complex square. The real-to-complex coercion is the inclusion `r ↦ (r,0)` and preserves sums and division (`Basic/Complex/Basic.lean:81–103,732`; `Basic/Complex/BigOperators.lean:29`). Consequently the denominator in the conditional mean is exactly the complex inclusion of the real denominator here. `Pi.instFintype` enumerates the entire dependent product (`Data/Fintype/Pi.lean:133–143`), and bare sums are sums over `Finset.univ` (`Algebra/BigOperators/Group/Finset/Defs.lean:170`). For a positive probability, the fibre contains `σ`, so its mass is at least `p σ > 0`; totalized division by zero is never used on the paper's domain. An empty block gives zero conditional variance, and the full block gives the ordinary variance.

DECL: blockDirichlet PASS

This auxiliary definition is the integrated conditional variance used in `d:framemodel`, `sec3-quantum-frames.tex:530`, and Lemma `l:CE`, `app-finite.tex:28–34,38–55`: `μ(Var_U f) = ‖f - E_U f‖²_μ`. It implements the right-hand side directly as `∑ σ, p σ * |f σ - E_U f σ|²`. To check the equality rather than assume it, group configurations by exterior fibre `F`, with mass `m_F > 0`. The conditional variance is constant on that fibre, and its contribution after integration is

`(∑ σ ∈ F, p σ) * (∑ τ ∈ F, p τ * |f τ - E_U f τ|²) / m_F`

`= ∑ τ ∈ F, p τ * |f τ - E_U f τ|²`.

Thus there is no missing conditional expectation or fibre denominator. The finite sums and `Complex.normSq` have the meanings checked above. This also fixes the operator sign: the form belongs to `I - E_U`, as in the paper, and is nonnegative. For `U = ∅` it is zero; for the full block it is the global variance.

DECL: dirichlet PASS

Matches `d:framemodel`, `sec3-quantum-frames.tex:511,515,530–531`, and the update convention in `sec1-result.tex:145–146`. The sum is over every physical site `x : ι` exactly once, and the block `{x}` is a singleton `Finset ι`. By the preceding fibre calculation each summand is `μ(Var_x f)`. There is no volume normalization or extraneous factor of one half. The resulting nonnegative form is associated with `-L = ∑ x (I - E_x)` for the paper's `L = ∑ x (E_x - I)`.

Mathlib's `Fintype` supplies an exhaustive finite enumeration without duplicates (`Data/Fintype/Defs.lean:53–61`), and `∑ x` is its ordinary finite sum, not an average. The `DecidableEq ι` and `classical` machinery determine membership and singleton operations and impose no mathematical restriction on finite site sets. An empty site set gives a zero sum and a product with one empty configuration, as required by `app-finite.tex:4–6`.

DECL: PoincareLower PASS

Matches the Poincare convention in `sec1-result.tex:140–145`, `d:framemodel`, `sec3-quantum-frames.tex:515–516`, and `app-finite.tex:18–20`. It says exactly `g * Var_p(f) ≤ D_p(f)` for every complex-valued function on the whole configuration space. The inferred domain of `f` is `((x : ι) → S x) → ℂ`; there is no hidden restriction to real functions, nonconstant functions, or a particular test subspace. `variance` expands to `∑ σ, p σ * |f σ - ∑ τ p τ f τ|²`, the probability variance with squared complex modulus. Multiplication and comparison are in `ℝ`, and the inequality has the correct direction.

For a normalized one-point law the mean is `f` itself, so both variance and Dirichlet form vanish and the predicate holds for every real `g`, exactly as the paper specifies. Allowing a real parameter `g` without separately conjoining `0 < g` is appropriate for a lower-bound predicate: at positive `g` it is precisely the stated positive-gap assertion; nonpositive lower bounds remain valid inequalities. No positivity conclusion is being smuggled into the predicate. The actual plane-law use asserts `PositiveProbability` alongside the bound (`AKLT/Blueprint/Top/Quantum.lean:84–93`), and the torus probability assertion is explicit at lines 94–95.

DECL: heatBathGap PASS

Matches the infimum in `d:framemodel`, `sec3-quantum-frames.tex:512–513`, including the explicit one-point convention in `sec1-result.tex:143–145`. The subtype index consists of all complex functions whose actual global variance is strictly positive. Hence every quotient divides by a strictly positive real number, and constants are excluded precisely when their variance is zero. The numerator is the correctly normalized site Dirichlet form checked above.

Mathlib checks: `ENNReal` is `WithTop ℝ≥0`, with a complete linear order and top denoted `∞` (`Basic/ENNReal/Basic.lean:100–110,153–154`). `ENNReal.ofReal` sends a nonnegative real to that same finite extended real and clips negative inputs to zero (`Basic/ENNReal/Basic.lean:230–265`). Here each quotient is nonnegative for a positive probability, so clipping does not change any value. Indexed infimum is the infimum of the range (`Order/SetNotation.lean:58–71`, via `to_dual`); an empty indexed infimum in this complete lattice is top (`Order/CompleteLattice/Basic.lean:704–712`, dual theorem `iInf_of_empty`). On a one-point probability space every variance is zero, so the subtype is empty and the result is exactly `∞`, not zero. If the positive finite configuration space has at least two points, an indicator of one point has positive variance and a finite quotient, so this definition cannot accidentally produce infinity there. No coercion back to `ℝ` collapses infinity.

Non-blocking remarks

- The entire `Probability.lean` file was read; its sole import is the Mathlib umbrella. The relevant Mathlib definitions, coercions, finite-product enumeration, field division, and lattice conventions were inspected directly. Consumer definitions in `FrameModel.lean` and the probability and Poincare assertions in `Blueprint/Top/Quantum.lean` were checked for context; only the five assigned declarations are judged here.
- These are total formulas on `Weight Ω = Ω → ℝ`, not assertions that every weight is a probability. Their probabilistic interpretation uses the paper's positive normalized laws, whose positivity and normalization are explicit conclusions in the interface. On that domain, empty alphabets are impossible: an empty configuration product has total mass zero, contradicting normalization to one; an existing configuration supplies a letter at every site. Thus omission of `Nonempty (S x)` from these generic formula signatures creates no vacuous paper case. Outside that domain, division by zero in `ℝ` or `ℂ` returns zero (`Algebra/GroupWithZero/Basic.lean:402`), and signed weights can make `ofReal` clip a quotient. Those total extensions must not be interpreted as probability claims; they do not alter the definitions on the paper's domain.
- There is no natural-number subtraction in these declarations. Function subtraction is in `ℂ`; fibre division and Rayleigh quotients use the usual fields `ℂ` and `ℝ`.
- Exact rational checks with nonuniform positive weights and complex-valued functions verified fibre-constant means, nonnegative conditional variances, equality of the two integrated forms, empty/full block identities, and singleton behavior for alphabet sizes `()`, `(1)`, `(1,1)`, `(2)`, `(2,3)`, and `(2,2,2)`. These supplement the algebraic comparison above; no Lean processes were run, and no inputs were modified.
