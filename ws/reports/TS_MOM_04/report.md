STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Finding |
|---|---|---|---|
| `AKLT.Blueprint.Mom.DepletedContractionStatement` | TRUE | easy | The D mean is `3A/(3A+2)` times the U mean whenever `A>0`. |
| `AKLT.Blueprint.Mom.MeanPathContinuityStatement` | TRUE | medium | The explicit normalizer is at least `1/2` for every real parameter. |
| `AKLT.Blueprint.Mom.MeanPathEndpointsStatement` | TRUE | medium | Endpoint means give squared norms `9/25` and zero. |
| `AKLT.Blueprint.Mom.MeanCovarianceStatement` | TRUE | medium | The scalar normalizer and vector numerator transform as required. |
| `AKLT.Blueprint.Mom.OrthogonalNormStatement` | TRUE | easy | `RᵀR=I` preserves the Euclidean sum of squares. |
| `AKLT.Blueprint.Mom.OrthogonalTransportStatement` | TRUE | medium | Identity or a Householder reflection handles equal lengths, including zero. |
| `AKLT.Blueprint.Mom.SingleSiteQuadratureStatement` | TRUE | easy | Apply the supplied polynomial law and its zero-atom mixture. |
| `AKLT.Blueprint.Mom.InteractionDegreeStatement` | TRUE | medium | Support degrees add with list multiplicities and two occurrences per loop. |

All eight leaves are true and self-sufficient as written. No corrected statements or additional premises are needed. Difficulty estimates concern Lean formalization. The two-line proof routes below are guidance; no proofs have been written.

Repository snapshot: `7a3393531c12080d76aefbdab300ac0c2df834b7`. Paper sources: [l:moments](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35), [l:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197), and [l:exact](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:297).

**Definitions and statement closure**

| Source | Definitions followed |
|---|---|
| [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9) | `Vec3`, `dot`, `normSq`; `goldenRatio`, `icoRadius`, `IcoLetter`, `signValue`, `icoVector`, `moment`; `Status`, `SpinLetter`, `spinVector`, `spinWeight`, `siteFunctional`; `DegreeFour`, `SeparateDegreeFour`. |
| [Defs/FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:52) | `localProduct`, `localMean`. |
| [Defs/Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:9) | `FrameData`, `MomentLaw`, `momentLawFunctional`; distinction from `IsFrame`. |
| [Mom/NodesCore.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesCore.lean:14) | `mono`. |
| [Mom/NodesFinite.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:36) | `dotPolynomial`. |
| [Mom/NodesMean.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:85) | Six assigned statements; `meanPath`, `meanPathEnd`; surrounding `tripleP`/`tripleV` formulas and proved `meanPathUnit`. |
| [Mom/NodesExact.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesExact.lean:22) | Two assigned statements; `pinPolynomial`, `interactionPolynomial`, `interactionOccurrences`. |

`normSq v` is `∑ i, v i * v i`. `localProduct a n` is `∏ j, (1+dot n (a j))`. `localMean` divides each coordinate numerator by the scalar normalizer. The atom definitions use the twelve labels `Fin 3 × Fin 2 × Fin 2`, the positive radius `sqrt(goldenRatio+2)`, and the three signed coordinate patterns stated in the paper. `SpinLetter = Option IcoLetter` adds a zero label. At U, its weight is zero and each geometric label has weight `1/12`; at D, these weights are `2/5` and `1/20`. Consequently, for every function `f`,

\[
L_U(f)=\mathcal M(f),\qquad L_D(f)=\tfrac35L_U(f)+\tfrac25f(0).
\]

`MomentLaw` supplies unit atoms, positive weights, mass one, and equality with `moment` for every real polynomial of total degree at most four. It does not require injectivity. `mono m v = ∏ i, v i ^ m i`. `SeparateDegreeFour` bounds the three-coordinate exponent sum at every site of every supported monomial. The interaction factors are the literal list products `1+C(q)*dotPolynomial(e)` and `1+C(q)*∑ i,C(a_i)*X(x,i)`.

[Inspect.lean](/home/ubuntu/aklt/reports/TS_MOM_04/Inspect.lean) successfully imported `NodesExact` and printed all eight elaborated definitions; see [lean_inspection.log](/home/ubuntu/aklt/reports/TS_MOM_04/lean_inspection.log). All are closed propositions, with no external parameters, instance arguments, or hidden hypotheses. Fixed `Fin` instances supply finite sums and decidable index equalities. Mathlib polynomial support, evaluation, and total-degree semantics were checked, including `support_mul` containment.

**DepletedContractionStatement — TRUE, easy**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:85); paper l:35, lines 260–266.

Put `W=localProduct a`, `A=L_U(W)>0`, and `B_i=L_U(n_i W)`. For every `k`, including zero, `W(0)=1`. The definitions give `A_D=(3A+2)/5>0`, `B_D=3B/5`, and contraction by `q=3A/(3A+2)∈(0,1)`. No bound on the fields or on `k` is missing; even signed products are covered when their U normalizer is positive.

Lean traps: retain the `Option.none` term, justify denominator cancellation, and scale `normSq` by `q²`.

Route 1: Expand the U/D finite sums and evaluate the product and coordinate numerators at zero.  
Route 2: Factor out `q`, bound it between zero and one, and use quadratic scaling and nonnegativity of `normSq`.

**MeanPathContinuityStatement — TRUE, medium**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:109); paper l:35, lines 269–275.

For `c=cos t`, the explicit normalizer is

\[
A(t)=\frac23(c^2+c+1)=\frac12+\frac23(c+\tfrac12)^2\ge\frac12.
\]

The numerator coordinates are finite sums of continuous trigonometric products. The squared norm is therefore continuous on all of `ℝ`, a stronger statement. The specified interval is nonempty because `meanPathEnd=2π/3>0`.

Lean traps: total real division does not supply quotient continuity at zero; establish denominator nonvanishing. The fixed path supplies it without any extra premise.

Route 1: Evaluate the degree-three normalizer and use `sin² t+cos² t=1` to obtain the displayed positive expression.  
Route 2: Apply continuity of finite sums/products, division by the nonzero normalizer, and the coordinate-square sum, then restrict to `Icc`.

**MeanPathEndpointsStatement — TRUE, medium**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:114); paper l:35, lines 276–279.

The actual path mean is

\[
\operatorname{localMean}_U(\operatorname{meanPath}(t))=
\left(\frac{(c+2)(2c+1)}{5(c^2+c+1)},0,0\right),\quad c=\cos t.
\]

At zero it is `(3/5,0,0)`, with normalizer `2`. At `2π/3`, `c=-1/2` and the mean is zero, with normalizer `1/2`. Both endpoint equalities have the intended meaning.

Lean traps: the conclusion gives squared norms, so the first value is `9/25`. All fractions and trigonometric arguments are real; `Fin 3` coordinates start at zero. Use exact trigonometric values.

Route 1: Expand the second/fourth moments to the displayed rational path mean, or evaluate the two triples in the generic mean formula.  
Route 2: Substitute `cos 0=1` and `cos(2π/3)=-1/2`, verify nonzero denominators, and sum the coordinate squares.

**MeanCovarianceStatement — TRUE, medium**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:120); paper l:35, lines 280–288, and l:moments, lines 78–84.

For a triple `(a,b,c)`, the defined quadrature has normalizer `A=1+p/3` and vector numerator `B=V/15`, where

\[
p=a\cdot b+a\cdot c+b\cdot c,\qquad
V=5(a+b+c)+a(b\cdot c)+b(a\cdot c)+c(a\cdot b).
\]

`RᵀR=I` preserves these scalar products, so `A` is fixed and `B` transforms by `R`. Unit triples have `A≥1/2`, from `normSq(a+b+c)≥0`. All tensor facts follow from the fixed twelve-atom definition; they need no additional hypothesis. The covariance identity even holds for arbitrary triples with Lean's total division.

Lean traps: the observable raises the numerator degree to four. Arbitrary orthogonal matrices need not permute the twelve atoms; only the relevant polynomial moments are invariant. The column identity has the correct transpose orientation.

Route 1: Derive `A` and `B` from the explicit second/fourth moments and use `RᵀR=I` to preserve every field scalar product.  
Route 2: Obtain `A(Ra)=A(a)` and `B(Ra)=RB(a)`, then commute common scalar division with `Matrix.mulVec`.

**OrthogonalNormStatement — TRUE, easy**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:127); paper l:moments, lines 78–84, and l:35, lines 280–284.

This is the coordinate identity `dot(Rv,Rv)=vᵀ(RᵀR)v=dot(v,v)`. The stated column identity suffices, including at `v=0`.

Lean trap: `Vec3` is an ordinary function type whose default Pi norm is the supremum norm. The explicit `normSq` is Euclidean. Use the finite sums or transfer to `EuclideanSpace` when using inner-product library results.

Route 1: Expand `normSq` and `Matrix.mulVec` and interchange the finite sums.  
Route 2: Replace each column contraction by its entry of `RᵀR=I` and simplify the identity matrix.

**OrthogonalTransportStatement — TRUE, medium**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:133); paper l:35, lines 283–285.

Use identity if `v=w`. Otherwise, with `u=v-w` and `d=normSq u>0`, the Householder matrix `I-2uuᵀ/d` has the required properties; equal squared lengths give `2 dot(u,v)=d`. Equal zero squared lengths force both vectors to be zero. A reflection is allowed because there is no determinant-one requirement.

Lean traps: split equality before dividing by `d`; establish definiteness of the real sum of squares. The Pi-norm issue also applies here.

Route 1: Choose identity for `v=w`; otherwise choose the displayed Householder matrix along `v-w`.  
Route 2: Use equal squared lengths and `d>0` to check column contractions and the action on `v` by finite-sum algebra.

**SingleSiteQuadratureStatement — TRUE, easy**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesExact.lean:22); paper l:exact, lines 317–325.

The polynomial `∏ i, X i ^ m i` evaluates to `mono m` and has total degree at most `∑ i, m i`. `MomentLaw` therefore supplies its equality. Both D functionals use the same `3/5` and `2/5` mixture. Repeated atoms are summed with their weights. `k=0` contradicts mass one, but nonempty laws exist: reindex the twelve explicit unit atoms by `Fin 12` with uniform weights. The entire leaf is not vacuous.

Lean traps: `mono 0 0=1` because `0^0=1`; only positive-degree monomials vanish at zero. The supplied active-status disjunction matters: `momentLawFunctional` treats X like U, whereas `siteFunctional X` is zero. Do not introduce deduplication or `IsFrame` injectivity.

Route 1: Apply the polynomial-equality component of `MomentLaw` to `∏ i, X i ^ m i`, using its total-degree bound.  
Route 2: Split U/D and unfold the matching zero-atom mixtures, retaining the constant monomial's value at zero.

**InteractionDegreeStatement — TRUE, medium**

[Lean statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesExact.lean:68); paper l:exact, lines 327–331.

A supported product exponent is a sum of exponents from the inserted polynomial and the interaction factors. A bond contributes at most one per endpoint at the site; a pin contributes at most one. Thus the resulting site degree is bounded by the inserted degree plus `interactionOccurrences`, as hypothesized. Loops count twice and lists retain repetitions. Arbitrary coefficients, signs, and pin lengths do not increase these degrees.

Lean traps: product support is contained in the sum of supports; cancellations prevent asserting equality. Keep list multiplicities. For `p=0`, the premise gives no occurrence bound, but the product is zero. For `n=0`, there are no site-degree tests, as intended. These valid degenerate subcases do not make the general theorem vacuous. No natural-number subtraction or distinct-endpoint premise is hidden.

Route 1: Bound each factor's supported site degree by its endpoint/pin count and add bounds by induction over the lists.  
Route 2: Use `MvPolynomial.support_mul` containment to select an inserted support exponent and apply its bound; handle `p=0` separately.

**Validation and limits**

[audit_checks.py](/home/ubuntu/aklt/reports/TS_MOM_04/audit_checks.py) uses exact SymPy arithmetic to check all twelve unit atoms, all 35 monomials through total degree four, the generic triple normalizer/numerator formulas, and the path formula/endpoints. It also checks repeated-atom quadrature, covariance under an orthogonal matrix that does not preserve the atom set, depleted contraction for `k=0,1,7` with fields outside the ball, five transport examples, and six interaction examples covering zero sites, loops, repetitions, cancellation, inserted observables, and `p=0` with excess occurrences. Results: [audit_checks.json](/home/ubuntu/aklt/reports/TS_MOM_04/audit_checks.json). Reproduce with `PYTHONPATH=/tmp/ts_mom_04_python python3 audit_checks.py`; SymPy 1.14.0 was installed only in that temporary directory.

The checks corroborate the definition-level and paper-argument review; they are not Lean proofs of the leaves. One Lean inspection process used existing compiled imports and a local package symlink. No sub-agents were launched, no proofs were written, and the repository was not modified. Real coefficients and fractions are correctly typed. Any need for `classical` during finite-support manipulation is a proof convenience, not an additional mathematical premise.
