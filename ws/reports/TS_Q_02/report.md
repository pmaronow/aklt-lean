STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty | Finding |
| --- | --- | --- | --- | --- |
| `AKLT.Blueprint.Q.QuarticKernelDegreeStatement` | `l:tight` | TRUE | easy | Both branches have total degree at most four. |
| `AKLT.Blueprint.Q.QuarticKernelEvaluationStatement` | `l:tight` | TRUE | medium | Density entries give the correct conjugation, sign, and factor `1/16`. |
| `AKLT.Blueprint.Q.ComplexQuadratureStatement` | `d:frame` | TRUE | medium | Real polynomial quadrature extends by complex linearity. |
| `AKLT.Blueprint.Q.QuarticOffDiagonalStatement` | `l:tight` | TRUE | medium | All twenty off-diagonal finite averages vanish. |
| `AKLT.Blueprint.Q.QuarticDiagonalStatement` | `l:tight` | TRUE | medium | Diagonal moments are `1/5, 1/20, 1/30, 1/20, 1/5`. |
| `AKLT.Blueprint.Q.ResolutionExpansionStatement` | `l:tight` | TRUE | medium | The supplied Gram identity gives the inverse-binomial monomial norm. |
| `AKLT.Blueprint.Q.TensorResolutionStatement` | `l:tight` | TRUE | hard | Dependent finite sums factor, and orthonormal-coordinate binomial factors cancel. |
| `AKLT.Blueprint.Q.StarPositiveStatement` | `l:star` | TRUE | easy | Every Hamiltonian summand is an orthogonal projection. |

All eight statements are true and self-sufficient as written. No corrected statement or additional mathematical premise is needed. No leaf is vacuous. The review used repository commit `7a3393531c12080d76aefbdab300ac0c2df834b7` on `main`, the exact Lean declarations, and the local manuscript. No proofs were written and the repository was not modified.

The seven tight-frame declarations are in [NodesTight.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesTight.lean:17); positivity is in [NodesStar.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesStar.lean:11). The paper sources are [the frame definition](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:264), [the tight-frame lemma](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:274), [the star lemma](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:223), and [the finite moment lemma](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35).

The custom definition chains were read through their concrete formulas:

- Kernels and quadrature: `compatible`, `quarticMonomial`, `quarticKernel`, `complexMoment`, `quadrature`, and `resolution` in [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:12); `Vec3`, `goldenRatio`, `icoRadius`, `IcoLetter`, `signValue`, `icoVector`, `moment`, and `DegreeFour` in [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8); `Spinor`, `pauli`, and `spinDensity` in [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:49).
- Resolution norms: `BinaryForm`, `binaryEval`, `binaryNormSq`, and `physicalEval` in [Polynomial.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Polynomial.lean:9); `Size`, `size_neZero`, `Site`, `Configuration`, and `Hilbert` in [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:17). The product binder in `physicalEval` includes the square-root binomial factor and both spinor powers.
- Star positivity: `StarHilbert`, `starAtSite`, `starCasimir`, and `starHamiltonian` in [Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:22), with `spinZ`, `spinPlus`, and `spinMinus` in [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:49).

Relevant Mathlib meanings were checked in the pinned package. `MvPolynomial.eval` is finite coefficient-weighted monomial evaluation. `totalDegree` is the maximum exponent sum over the polynomial support, with zero polynomial degree zero. `Complex.normSq` is squared modulus. `EuclideanSpace` is `PiLp 2`, with squared norm the sum of squared coordinate moduli. The eigenspace is the kernel of `T - μ • 1`. `starProjection` projects orthogonally onto a submodule and includes it in the ambient space. `LinearMap.IsSymmetric` means `⟪T x,y⟫ = ⟪x,T y⟫`; over `ℂ` this is the Hermitian condition.

**QuarticKernelDegreeStatement.** Each variable-dependent base has degree at most one. In the `j ≤ k` branch the exponent sum is `(4-k.val)+j.val+(k.val-j.val)=4`; the reverse branch exchanges the indices. Both indices are at most four.

Route, line 1: Split `j ≤ k` and bound degrees of products and powers by the sum of their exponent bounds.  
Route, line 2: Use the `Fin 5` bounds and branch inequality to simplify the natural subtractions to a total of four.

Lean traps: Transfer `Fin` comparisons to natural-number values when needed. Establish the branch inequality before simplifying `k.val-j.val`. A constant polynomial has degree zero. Difficulty: **easy**.

**QuarticKernelEvaluationStatement.** The density equality in `compatible` gives `|z₀|²=(1+v₂)/2`, `|z₁|²=(1-v₂)/2`, and `star(z₀)*z₁=(v₀+i v₁)/2`. The opposite cross entry is its conjugate. These match both kernel branches and their denominator `16`. Pole spinors cause no exception. The normalization conjunct of `compatible` is stronger than this algebra needs: its density equality already supplies the required identities.

Route, line 1: Extract the four matrix entries of the density equality and simplify the Pauli matrices.  
Route, line 2: Split the index comparison, regroup conjugated powers into the paired factors, and simplify four factors of `1/2` to `1/16`.

Lean traps: The plus sign comes from entry `(1,0)` of the outer product `z k * star(z l)`; entry `(0,1)` has the minus sign. Move `star` through products and powers, and manage real-to-complex casts. No square-root division or spinor-choice construction is needed. Difficulty: **medium**.

**ComplexQuadratureStatement.** `quadrature` supplies the entire real degree-four polynomial identity. Since all coordinates and weights are real, complex linear extension gives the conclusion. Positivity, distinctness, and sphere membership are unnecessary. The `Fintype A` parameter is retained in the elaborated declaration.

Route, line 1: Apply `quadrature` to each real monomial with coefficient one in `p.support`, then cast each equality into `ℂ`.  
Route, line 2: Multiply by its complex coefficient and sum over the finite support, commuting sums to obtain `complexMoment p`.

Lean traps: `Complex.re` and `Complex.im` are real linear maps, not ring homomorphisms, so they cannot simply be supplied to `MvPolynomial.map`. The monomial route avoids this issue. For coefficientwise real/imaginary polynomials, prove support inclusion to retain the degree bound. The constants `1/12` are field divisions on both sides, with compatible casts. Difficulty: **medium**.

**QuarticOffDiagonalStatement.** `complexMoment` is explicitly the average over twelve labels `Fin 3 × Fin 2 × Fin 2`, with independent signs. Direct summation gives zero if any coordinate exponent is odd, second moments `1/3`, fourth moments `1/5`, and mixed even fourth moments `1/15`. Substitution into all twenty off-diagonal kernels gives zero. This agrees with the paper's degree-four rotation argument.

Route, line 1: Derive the required monomial moments from the labels using `φ²=φ+1`, `r²=φ+2`, and `r⁴=5φ²`.  
Route, line 2: Expand the finite off-diagonal cases and cancel their averages; alternatively derive degree-four covariance and apply the paper's phase-changing rotation.

Lean traps: The icosahedral average is not invariant under arbitrary rotations on arbitrary functions; stay within degree four. This is a `Fintype` sum over twelve labels, with no separate `Finset` cardinality assumption. The concrete radius is strictly positive. An external `Top.MomentsStatement` premise is unnecessary because the finite identities are derivable from these definitions. Difficulty: **medium**.

**QuarticDiagonalStatement.** With `t=v₂`, the diagonal kernel is `(1+t)^(4-j)*(1-t)^j/16`. Direct averages give `M(1)=1`, `M(t)=M(t³)=0`, `M(t²)=1/3`, and `M(t⁴)=1/5`. The five kernel averages are `1/5, 1/20, 1/30, 1/20, 1/5`. Multiplying by five gives the inverses of `1,4,6,4,1`.

Route, line 1: Compute the five third-coordinate moments from `icoVector` and the golden-ratio/radius identities.  
Route, line 2: Split `j : Fin 5` into five cases, expand the diagonal polynomial, and compare with the binomial inverses.

Lean traps: The inverse is taken in `ℂ` after casting a binomial computed in `ℕ`; all five values are nonzero. Square-root identities require nonnegative radicands, supplied by `5>0` and `φ+2>0`. Keep both normalizations, `1/12` and `1/16`. Difficulty: **medium**.

**ResolutionExpansionStatement.** `BinaryForm 4` contains ordinary monomial coefficients. `binaryEval` uses the same monomials as `resolution`, and `binaryNormSq` divides coefficient squared moduli by `choose(4,j)`. Expanding the supplied Gram identity therefore gives exactly the conclusion. Signed weights and non-unit spinors are allowed; no frame or compatibility premise is missing.

Route, line 1: Cast the real identity into `ℂ`, expand `normSq(binaryEval)` as a conjugate product, and interchange finite sums.  
Route, line 2: Apply `resolution`, collapse the diagonal coefficient pairs, and identify the remaining sum with `binaryNormSq 4 p`.

Lean traps: Manage casts between the real conclusion and complex Gram premise. Use `(Complex.normSq u : ℂ)=star(u)*u`, reordering multiplication if necessary. The norm divides by `choose(4,j)` directly. Every binomial denominator is positive; positivity of the weights is not needed. Difficulty: **medium**.

**TensorResolutionStatement.** The local factors in `physicalEval` are `sqrt(choose(4,j))*quarticMonomial j`, while `Hilbert` has the Euclidean norm of its orthonormal coordinates. The sum over `(x : Site L N) → S x` factors into local Gram sums. Distinct configurations vanish at a differing site. On equal configurations, `sqrt(choose)^2/choose=1` at every site, leaving the sum of squared coordinate moduli.

Route, line 1: Expand the conjugate product of `physicalEval`, commute the finite sums, and factor the dependent alphabet sum into local Gram factors.  
Route, line 2: Apply the local resolutions, cancel positive binomial factors on the diagonal, and use `EuclideanSpace.norm_sq_eq`.

Lean traps: The binder `∀ (_ : ∀ x, Fintype (S x)), ...` is retained. The compiled declaration applies each `resolution` with its corresponding component; no equal-cardinality premise is hidden or lost. Bind the family and install its components locally if necessary during finite-sum manipulations; use `classical` for dependent-function and finite-support decidability. This adds no mathematical premise. Preserve the dependent product. Conjugation fixes each real square root, and `Nat.choose 4 j.val>0` justifies cancellation. `Size` already imposes `L,N≥3`, giving finite nonempty site types. Difficulty: **hard**.

**StarPositiveStatement.** `starHamiltonian` is the sum of four orthogonal projections onto concrete eigenspaces in `EuclideanSpace ℂ (Fin 5 → Fin 5)`. Each is Hermitian and has nonnegative real quadratic form. These facts require neither a nonzero eigenspace nor a separate symmetry proof for `starCasimir`; they are the paper's intended positivity mechanism.

Route, line 1: Unfold `starHamiltonian`, apply `Submodule.starProjection_isSymmetric` to each summand, and preserve symmetry under the finite sum.  
Route, line 2: Sum the four projection quadratic-form identities `Re⟪ψ,Pψ⟫=‖Pψ‖²≥0`.

Lean traps: `starProjection` is a continuous linear map and the definition takes its `toLinearMap`. Mathlib's `re_inner_starProjection_nonneg` puts the projection in the first inner-product slot; use conjugate symmetry or `inner_starProjection_left_eq_right` for the statement's order. Finite dimension supplies projection instances. The space has dimension `5^5=3125`, so this is not an empty-domain assertion. Difficulty: **easy**.

The degenerate cases also behave correctly. An empty quadrature alphabet contradicts its constant-one identity (`0=1`); an empty resolution alphabet contradicts its `j=k=0` identity. An empty tensor alphabet therefore violates its local resolution premise. These excluded special inputs do not make a leaf vacuous: the twelve icosahedral atoms with uniform weights provide quadrature and, with compatible spinors, resolution examples. Both spinor poles, quartic endpoint exponents, natural subtractions, denominators, and quantifier/instance retention were checked. No listed leaf fails any of these checks.

[inspect.lean](/home/ubuntu/aklt/reports/TS_Q_02/inspect.lean) imports the two assigned modules and prints all eight elaborated declarations plus the evaluation and star definitions. It contains only inspection commands. It completed with Lean `v4.35.0-rc2`, exit code zero; output is [inspect.out](/home/ubuntu/aklt/reports/TS_Q_02/inspect.out). Existing compiled dependencies were read directly; [.lake/packages](/home/ubuntu/aklt/reports/TS_Q_02/.lake/packages) links to the repository's packages. Only one Lean process ran at a time, and no repository module was built.

[checks.py](/home/ubuntu/aklt/reports/TS_Q_02/checks.py) checked all 35 monomial moments of degree at most four, all 25 kernel degree bounds, all 25 kernel moments, and all 25 evaluation identities on eight compatible rational spinors, using exact rational/quadratic-field arithmetic. All passed. Supplementary floating-point checks covered Gram and norm identities for alphabets of sizes 12, 24, and 13, with negative weights, repeated atoms, non-unit spinors, and an extra zero spinor; a direct two-site tensor sum with unequal alphabet sizes; and a factorized nine-site sparse entangled state, matching the minimum allowed site count. The largest absolute discrepancy was below `7e-15`. The two-site calculation exercises the generic finite tensor algebra, not a permitted `Size` instance. These checks support the audit and do not replace its mathematical routes. Recorded output is [checks.out](/home/ubuntu/aklt/reports/TS_Q_02/checks.out).

[verdicts.jsonl](/home/ubuntu/aklt/reports/TS_Q_02/verdicts.jsonl) contains one machine-readable verdict per leaf, with reason, fix, two-line route, and difficulty.
