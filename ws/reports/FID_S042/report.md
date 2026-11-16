STATUS: PASS
BLOCKING: 0

DECL: spinWeight PASS

Matches Definition `d:moment`, `paper/sec2-moments.tex:8–19`: the U law assigns mass 1/12 to each of twelve vertices; the D law is (3/5) times that law plus (2/5) times the zero atom. At `lean/AKLT/Defs/Moment.lean:67–69`, the `some` weights are therefore exactly 1/12 and 1/20, and the `none` weights are respectively 0 and 2/5. The return type forces all divisions and numerals here to be in ℝ, so there is no natural-number division or rounding; all denominators are nonzero. The total masses are 12/12 = 1 and 12/20 + 2/5 = 1.

Checked the supporting labels and their interpretation (`Moment.lean:9–47,58–63`): `Fin 3 × Fin 2 × Fin 2` has twelve elements, the two signs are independent, and the three coordinate patterns agree with the paper in the same cyclic order. `Fin 3` uses coordinates 0,1,2, a consistent relabeling of the paper's 1,2,3. The common radius is positive: φ = (1 + √5)/2 > 0 and r = √(φ + 2) > 0. Mathlib's square root is the nonnegative real root (`Mathlib/Analysis/Real/Sqrt.lean:144–150,178,286–287`), so vector normalization never divides by zero. Each raw vector has squared norm 1 + φ² = φ + 2; its zero-coordinate location and two signs distinguish it from the other labels. Thus labeled summation neither repeats nor loses paper atoms. Mathlib's product and option `Fintype` instances enumerate all pairs and add precisely one `none` (`Mathlib/Data/Fintype/Prod.lean:42–43`; `Mathlib/Data/Fintype/Option.lean:29–41`).

The X branch is an auxiliary zero extension, not a third probability law. Definition `d:domain` removes X sites (`paper/sec6-walks.tex:8–26`). The inspected partition functions sum only over active sites, and the generic finite-network interfaces require U/D statuses; see the non-blocking remark below.

DECL: siteFunctional PASS

Matches the finite functionals of `d:moment`, `paper/sec2-moments.tex:14–19`, and their single-site use in `l:moments`, `paper/sec2-moments.tex:46–52,86–94`. Mathlib's `∑ j : SpinLetter` is a `Finset.univ` sum, not an integral or an infinite sum (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:59–69`). The option enumeration contains one zero label and the twelve geometric labels. Consequently, for every real-valued function f,

`siteFunctional U f = (1/12) ∑ j : IcoLetter, f (icoVector j)`,

`siteFunctional D f = (3/5) * moment f + (2/5) * f 0`.

The extra zero label at a U site contributes zero, including for constant functions. At a D site the constant moment remains one, whereas every positive-degree monomial vanishes at zero and acquires exactly the paper's factor 3/5. The function domain `Vec3 → ℝ` permits arbitrary functions, which is legitimate for this finite sum; polynomial degree restrictions belong to the identities using it. There are no omitted measurability, convergence, or normalization hypotheses, and no division by a possibly zero normalizer in this definition. Vector-valued uses take the functional coordinate by coordinate, as prescribed at `paper/sec2-moments.tex:31–33`.

DECL: DegreeFour PASS

Encodes precisely “polynomial of total degree at most four” in `l:moments`, `paper/sec2-moments.tex:46–47`, and the frame condition `d:frame`, `paper/sec3-quantum-frames.tex:264–268`. The callers `lean/AKLT/Defs/Frame.lean:14–25` use it on real polynomials in the three spin coordinates and evaluate them by ordinary substitution.

Checked Mathlib's actual definition: `MvPolynomial σ R` represents finite formal sums of monomials with natural exponents (`Mathlib/Algebra/MvPolynomial/Basic.lean:55–61,80–83`), and `totalDegree` is the maximum, over monomials with nonzero coefficient, of the sum of their exponents (`Mathlib/Algebra/MvPolynomial/Degrees.lean:431–443`). It is not the maximum individual-coordinate degree. The bound and the numeral 4 are in ℕ. Constants and the zero polynomial have total degree zero (`Degrees.lean:455–465`), so both are admitted, as intended by an upper degree bound. `MvPolynomial.eval` is evaluation with the identity coefficient map and the supplied coordinate values (`Mathlib/Algebra/MvPolynomial/Eval.lean:255–275`); there is no quotient by sphere identities or restriction to the twelve sample points.

DECL: SeparateDegreeFour PASS

Matches the separate, sitewise total degree condition in `l:moments`, `paper/sec2-moments.tex:51–52,90–94`, and its explicit monomial formulation in the proof of `l:exact`, `paper/sec2-moments.tex:311–320`: for every monomial and each site x, the sum of the three coordinate exponents at x is at most four.

Mathlib's `p.support` consists exactly of exponent functions of monomials having nonzero coefficients (`Mathlib/Algebra/MvPolynomial/Basic.lean:459–474`); an exponent function has type `(ι × Fin 3) →₀ ℕ`. The coercion `m (x,k)` retrieves its natural exponent, returning zero off its finite support (`Mathlib/Data/Finsupp/Defs.lean:158–166`). Thus the bound in `Moment.lean:79–80` sums exponents, including multiplicity, over all three coordinates of one site. It neither imposes total degree four across different sites nor allows degree four independently in each scalar coordinate. The quantifiers inspect every supported monomial and every site. Absent sites, constants, and the zero polynomial satisfy the bound for the intended reasons.

The predicate constrains the whole polynomial supplied to it. This agrees with the requirement to include inserted observables (`paper/sec2-moments.tex:3–6,304–307,327–331`); it introduces no separate exemption for an observable. Although its auxiliary type parameter permits infinite ι, every polynomial still has finite support, and its product-functional callers use finite site types (`lean/AKLT/Blueprint/Top/Common.lean:24–28,62–73`). No additional finiteness or nonemptiness hypothesis is needed for the degree predicate itself.

DECL: productFunctional PASS

Matches the finite product of site laws in `d:moment`, `paper/sec2-moments.tex:16–23`, and the sitewise factorization used in `l:moments` and `l:exact` (`paper/sec2-moments.tex:90–94,311–325`). `[Fintype ι]` supplies precisely a finite site set without assuming it is nonempty. Mathlib's function-space instance enumerates all assignments `ι → SpinLetter`, with independent choices at every site (`Mathlib/Data/Fintype/Pi.lean:28–45,133–143`). The summand multiplies exactly one site mass per site and evaluates f on the corresponding spin vectors. It therefore has the required product weights, with no missing power of 12 or extra normalization. At U sites, assignments using `none` have zero mass, so the common thirteen-label space gives exactly the paper's twelve-point support there; D sites have all thirteen atoms.

The inner product and outer sum are finite `Finset.univ` operations. Mathlib's `Fintype.prod_sum` expresses their expected factorization on products of single-site functions (`Mathlib/Algebra/BigOperators/Ring/Finset.lean:300–302`). Different `Fintype` instances cannot omit or repeat configurations: their enumerations contain every element without duplicates (`Mathlib/Data/Fintype/Defs.lean:55–61,90–97,262–263`). The local `classical` supplies decidable equality for enumeration, without adding a mathematical hypothesis.

For empty ι there is exactly one function `ι → SpinLetter`; the product of masses is 1 (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:753–754`). The result is f at the unique empty spin configuration, and is 1 for the constant-one observable, exactly as specified by `paper/sec2-moments.tex:22–23,320`. The definition contains no subtraction or division, and imposes no unnecessary regularity or degree condition on f. Its U/D product identities explicitly restrict statuses to those two active laws (`lean/AKLT/Blueprint/Top/Common.lean:24–28,62–73`).

Non-blocking remarks:

- `siteFunctional X` is identically zero, and a product containing an X site would also be zero. This would not implement deletion if X were retained in the index set. Current intended uses avoid that case: `Network.active` and `PatternData.active` exclude X (`lean/AKLT/Defs/Domain.lean:14–16,63–70`; `lean/AKLT/Defs/Pattern.lean:66–87`), passage deletion uses a subset of active sites (`lean/AKLT/Defs/OperatorContracts.lean:13–21`), `FiniteSpinNetwork.Valid` requires U/D (`lean/AKLT/Defs/FiniteNetwork.lean:17–20`), and the single-site leaf statement explicitly excludes X (`lean/AKLT/Blueprint/Top/Operator.lean:37–44`). The extension therefore creates no vacuous or unintended reading of the reviewed objects in their paper-facing uses.
- Read all of `Moment.lean` and its project import `Geometry.lean`, checked the relevant consumers, and inspected the Mathlib definitions cited above. Exact rational arithmetic in ℚ(√5) independently confirmed twelve distinct antipodal atoms, their common raw squared norm φ + 2, and all 35 monomials of total degree at most four; rational checks confirmed the U/D masses and the empty and two-site product masses. No Lean process was run. Inputs were not modified.
