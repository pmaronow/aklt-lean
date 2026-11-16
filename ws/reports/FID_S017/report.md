STATUS: PASS
BLOCKING: 0

DECL: conditionOn PASS

This is an auxiliary finite-weight implementation of conditioning. The matching paper uses are conditioning off a block in `sec3-quantum-frames.tex:508` and consistency under conditioning in Lemma `l:planeenergy`, `sec3-quantum-frames.tex:691–719`. The latter proof explicitly cancels constant factors against the conditional normalizer (`:709–716`). Unfolding `normalize` (`lean/AKLT/Defs/Probability.lean:12–13`) gives

`conditionOn p E σ = (if E σ then p σ else 0) / (∑ τ, if E τ then p τ else 0)`.

Thus it retains exactly the event, divides by its actual mass, and assigns zero outside it. Keeping the original state space is appropriate: `conditionalPlaneLaw` and `conditionalTorusLaw` subsequently push this weight forward to block configurations (`lean/AKLT/Defs/Specification.lean:14–24`). Their interface claims are under proper colourings and positive frame laws (`lean/AKLT/Blueprint/Top/Quantum.lean:82–101`). A conditioning fibre contains the specified configuration, so its mass is positive. This agrees with the paper's full-support assertion and positive normalizers (`sec3-quantum-frames.tex:508–524`).

Mathlib meaning checked: a type-indexed sum ranges over `Finset.univ`, containing each element once (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:63–69`; `Mathlib/Data/Fintype/Defs.lean:53–61,90–97`). `Weight Ω` is an ordinary real-valued function, with no implicit probability hypothesis. Real division is total: division by zero returns zero (`Mathlib/Algebra/GroupWithZero/Basic.lean:398–402`). Consequently a zero-mass event produces the zero weight, not a probability. No reviewed use claims it is a conditional probability on such an event; this total extension does not change the intended object on its probabilistic domain. The `[Fintype Ω]` assumption imposes precisely finite summation, without an extra nonemptiness assumption.

DECL: eventMass PASS

This auxiliary is exactly the finite event mass `∑_{σ∈E} p(σ)`. Its paper counterpart is the positive-probability conditioning requirement in Lemma `l:finitefacts`, `sec2-moments.tex:126–137`, expanded as a positive marginal probability in `:159–174`. The Lean use sets `p = normalize (D.weight pinned)` and explicitly assumes `0 < eventMass p E` before asserting conditional independence (`lean/AKLT/Blueprint/Top/Common.lean:40–49`). Thus the event mass tests the correct conditioning event and excludes null fibres.

Mathlib meaning checked: the finite universe sum and the real-valued `if` give each atom its weight exactly once when `E` holds, and zero otherwise. There is no cardinality normalization, absolute value, extended-real conversion, or hidden measure-theory convention. An empty event has mass zero; the whole event has mass `∑ σ, p σ`. The definition also accepts unnormalized or signed weights, as its auxiliary `Weight` type permits, but its probability interpretation at this use is under the normalized nonnegative network law. No paper hypothesis is lost by this algebraic generality.

DECL: localProduct PASS

This is precisely `W(n) = ∏_{j=1}^k (1+n·a_j)` from Lemma `l:35`, `sec2-moments.tex:197–208`, also denoted `W` in its proof (`:250–261`). `dot` is explicitly `∑ i : Fin 3, n i * a j i` (`lean/AKLT/Defs/Moment.lean:8–15`), hence the Euclidean scalar product, with the same positive sign. No ambient function-space norm is substituted for Euclidean geometry. `Fin k` indexes exactly `k` fields; replacing the paper's one-based enumeration by zero-based indices changes no factor.

Mathlib meaning checked: `∏ j` is the product over every member of `Fin k`, and the product for `Fin 0` is one (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:59–69`; `Mathlib/Algebra/BigOperators/Fin.lean:55–62`). This includes the paper's `k=0` case. The polynomial definition sensibly accepts arbitrary fields and any natural `k`; the matching mean statement supplies `k ≤ 3` and `normSq (a j) ≤ 1` explicitly (`lean/AKLT/Blueprint/Top/Common.lean:52–56`). There is no natural-number subtraction, missing factor, or added unit-vector restriction.

DECL: localMean PASS

This is the mean of the normalized law proportional to `localProduct a n · λ_s(dn)` in `sec2-moments.tex:197–208`. The paper explicitly applies a vector functional coordinatewise (`:31–33`), exactly as the Lean function `fun i => ...` does. Its numerator is the finite integral of `n_i W(n)`, and its common denominator is the integral of `W(n)`.

Checked the imported atomic laws (`lean/AKLT/Defs/Moment.lean:23–73`): the twelve independently signed icosahedral labels have exactly the vectors and radius in Definition `d:moment`, `sec2-moments.tex:8–19`. At U, each has weight `1/12` and the additional zero label has weight zero. At D, each has weight `1/20 = (3/5)(1/12)`, and the zero atom has weight `2/5`. Thus `siteFunctional .U` is precisely the paper's `M`, and `siteFunctional .D` is precisely its mixture law; the extra U label changes no sum. All displayed fractions are real divisions, not natural-number divisions.

Mathlib meaning checked: each coordinate is an ordinary real quotient of finite sums. Its denominator is strictly positive throughout the claimed domain: the paper proves positivity for at most three fields in the unit ball (`sec2-moments.tex:241–258`) and gives the D normalizer `(3/5)A+2/5` (`:260–265`). The Lean interface has exactly these field conditions and explicitly restricts `s` to U or D (`lean/AKLT/Blueprint/Top/Common.lean:53–55`). Its second clause uses three unit fields and status U, exactly matching the displayed attainable-mean set. `normSq` is the sum of coordinate squares, so its squared-radius formulation has the same meaning as the Euclidean ball. For `k=0`, the denominator is one and the mean is zero. The totalized value for status X or a zero denominator outside this domain does not enter the paper claim.

DECL: evaluateReduced PASS

This is an auxiliary evaluation map for the rational polynomials used to encode the paper's real reduced partition polynomials. Definition `d:reduction`, `app-local-operator.tex:146–168`, explicitly defines their values for every remaining vector in `ℝ³`, without a realizability restriction. The evaluation also supplies the polynomial value in the Pauli construction and trace identity (`app-local-operator.tex:246–279`). Returning a real scalar is correct; the operator interface then explicitly coerces it to `ℂ` when comparing it to a complex trace (`lean/AKLT/Blueprint/Top/Operator.lean:63–71`).

Mathlib meaning checked: `MvPolynomial.eval₂ f g` sums each coefficient mapped by `f` times the product of the assigned variables raised to their monomial exponents (`Mathlib/Algebra/MvPolynomial/Eval.lean:67–78`). It maps `C q` to `f q`, `X v` to `g v`, and preserves sums and products (`:88–112,138–163`). `Rat.castHom ℝ` is exactly the injective rational-to-real ring homomorphism, preserving rational division (`Mathlib/Data/Rat/Cast/CharZero.lean:24–25,51–64`). Hence the definition evaluates a monomial as `(q : ℝ) * ∏ (j,i), (u j i)^(m (j,i))`, with no rounding or coefficient alteration.

The variable valuation `fun v => u v.1 v.2` uses the first index for the vector token and the second for its coordinate, matching `formalDot`, `contractSpins`, and the reduced polynomial constructions in `lean/AKLT/Defs/Operator.lean`. The twenty indices preserve original slot identities; unused tokens have no occurrence in the constructed polynomial, and the general Pauli interface explicitly requires `SupportedVectors J p`. Constants therefore evaluate correctly even when no vector token remains, as required by `app-local-operator.tex:16–18,226–227`. Evaluation itself adds no unit-ball, affineness, or positivity hypothesis; the interfaces supply those where needed. No index reversal, sign change, or division by vector data occurs.

Non-blocking remarks:

- Read the complete `FiniteNetwork.lean` and its local transitive import closure: `Probability`, `Operator`, `Pattern`, `Frame`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Checked the relevant interface uses and Mathlib definitions cited above. Only the five assigned declarations are judged.
- The total-function behavior at null conditioning events and inadmissible local-mean inputs is harmless in the inspected uses. Their probability interpretations require the positivity and U/D restrictions described above; these definitions alone do not assert such properties for arbitrary arguments.
- This was a source-level fidelity review. No Lean proof compilation was needed, and no input files were modified.
