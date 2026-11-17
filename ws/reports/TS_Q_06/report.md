STATUS: COMPLETE

| Leaf | Verdict | Reason | Difficulty |
|---|---|---|---|
| [`AKLT.Blueprint.Q.IncidentEvaluationStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:33) | **TRUE** | Evaluation and orientation signs agree; independent residual gives the fibre scalar. | medium |
| [`AKLT.Blueprint.Q.GroundFibreFactorizationStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:44) | **TRUE** | The given bond product splits correctly; nonincident factors ignore the centre. | medium |
| [`AKLT.Blueprint.Q.GroundTransformStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:56) | **TRUE** | The density gives the squared norm identity; both inverse cancellations are valid. | easy |
| [`AKLT.Blueprint.Q.FibreIntertwiningStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:69) | **TRUE** | The singleton conditional quotient equals the projection coefficient; the residual norms agree. | hard |
| [`AKLT.Blueprint.Q.FibreProjectionStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:87) | **TRUE** | The denominator is positive and the formula gives fibrewise weighted least squares. | hard |
| [`AKLT.Blueprint.Q.WeightedPolarizationStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:100) | **TRUE** | Real weights give a Hermitian form; complex polarization recovers the full inner product. | medium |
| [`AKLT.Blueprint.Q.GroundQuotientVarianceStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:109) | **TRUE** | The quotient mean is ⟨B,ψ⟩/‖B‖; its variance is the physical squared norm. | medium |
| [`AKLT.Blueprint.Q.BetaNonzeroStatement`](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesQuantum.lean:124) | **TRUE** | Each neighbour corresponds to a bond determinant, up to a harmless sign. | easy |

All eight leaves are true and self-sufficient as written. No missing premise, corrected statement, counterexample, or global vacuity was found. The `fix` field is empty for every leaf. Difficulty estimates include the Lean work needed for finite-product and fibre-sum reindexing.

Audited repository: `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The paper arguments are in [sec3-quantum-frames.tex](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:546), `l:quantumfibre` at lines 546–644 and `t:QD` at lines 646–690. The two `t:QD` leaves are polarization and quotient variance; the other six belong to `l:quantumfibre`. No other blueprint Statement was assumed as an axiom in this audit.

**Definitions examined.** The project definition closure used by these leaves is:

- [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:17): `Size`, its `NeZero` instance, `Site`, `Direction`, `Bond`, `nextSite`, `bondSites`, `Configuration`, `Hilbert`, `SpinorPolynomial`, `singlet`, `vbsPolynomial`, `monomialDegree`, and `B`.
- [Defs/Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:10): `torusNeighbours`; [Defs/Polynomial.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Polynomial.lean:33): `physicalEval`.
- [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:10) and [Defs/Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:38): `Vec3`, `dot`, `goldenRatio`, `icoRadius`, `IcoLetter`, `signValue`, `icoVector`, `Spinor`, `frameRotation`, `frameVector`, and `frameSpinor`. The eight assertions use these actual values through algebraic evaluations; they do not silently require an additional frame-moment theorem.
- [Defs/FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:57): `TorusConfiguration`, `torusWeight`, `torusLaw`, `torusReference`, and `frameEval`.
- [Defs/Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9): `Weight`, `normalize`, `complexMean`, `variance`, `AgreeOutside`, `conditionalExpectation`, and `blockDirichlet`. `blockDirichlet` directly sums the squared conditional residual; it does not introduce a second conditional-variance normalization.
- [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:22): `determinant`, `weightedNorm`, `weightedInner`, `statePolynomial`, `independentAt`, `incidentProduct`, `edgeSign`, `centreSign`, `beta`, `rho`, `inFibreSpan`, `fibreDenominator`, `fibreProjection`, `groundTransform`, and `groundQuotient`.
- Mathlib conventions checked in `Analysis/InnerProductSpace/PiL2.lean` and `Analysis/InnerProductSpace/Basic.lean`: EuclideanSpace has the sum inner product, conjugate-linear in its first argument; its self-inner product gives the cast of the squared norm. `Complex.normSq_eq_conj_mul_self` has the matching convention.

**Shared boundary and Lean checks.** `Size` enforces both periods at least three. Thus there are no loops or repeated unoriented bonds, and the four entries of `torusNeighbours x` are distinct, including at period three. Torus subtraction is in `ZMod`, so it is not truncated natural subtraction. The four incident bonds are the two starting at x and the two starting at its negative-direction neighbours. In this fixed orientation there are exactly two incoming signs, so `centreSign x = 1`; the statements correctly retain the product of signs instead of relying on that simplification.

`IcoLetter = Fin 3 × Fin 2 × Fin 2` has twelve elements and is nonempty; `Site` and the torus configuration space are nonempty finite types. Classical decidability for supports, filters and function equality is a proof convenience, not a missing mathematical hypothesis. Lean inspection confirms no required instance argument was silently dropped.

`torusReference σ = (5/12)^|Site|` is strictly positive and independent of σ. It is unnormalized: its total mass is `5^|Site|`. The local projection uses the same `5/12` factor as the product reference. All displayed divisions by 5, 12 and ground-state norms have the intended real or complex types; there is no integer-division or rational-coercion mismatch. Although Lean defines division at zero, every denominator that needs cancellation is nonzero under these statements’ explicit hypotheses.

Proper colouring is unnecessary in the two factorization leaves, which allow zero determinant values. In the remaining relevant leaves, nonvanishing and density identities are explicit premises. These premises have the paper’s intended instances for proper colourings, for example the `3 × 3` colouring `(i,j) ↦ i+j mod 3`. Some improper colourings make a premise false, but this does not make the universally quantified leaves vacuous. The generic polarization leaf also handles empty finite types correctly; no nonemptiness premise is required there.

**IncidentEvaluationStatement — TRUE; medium.**

Evaluating statePolynomial ψ gives physicalEval ψ exactly: the binomial square-root factors and the monomialDegree exponents agree. Each of the four incident singlets evaluates to edgeSign x e times the centre-first determinant, and the incident-edge/other-endpoint map bijects with torusNeighbours x because both periods are at least three. independentAt x χ makes the residual evaluation constant under changing σ x, supplying the scalar in inFibreSpan. No colouring or residual-isometry premise is needed.

Proof route (two steps only):

1. Evaluate the supplied polynomial factorization and reindex the four incident bonds by their distinct neighbouring endpoints, collecting centreSign.
2. Use the zero exponents guaranteed by independentAt to make the residual evaluation invariant under Function.update; choose this value times centreSign as the fibre scalar.

Lean traps: The residual is evaluated as an MvPolynomial, with no degree-four isometry claim. The fibre scalar may depend on the exterior configuration, but must be independent of the new centre letter. monomialDegree uses natural subtraction only with Fin 5 exponents at most four.

**GroundFibreFactorizationStatement — TRUE; medium.**

The explicitly assumed evaluation/product identity can be split into incident and nonincident factors. The incident factors are centreSign x times beta κ x; the remaining factors, multiplied by centreSign x, are exactly rho κ x. No nonincident factor uses σ x, so rho is invariant under updating that coordinate. The four distinct neighbours and absence of repeated unoriented bonds follow from Size={n:ℕ // 3≤n}, including period three.

Proof route (two steps only):

1. Partition the supplied bond product into incident and nonincident factors and reindex the incident product by the four neighbours, retaining orientation signs.
2. For every nonincident bond, both endpoints differ from x; simplify Function.update at those endpoints to obtain rho invariance.

Lean traps: The product over Bond is a Fintype product, whereas torusNeighbours is a deduplicating Finset. Their incidence bijection needs the bound in Size. rho already contains centreSign; it must not be inserted a second time.

**GroundTransformStatement — TRUE; easy.**

With b(σ)=frameEval κ (B L N) σ and r=‖B L N‖, the hypotheses give r>0, b(σ)≠0 and μ(σ)=π(σ)|b(σ)|²/r². Thus |f(σ)b(σ)/r|² yields the asserted weighted squared norm identity, and both inverse identities cancel nonzero factors. The conclusion supplies precisely finite norm/inverse identities, not a bundled unitary map.

Proof route (two steps only):

1. Expand groundTransform and the density identity; use multiplicativity of Complex.normSq and normSq of the real cast r.
2. For both inverse identities, use function extensionality and cancel b(σ) and (r:ℂ), deriving their nonzero facts explicitly.

Lean traps: weightedNorm is a squared norm. Derive ‖B‖>0 and (‖B‖:ℂ)≠0 before cancelling; keep the real density denominator ‖B‖² separate from its complex casts. This leaf states norm and inverse identities rather than constructing a bundled unitary equivalence.

**FibreIntertwiningStatement — TRUE; hard.**

The singleton AgreeOutside fibre is in bijection with a ↦ Function.update σ x a. The reference weight is constant, rho is constant and nonzero on this fibre, and the density premise therefore makes conditionalExpectation the ratio with weights (5/12)|beta(σ_a)|². This is exactly the coefficient obtained by inserting groundTransform f into fibreProjection. Positivity of all displayed denominators follows from the supplied nonvanishing and B≠0. The blockDirichlet equality is the weighted squared norm of this same residual; no independent probability or isometry premise is missing.

Proof route (two steps only):

1. Reindex the full singleton conditional sum by centre letters; factor out the positive outside reference weight, |rho|² and ‖B‖⁻², then compare the two explicit quotients.
2. Rewrite the projected residual as groundTransform of f minus its conditional expectation, and use the density identity pointwise before summing to obtain blockDirichlet.

Lean traps: conditionalExpectation sums over full configurations satisfying AgreeOutside, not directly over centre letters. Reindex by the singleton-fibre bijection, with no extra multiplicity. Its denominator is complex, while fibreDenominator is real and then cast. rho≠0 follows from the supplied nonzero ground evaluation and factorization.

**FibreProjectionStatement — TRUE; hard.**

IcoLetter is nonempty with twelve elements, so the sum of (5/12)|beta(σ_a)|² is strictly positive under the premise. The numerator and denominator are invariant under updating the centre again, making the formula a scalar multiple of beta on each fibre. It fixes every such multiple. The local conjugate-first least-squares identity, summed against the positive exterior product reference weight, proves the global best-approximation inequality. No torusLaw, proper-colouring or ground-state premise is required.

Proof route (two steps only):

1. Prove denominator positivity, use Function.update_update to make the coefficient fibre-constant, and substitute h=c*beta to prove the fixed-point identity.
2. Show each fibre residual has zero weighted inner product with beta, apply the finite least-squares identity, and sum over exterior configurations using the product reference weight.

Lean traps: Repeated centre updates collapse, so numerator and denominator are fibre-constant even for arbitrary h. Global least squares needs the positive product reference weight and an exterior-fibre sum. Standard unweighted Pi norms cannot replace weightedNorm.

**WeightedPolarizationStatement — TRUE; medium.**

weightedInner is Hermitian and conjugate-linear in its first slot because w is real, even when some weights are negative. Its diagonal equals the real cast of weightedNorm. Complex linearity of E and equality of the diagonal quadratic forms determine both real and imaginary parts of the full inner product by polarization. Neither positivity nor normalization of w is missing; empty finite index types also satisfy the implication.

Proof route (two steps only):

1. Expand the weighted quadratic form at ψ+φ and ψ-φ and use the norm-isometry premise to identify the real part.
2. Repeat with ψ+iφ and ψ-iφ to identify the imaginary part, using complex linearity of E and Mathlib’s conjugate-first inner product.

Lean traps: Both Fintype binders survive elaboration. E must be complex-linear: norm preservation of a merely real-linear map would not determine the complex inner product. With conjugation in the first slot, the imaginary-part formula uses Q(ψ−iφ)−Q(ψ+iφ), in that order. Classical decidability is available without an additional premise.

**GroundQuotientVarianceStatement — TRUE; medium.**

Writing b=frameEval κ B, p=frameEval κ ψ and r=‖B‖>0, the explicit density and b≠0 give complexMean μ (r*p/b)=weightedInner π b p/r=inner ℂ B ψ/r=0. With this mean zero, the variance reduces termwise to weightedNorm π p; the supplied inner-product isometry on (ψ,ψ) identifies this with ‖ψ‖². No extra probability premise or residual-polynomial isometry is needed.

Proof route (two steps only):

1. Substitute the density and quotient, rewrite |b|²=conj(b)*b, cancel b and r, and apply the supplied isometry to (B,ψ) to obtain mean zero.
2. Replace the mean in variance by zero, cancel squared moduli pointwise, and take real parts of the isometry at (ψ,ψ).

Lean traps: The mean uses weightedInner π (frameEval κ B) (frameEval κ ψ), in that order. Complex.normSq_eq_conj_mul_self requires a cast into ℂ. Obtain the real norm equality by taking real parts of the supplied self-inner-product equality; no assumption ∑π=1 is available or needed.

**BetaNonzeroStatement — TRUE; easy.**

Every neighbour y is the other endpoint of a positively indexed incident bond: outgoing from x for positive neighbours, or outgoing from y for negative neighbours. Its centre-first determinant is therefore either the assumed determinant or its negative. Strict positivity of its Complex.normSq rules out zero; the finite product defining beta is nonzero. The premise quantifies over all bonds and all configurations and does not need a separate proper-colouring premise.

Proof route (two steps only):

1. For each neighbour, select its actual positive-direction bond and convert the assumed positive squared modulus into determinant nonvanishing.
2. For incoming bonds use determinant antisymmetry, then apply finite-product nonvanishing to the product defining beta.

Lean traps: Negative-direction neighbours are endpoints of bonds starting at the neighbour. Reverse their determinant arguments using antisymmetry before applying the nonzero product lemma. The strict squared-modulus premise already supplies nonvanishing, so no frame-separation theorem needs to be imported as an extra hypothesis.

**Verification and limits.** The conclusions above come from checking the definitions against the paper’s finite algebra, not from treating numerical checks as proofs. No proofs were written.

- A single Lean 4.35.0-rc2 process imported `AKLT.Blueprint.Q.NodesQuantum`, printed all eight elaborated definitions, checked the relevant argument types and inner-product conventions, and synthesized the finite/decidable instances. It exited with status 0. See [inspect.lean](/home/ubuntu/aklt/reports/TS_Q_06/scratch/inspect.lean) and [inspect.log](/home/ubuntu/aklt/reports/TS_Q_06/scratch/inspect.log). This is declaration inspection, not a proof of the leaves.
- [audit_checks.py](/home/ubuntu/aklt/reports/TS_Q_06/scratch/audit_checks.py) exhaustively checked the incident-bond/unique-neighbour correspondence at 1,089 sites across all periods `3 ≤ L,N ≤ 8`, including period three. It numerically checked all 864 ordered cross-frame letter pairs; the minimum determinant squared modulus was approximately `0.002736566358911097`, matching `(5−√5)/1010`.
- With fixed seed 6006, 100 samples checked the actual 12-letter fibre formulas for factorization, rho invariance, nonzero beta, projection fixed points, least squares, intertwining, weighted norm and Dirichlet residuals. Another 100 samples checked polarization for a signed-weight isometry; an abstract quotient example checked its zero mean and variance. These signed weights were used only to inspect the generic algebra, not as an instance of `torusLaw`. Results are in [audit_checks.json](/home/ubuntu/aklt/reports/TS_Q_06/scratch/audit_checks.json).
- No sub-agents were launched, no repository files were modified, and no repository build was run. Scratch imports used the repository’s existing compiled modules and a symlink to its package directory. The final repository `git status --short` was empty.
