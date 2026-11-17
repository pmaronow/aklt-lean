STATUS: COMPLETE

All eight leaves are **TRUE** as written and self-sufficient. No additional premise or statement correction is required. None is classified as VACUOUS. Difficulty refers to formalizing the stated route in Lean; no proofs were written.

| Leaf (namespace `AKLT.Blueprint.Q`) | Paper label | Verdict | Difficulty | Decisive check |
|---|---|---|---|---|
| [StarWitnessStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesStar.lean:16) | `l:star` | TRUE | medium | Each of the four projections fixes a nonzero extremal tensor. |
| [PositiveSpectralMinimumStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesStar.lean:21) | `l:star` | TRUE | easy | The positive real spectrum is finite and explicitly nonempty. |
| [SpectralKernelCoercivityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesStar.lean:31) | `l:star` | TRUE | hard | The spectral bound controls precisely the nonzero modes. |
| [StarAmplificationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesStar.lean:48) | `l:star` | TRUE | hard | The premise gives a direct sum of identical star operators. |
| [StateEvaluationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesPolynomial.lean:11) | `d:poly` | TRUE | easy | The monomial exponents and binomial factors agree exactly. |
| [VbsHomogeneityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesPolynomial.lean:18) | `p:toruskernel` | TRUE | medium | Exactly four degree-one incident factors meet every site. |
| [CoefficientReconstructionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesPolynomial.lean:24) | `d:poly` | TRUE | medium | Homogeneous exponents are exactly the configuration exponents. |
| [PairDiagonalDivisionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesPolynomial.lean:38) | `l:edge` | TRUE | medium | The diagonal kernel and determinant image both have dimension 16. |

**Audit scope and definitions.** The inspected repository was branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The paper comparison uses [sec3-quantum-frames.tex](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:14), specifically `d:poly`, `l:edge`, `p:toruskernel` and `l:star`. The repository was only read.

The star dependency trace is `StarHilbert` → Euclidean coordinates on `Fin 5 → Fin 5`; `starHamiltonian` → four eigenspace projections → `starCasimir` → `starAtSite` → the frozen `spinZ`, `spinPlus`, `spinMinus` matrices. These definitions are in [Defs/Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:23) and [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:49). The abstract spectral leaves additionally unfold `kernelCoercivity`; amplification unfolds `amplifiesStar`, both in [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:121).

The polynomial dependency trace includes `Size`, its nonzero-modulus instance, `Site`, `Direction`, `Bond`, `nextSite`, `bondSites`, `Configuration`, `Hilbert`, `SpinorPolynomial`, `singlet`, `vbsPolynomial` and `monomialDegree` from [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:17); `Spinor` from [Defs/Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:50); `physicalEval` from [Defs/Polynomial.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Polynomial.lean:33); `polynomialState` from [Defs/Quantum.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Quantum.lean:14); and `statePolynomial`, `siteHomogeneous`, `PairHilbert`, `PairPolynomial`, `pairPolynomial`, `pairDiagonal`, `pairSinglet` from [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:72). No other blueprint leaf is assumed in these verdicts.

Mathlib conventions were also checked: `EuclideanSpace` is the `WithLp 2` function space with the sum inner product; `IsSymmetric` is sesquilinear self-adjointness; `HasEigenvalue` means a nontrivial eigenspace; `eigenspace` is the appropriate linear-map kernel; `starProjection` is the ambient orthogonal projection. For multivariate polynomials, the checks cover the monomial, coefficient/support, evaluation and variable-renaming definitions.

**Per-leaf reasons, routes and Lean traps.**

**`AKLT.Blueprint.Q.StarWitnessStatement` — TRUE (medium).** The nonzero coordinate vector supported at the constant-4 configuration is a 20-eigenvector of each frozen starCasimir. Each orthogonal eigenspace projection fixes it, so their four-term sum has eigenvalue 4. The finite-dimension and nonzero-vector requirements are supplied by the concrete definitions.

Proof route, line 1: Use the basis vector supported at sigma(x)=4 and compute each two-site Casimir action from spinZ, spinPlus and spinMinus.  
Proof route, line 2: Projecting a vector already in each 20-eigenspace fixes it; sum over Fin 4 and use the nonzero coordinate to obtain HasEigenvalue.

Lean traps: Use a coordinate basis vector supported at the constant configuration, not the vector having every coordinate equal to one. The code uses magnetic labels 2-j, so label 4 has total pair Z-weight -4; its Casimir eigenvalue is still 20. Module.End multiplication is composition, Matrix.toEuclideanLin uses matrix-times-column action, and (1/2 : ℂ) is complex division. HasEigenvalue requires a nonzero vector; merely exhibiting membership in an eigenspace is insufficient.

**`AKLT.Blueprint.Q.PositiveSpectralMinimumStatement` — TRUE (easy).** In finite dimension the set of complex eigenvalues is finite; injectivity of the real-to-complex cast makes the positive real eigenvalue set finite. The explicit existence premise makes it nonempty, so its infimum is an attained, strictly positive minimum. Symmetry and positivity are stronger than needed for this particular conclusion.

Proof route, line 1: Pull finite_hasEigenvalue back along the injective real-to-complex cast and intersect with the strictly positive reals.  
Proof route, line 2: Use the supplied witness and finite-set minimum/sInf lemmas to obtain membership, positivity and the lower-bound property.

Lean traps: sInf is the real conditional infimum: invoke nonemptiness and lower boundedness (0 is a lower bound) before its comparison lemmas. Strict positivity follows from attainment in the finite positive set, not from lower boundedness alone. Eigenvalues are complex and parameters here are real, so use injectivity of Complex.ofReal when pulling back the finite set. If ι is empty the eigenvalue-existence premise fails; this harmless branch does not make the whole leaf vacuous.

**`AKLT.Blueprint.Q.SpectralKernelCoercivityStatement` — TRUE (hard).** Complex IsSymmetric supplies an orthonormal eigenbasis with real eigenvalues, and the quadratic-form premise makes every eigenvalue nonnegative. The positive eigenvalue bound controls exactly the coordinates outside the zero eigenspace, which equals ker T. The zero operator and empty index type give a valid zero inequality rather than a counterexample.

Proof route, line 1: Diagonalize the finite-dimensional symmetric operator and use the nonnegative quadratic form to show its real eigenvalues are nonnegative.  
Proof route, line 2: Identify the kernel projection with the zero-eigenvalue coordinates and compare the remaining squared coordinates term by term using g <= mu.

Lean traps: Over ℂ, IsSymmetric uses the conjugate-linear-first inner product and gives Hermitian spectral theory. The real-part positivity hypothesis controls all real eigenvalues; symmetry makes the full spectrum real. The norm is distance from the kernel projection, and zero modes must be retained in the kernel. Finite-dimensional Euclidean space supplies completeness and orthogonal projections; an additional closedness premise is unnecessary. No existence of a positive eigenvalue is needed: T=0 gives equality for every positive g.

**`AKLT.Blueprint.Q.StarAmplificationStatement` — TRUE (hard).** The displayed amplifiesStar premise is a pointwise intertwining identity with a direct sum of n copies of starHamiltonian. A linear isometry equivalence transports both the kernel and its orthogonal projection. Summing the supplied coercivity inequality over slices proves the conclusion for every real g; no positivity premise on g is needed, and n=0 is harmless.

Proof route, line 1: In the target Euclidean space identify the conjugated kernel with all vectors whose individual Fin n slices lie in ker starHamiltonian, and its projection with the slice projections.  
Proof route, line 2: Sum the assumed star inequality over slices, use the product-coordinate norm and inner-product identities, and transport back through U.

Lean traps: amplifiesStar is universally quantified in ψ, r and s, so it specifies every coordinate of the conjugated operator. Its WithLp.toLp 2 slice uses the standard sum norm, with no averaging or n-dependent scalar. Transport the kernel projection as well as the operator. The statement quantifies over every real g; summing inequalities needs no sign assumption. At n=0 the target space is zero, and the isometry makes the source zero too.

**`AKLT.Blueprint.Q.StateEvaluationStatement` — TRUE (easy).** Evaluating each monomialDegree sigma gives the product over sites of z(x,0)^(4-sigma(x)) z(x,1)^sigma(x). The coefficient is psi(sigma) times the same square-root binomial product used by physicalEval, so finite-sum evaluation and product distributivity give precisely the stated identity. Spinors need no unit-norm or compatibility premise.

Proof route, line 1: Expand statePolynomial, commute MvPolynomial.eval with the sum, and evaluate C and monomial.  
Proof route, line 2: Replace the finite product over Site x Fin 2 by the two-coordinate product at each site, unfold monomialDegree, and collect factors to match physicalEval.

Lean traps: The physicalEval product binder includes all three factors: the square-root binomial and both spinor powers. MvPolynomial.monomial uses coefficient 1 here, and eval is a ring homomorphism. monomialDegree uses if k=0 then 4-j else j; Fin 2 has exactly those two coordinates, while Fin 5 ensures j<=4, so natural subtraction does not truncate an out-of-range exponent. WithLp is only the coordinate wrapper here. The spinors are arbitrary, including zero.

**`AKLT.Blueprint.Q.VbsHomogeneityStatement` — TRUE (medium).** Each singlet has site degree one at each of its two different endpoints and zero elsewhere. For every Size, each site belongs to exactly the two outgoing and two incoming indexed bonds, including period three, giving degree four in the full product. The Size bound supplies the required geometry without another premise; the product is also nonzero, so support homogeneity is not merely vacuous.

Proof route, line 1: Give each variable (x,k) the site weight concentrated at x; each loop-free singlet is homogeneous of endpoint degree one.  
Proof route, line 2: Multiply these degrees over all indexed bonds and count the two incoming and two outgoing factors at each site, using L,N >= 3.

Lean traps: The product is indexed by the Fintype Bond = Site × Fin 2, whereas bondSites is a two-element Finset of endpoints. Count incident indexed bonds, rather than assuming a cardinality conversion. Size = {n : ℕ // 3<=n} excludes moduli 0, 1 and 2 and supplies the nonzero ZMod modulus instance. At period three, +1 and -1 are still different; possible edges between neighbours do not change the four incident factors. Cancellation can remove monomials but cannot create another site degree.

**`AKLT.Blueprint.Q.CoefficientReconstructionStatement` — TRUE (medium).** A supported exponent m with m(x,0)+m(x,1)=4 has the unique configuration sigma(x)=m(x,1), whose value is at most four, and monomialDegree sigma=m. Thus the homogeneous-support premise rules out all coefficients discarded by polynomialState. Every denominator factor is the positive square root of choose(4,j) for j<5, so extraction followed by rescaling restores each coefficient, including for p=0.

Proof route, line 1: Show monomialDegree is injective and its image consists exactly of exponent vectors of site degree four, decoding sigma(x) from m(x,1).  
Proof route, line 2: Use coefficient extensionality, the support hypothesis, and nonvanishing of every square-root binomial product to cancel the extraction denominator.

Lean traps: The support condition allows p=0 and imposes no nonzero premise. To decode a supported exponent, first derive m(x,1)<=4 from its sum with m(x,0), then construct its Fin 5 value and justify 4-m(x,1)=m(x,0). Division is in ℂ, after taking a real square root and casting it. The five binomial values are 1,4,6,4,1, all positive; prove each denominator product nonzero before cancellation. Off-image coefficients vanish by site homogeneity.

**`AKLT.Blueprint.Q.PairDiagonalDivisionStatement` — TRUE (medium).** pairPolynomial always has bidegree (4,4), and rename Prod.snd is exactly substitution of equal endpoint spinors. On that 25-dimensional coefficient space diagonal evaluation has rank 9. Multiplication by the nonzero pairSinglet maps the 16-dimensional bidegree-(3,3) space injectively into its 16-dimensional kernel, so every polynomial in that kernel is divisible. The bidegree restriction is supplied by the definition, not missing from the hypotheses.

Proof route, line 1: Work in the fixed bidegree-(4,4) coefficient space: diagonal evaluation is onto the degree-eight binary forms, so its kernel has dimension 25-9=16.  
Proof route, line 2: Multiplication by pairSinglet injects the 16-dimensional bidegree-(3,3) space into that kernel; equality of the subspaces gives the required divisor.

Lean traps: Prod.snd identifies the two sites while retaining the spinor coordinate; it is the intended polynomial diagonal substitution. The bidegree restriction is built into pairPolynomial through j,k : Fin 5 and the exponents 4-j,4-k. Vanishing under diagonal substitution does not imply determinant divisibility for an arbitrary four-variable polynomial, so preserve this restriction throughout the argument. The positive square-root binomial factors form an invertible coordinate change and do not alter the ranks. Divisibility is in the commutative polynomial ring; ψ=0 is allowed.

**Shared instance and decidability check.** The elaborated statements retain every generic `[Fintype ι]` binder, the isometry `U`, and all stated hypotheses. There is no silently dropped instance that changes the mathematical scope. A writer may need `classical` for polynomial supports, complex equality, finite-set filters and coordinate basis manipulations; this is a decidability choice, not a missing mathematical hypothesis. `Fintype` ranges and `Finset` supports must be handled separately. The generic spectral statements quantify over `ι : Type` as written; no larger-universe claim is inferred.

**Verification and its limits.** [scratch/Inspect.lean](/home/ubuntu/aklt/reports/TS_Q_03/scratch/Inspect.lean) imports only the two assigned modules and prints their elaborated statements, three coordinate definitions, and the relevant Mathlib API types. The final Lean run exited 0 using the repository toolchain `v4.35.0-rc2`; [lean-inspection.txt](/home/ubuntu/aklt/reports/TS_Q_03/scratch/lean-inspection.txt) preserves the output. No target leaf was proved or assumed as an axiom. A single Lean process ran at a time; all imports used existing compiled files through read-only library paths. The local `.lake/packages` entry is a symlink to the supplied packages.

The standard-library Python checks in [scratch/checks.py](/home/ubuntu/aklt/reports/TS_Q_03/scratch/checks.py) use exact rational row reduction: diagonal evaluation has rank 9, determinant multiplication has rank 16, and their composite is zero. Exact sparse application of the frozen five-site matrices gives Casimir eigenvalue 20 at all four leaves for both constant-0 and constant-4 basis vectors. Additional checks cover all local degree-four exponent pairs, all five positive binomial values, and bond/neighbour counts on all 36 tori with periods from 3 through 8. [checks-output.json](/home/ubuntu/aklt/reports/TS_Q_03/scratch/checks-output.json) records the successful checks. These finite checks support the audit; the universal conclusions use the paper arguments and definition analysis above.
