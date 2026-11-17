STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| [AKLT.Blueprint.H1.BlochPositivityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPauli.lean:17) | TRUE | medium | Hermitian eigenvalues have square at most one. |
| [AKLT.Blueprint.H1.PauliExpansionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPauli.lean:34) | TRUE | medium | The hypotheses give exactly the Pauli-indexed monomials. |
| [AKLT.Blueprint.H1.PauliProductTraceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPauli.lean:42) | TRUE | medium | Finite tensor trace factorization; no affineness needed. |
| [AKLT.Blueprint.H1.InversionPolynomialStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPauli.lean:52) | TRUE | medium | Signs preserve support and cancel on double inversion. |
| [AKLT.Blueprint.H1.ProductDensityPositiveStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPauli.lean:60) | TRUE | medium | Tensor products preserve positive semidefiniteness. |
| [AKLT.Blueprint.H1.TraceProductPositiveStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPauli.lean:67) | TRUE | medium | A PSD square root gives a PSD congruence with the same trace. |
| [AKLT.Blueprint.H1.ReducedDegreeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesReduction.lean:12) | TRUE | medium | Internal support is retained and separate spin degree is at most four. |
| [AKLT.Blueprint.H1.ReducedFactorStructureStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesReduction.lean:18) | TRUE | medium | Tokens are disjoint and factors preserve scalar products. |

All eight leaves are true and self-sufficient as written. No additional premises or corrections are needed; every `fix` field in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_H1M_03/verdicts.jsonl) is empty. Difficulty estimates concern Lean formalization, including polynomial-support and finite-index bookkeeping. No proofs were written.

The audit used repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The paper arguments are [d:reduction and c:reduce](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:145), and [d:Pauli and l:inversion](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:249). The repository was left unchanged.

The exact statements were followed through these definitions:

- [Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:53): `pauli` and `spinDensity`; [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9): `Vec3`, `dot`, `normSq`, and `Status`.
- [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:117): `VectorAffine`, `invertPolynomial`, `pauliExponent`, and `pauliOperator`; [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:59): `evaluateReduced`, `productDensity`, and `invertVectors`; [OperatorContracts.lean](/home/ubuntu/aklt/repo/AKLT/Defs/OperatorContracts.lean:36): `SupportedVectors`.
- [H1/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/Definitions.lean:14): polynomial abbreviations, `localEvaluation`, `InternalAdmissible`, `LocalVectorAffine`, `LocalSupportedVectors`, `IntegrandInvariant`, and `pauliCoordinate`.
- [Operator.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Operator.lean:10): `Representation`, `patternDegree`, `SingleReplacement`, `reducedSpinSites`, `reductionGroups`, `groupLeader`, `groupSecond`, `groupIsPair`, `reductionVectors`, `replacementRadius`, `leafNeighbour`, `LocalVariable`, `formalDot`, and `reducedIntegrand`.
- [Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:9): the template sets, `PatternData`, `statusAt`, `keptAt`, `Covered`, `bonds`, and `active`; [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8): `Plane`, compass steps, distances, `square`, adjacency, neighbours, positive neighbours, and `internalBonds`.
- Mathlib's [IsHermitian](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean:44), [PosSemidef](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:62), [finite quadratic-form interpretation](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean:300), [trace](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean:45), [complex order](/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/Analysis/Complex/Order.lean:40), and `Finsupp.equivFunOnFinite` were checked against their intended meanings.

1. **BlochPositivityStatement.** Tracelessness is unnecessary: every real eigenvalue satisfies `λ² = r ≤ 1`. The cases `A = I`, `A = -I`, and `r = 0` are included. The argument needs no division by a norm or by `sqrt r`.

   Route: Diagonalize `A` and transfer its square identity to `λ² = r` for each eigenvalue.  
   Deduce `λ ≥ -1` and apply the nonnegative-eigenvalue criterion to `(1+A)/2`.

2. **PauliExpansionStatement.** The whole-vector exponent bound permits no coordinate or exactly one coordinate per token. Support excludes tokens outside `J`. This gives a unique Pauli label function, with coefficient zero for labels absent from the support. Empty `J` gives the constant coefficient; the zero polynomial is also covered.

   Route: Identify each supported exponent with its unique label function, assigning zero to unused tokens.  
   Reindex the finite monomial evaluation and simplify each monomial to the displayed coordinate product.

3. **PauliProductTraceStatement.** Both matrices use `J → Fin 2` as their basis. The one-site trace identity is an explicit, satisfiable premise, also established by `singlePauliTrace` in the source module. No affineness, support, or norm premise is missing: both sides select the same Pauli coefficients of arbitrary `p`.

   Route: Expand the finite Pauli sum, matrix multiplication, and trace, then interchange the finite sums.  
   Factor each tensor trace into one-site traces, apply the premise, and reconcile the coefficient casts.

4. **InversionPolynomialStatement.** Each monomial coefficient is multiplied by a nonzero rational sign, preserving its exponent and support. Vector inversion supplies the same signs again. Arbitrary `I`, including `I ⊈ J`, is valid. Groupwise inversion is not required for this statement.

   Route: Compute the signed image of a monomial and transfer support and whole-vector degree bounds.  
   Compose evaluation with vector inversion and cancel the two signs on every coordinate.

5. **ProductDensityPositiveStatement.** The PSD premise covers exactly the tensor factors, supplying all positivity needed without a separate norm bound. Empty `J` gives a singleton function-space basis and the one-by-one matrix `[1]`.

   Route: Induct on `J`, splitting the function-space basis into one `Fin 2` coordinate and the remaining coordinates.  
   Apply `Matrix.PosSemidef.kronecker` and transport by reindexing, starting from `[1]`.

6. **TraceProductPositiveStatement.** PSD factors need not commute, and their product need not be Hermitian. A Hermitian square root gives a PSD congruence with the same trace. Empty `n` gives trace zero, an intended boundary case within a nonvacuous universal statement.

   Route: Choose a Hermitian PSD square root `S` of `A` and apply PSD congruence to `S*B*S`.  
   Use trace cyclicity and `S*S = A`, then take the real part of the nonnegative trace.

7. **ReducedDegreeStatement.** Both requirements hold: internal support lies in `reducedSpinSites`, and separate whole-spin degree is at most four. Retained corners have at most two bonds and two slots. At axial sites, replacing a leaf replaces one incident bond by one linear factor. The actual Lean integrand retains the passage, with at most three current bonds or two next bonds. Each single replacement has a unique retained neighbour, so `leafNeighbour` never uses its fallback. No moment or leaf-integration premise is missing.

   Route: Check template incidence and deletion rules to locate every factor's internal coordinates in the retained set.  
   Bound each spin's degree by its incident linear factors; changing to `next` only deletes a bond.

8. **ReducedFactorStructureStatement.** Corner pairs use `{0,1}`, `{2,3}`, `{4,5}`, `{6,7}`; a single corner keeps its leader alone. Tip leaders are `8`, `11`, `14`, `17`. No token repeats, and `reductionVectors` contains them all. `formalDot` evaluates to the real scalar product. The invariant predicate transforms spins and vectors together, so `RᵀR = I` preserves every factor, including under reflections. No finite-law covariance or norm hypothesis is needed here.

   Route: Check disjoint group-token lists, then propagate token support and vector-degree bounds through products.  
   Evaluate scalar-product factors and use `RᵀR = I` to preserve them under simultaneous transformation.

The Lean traps are bookkeeping issues, not statement defects:

- `J` is a `Finset (Fin 20)`; `j : J` ranges over its finite subtype. Tensor indices and Pauli labels use the entire function type. An empty domain therefore gives one function.
- `VectorAffine` bounds the sum of all three coordinate exponents of a token, not each scalar exponent separately. `pauliCoordinate` branches at zero before natural subtraction `a.val - 1`, consistently reversing `pauliExponent`'s coordinate index plus one.
- Coefficients and radii are rational; evaluation uses `Rat.castHom ℝ`; operators use complex coefficients. The direct cast `ℚ → ℂ` agrees with the cast through `ℝ`. The complex scalar `1 / 2` has a positive real value.
- Under `ComplexOrder`, nonnegative complex numbers have nonnegative real part and zero imaginary part. `PosSemidef` includes Hermitian symmetry and quadratic-form positivity, not entrywise positivity. The optional matrix-order API needs the separate `MatrixOrder` scope.
- Classical decidability is needed when manipulating the noncomputable definitions, subtype function spaces, and `groupIsPair`; it is not a missing mathematical premise. All eight definitions are closed. The `Fintype` and `DecidableEq` instances in trace positivity are explicitly retained; `n : Type` restricts it to universe zero without harming the stated result.
- `groupLeader` is injective only on allowed groups, not globally on `Plane`. `groupSecond`'s `min 19` never truncates a corner's second slot. The list order and default in `leafNeighbour` are harmless after establishing unique incidence. Polynomial support arguments need inclusion, allowing cancellations.

The hypotheses are nonvacuous. A covered pattern exists: take outgoing east, status `X` at the south neighbour and `U` everywhere else, the prescribed three kept neighbours at the passage, and all four directions elsewhere. Zero and constant polynomials, zero Hermitian matrices, and zero vector assignments supply ordinary Pauli examples. Empty tensor products and empty traces match the paper's conventions.

[Inspect.lean](/home/ubuntu/aklt/reports/TS_H1M_03/scratch/Inspect.lean) imports the existing compiled module and uses only `#print`/`#check`. Its final run exited successfully; [inspect.out](/home/ubuntu/aklt/reports/TS_H1M_03/scratch/inspect.out) records the elaborated declarations and available matrix APIs. This checks statements and APIs without proving the leaves. Only one Lean process ran at a time, and no repository modules were built.

[check_geometry.py](/home/ubuntu/aklt/reports/TS_H1M_03/scratch/check_geometry.py) checked all **65,536 subsets of the 16 template edges**, in both representations: **131,072 cases**, with zero failures. Maximum spin factor degree was four in each representation; all internal factor coordinates were retained, each single had a unique retained neighbour, and tokens never collided. The check overapproximates covered graphs using all sites active: an inactive site is isolated and contributes no factor. Current-factor counts also bound `next`, which only removes a bond. [geometry_checks.json](/home/ubuntu/aklt/reports/TS_H1M_03/scratch/geometry_checks.json) records the results. These diagnostics support the definition audit; the verdicts rest on the mathematical arguments above.
