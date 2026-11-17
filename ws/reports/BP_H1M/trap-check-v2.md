# V2 per-leaf trap checks

Old kept/superseded leaf checks are preserved in `leaves.json` and `trap-check.md`. All 13 new manifest entries are audited below.

## AKLT.Blueprint.H1.PauliExpansionStatementV2

- **premises**: All required mathematical premises are explicit. The definition is a closed Prop and assumes no other blueprint leaf proposition.
- **vacuity_and_degenerate**: For n=0, necessarily J is empty and J->Fin4 has one member. The operator is scalar on C, not a zero-dimensional matrix. J empty is also allowed for positive n.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: The unchanged pauliCoordinate uses a.val-1 only after the a.val=0 guard; its index proof is retained in the frozen definition.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.PauliProductTraceStatementV2

- **premises**: The mathematical one-slot trace identity is explicit; affineness is unnecessary because both sides select the same Pauli exponents. Irrational real coefficients are permitted.
- **vacuity_and_degenerate**: Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.InversionPolynomialStatementV2

- **premises**: Affineness/support are explicit; sign cancellation is valid even when I is not a subset of J. The public Top contract imposes I subset J when used.
- **vacuity_and_degenerate**: Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.ProductDensityPositiveStatementV2

- **premises**: Every individual density on J is assumed PSD; no invertibility, positive definiteness, or trace normalization is needed by this tensor-positivity step.
- **vacuity_and_degenerate**: J empty yields the 1-by-1 matrix [1]. Arbitrary n and token counts above 20 are permitted.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.InversionBallStatementV2

- **premises**: All required mathematical premises are explicit. The definition is a closed Prop and assumes no other blueprint leaf proposition.
- **vacuity_and_degenerate**: n=0 makes the j quantifier empty; for n>0 the equality also holds at the zero vector.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.RationalEmbeddingStructureStatementV2

- **premises**: Affineness and support of the rational polynomial are explicit; support inclusion suffices even if a coefficient map deletes terms.
- **vacuity_and_degenerate**: Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.RationalEmbeddingEvaluationStatementV2

- **premises**: All required mathematical premises are explicit. The definition is a closed Prop and assumes no other blueprint leaf proposition.
- **vacuity_and_degenerate**: Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.
- **coercions**: Both evaluations take values in R. The rational coefficients are embedded once using Rat.castHom R; no change to vector coordinates.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.DifferenceStructureStatementV2

- **premises**: Affineness, invariance and support are supplied separately for both polynomials. c is arbitrary real, not restricted to rational thresholds.
- **vacuity_and_degenerate**: Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.DifferenceEvaluationStatementV2

- **premises**: All required mathematical premises are explicit. The definition is a closed Prop and assumes no other blueprint leaf proposition.
- **vacuity_and_degenerate**: Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.
- **coercions**: c is a real scalar multiplying the rational-to-real evaluations; no c-as-rational term appears anywhere.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.AffineEvaluationStatementV2

- **premises**: Whole-vector degree <=1 is essential; coordinatewise multiaffineness alone would be insufficient. The output is the existing 20-token affine-function predicate needed for the unchanged convex-extension leaf.
- **vacuity_and_degenerate**: Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.RealDifferencePauliInterpolationStatementV2

- **premises**: The identity holds for arbitrary real c and any inversion; neither coveredness nor group inversion is needed for coefficientwise linearity.
- **vacuity_and_degenerate**: At c=1/3 or 2/3 one interpolation weight vanishes. Weights may be negative elsewhere; this is not interpolation of PSD/PD.
- **coercions**: The exact rational matrices at thresholds 1/3 and 2/3 are multiplied by real weights embedded in C. No rational approximation to c is used.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.H1.OperatorStructureLinearCombinationStatementV2

- **premises**: Both input matrices satisfy the explicit mathematical predicate OperatorStructureAtV2. This predicate contains no positivity claim, so real coefficients of either sign are legitimate.
- **vacuity_and_degenerate**: Zero coefficients, the zero matrix, empty groups, and empty tensors are allowed. Fixed pair projections are shared by both input properties.
- **coercions**: Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.
- **finite_sums**: Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.
- **nat_subtraction**: No unguarded natural subtraction is introduced.
- **division_by_zero**: No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.
- **instances**: No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.

## AKLT.Blueprint.Top.H1FiniteDataStatementV2

- **premises**: This is an EXTERNAL finite-data existence obligation, not a derived fact. It includes GroupInversion, ClearsDenominator and every sector witness at the selected threshold.
- **vacuity_and_degenerate**: Repeated unused exchange signs are permitted. Empty central matrices use Fin 0 and still require positive scales.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: h1Denominator is 1000 or 200; ClearsDenominator includes D0>0. GramResidualRows includes g,d,S>0.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.
