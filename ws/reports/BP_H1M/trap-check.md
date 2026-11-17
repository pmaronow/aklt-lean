# Per-node trap audit

All 67 statement definitions are checked as closed `Prop`s in `AKLT.Blueprint.H1.Audit`.
Every open node has the seven detailed trap categories in `leaves.json`; this file also records immediate and assembled nodes.

## H1FiniteDataStatementV2

Status: external input. Paper: `t:H1 / p:certificate`.

- **premises**: This is an EXTERNAL finite-data existence obligation, not a derived fact. It includes GroupInversion, ClearsDenominator and every sector witness at the selected threshold.
- **vacuity_and_degenerate**: Repeated unused exchange signs are permitted. Empty central matrices use Fin 0 and still require positive scales.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: h1Denominator is 1000 or 200; ClearsDenominator includes D0>0. GramResidualRows includes g,d,S>0.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## CertificateStatementV2

Status: package. Paper: `t:H1 / p:certificate`.

- **premises**: A definition packaging soundness AND finite data coverage. No theorem asserts either conjunct without its explicit input.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ThresholdSymmetryStatement

Status: assembled. Paper: `l:integercheck`.

- **premises**: Kernel-checked implication `thresholdSymmetry_of_integerCheck` assembles this intermediate from closed inputs. It is not another independent open obligation.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## CoveredSlotEnumerationStatement

Status: open. Paper: `l:leaf`.

- **premises**: Nonremovedness is required for corners. All tips are U by Covered. Both corner slots are retained regardless of kept external half-bonds.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## CornerMeanBoundsStatement

Status: open. Paper: `l:leaf`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Normalizer positivity is part of the conclusion and must be established before any division in localMean is cleared.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## NormalizedMeanFactorStatement

Status: open. Paper: `l:leaf`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: A=siteFunctional s(localProduct a)>0 and rho>0 are explicit premises. The zero-mean case gives u=0 and causes no division by its norm.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PassageSiteMomentsStatement

Status: open. Paper: `l:Iw`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PassageFubiniStatement

Status: open. Paper: `l:Iw`.

- **premises**: Coveredness, exact neighbour set equality and all three distinctness conditions are explicit. Removed-site vectors are zero, never additional spin variables.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PassageNetworkPositiveStatement

Status: open. Paper: `l:Iw`.

- **premises**: The supplied generic network result includes Valid; the proof must build a valid erased network retaining every original slot.
- **vacuity_and_degenerate**: The template has a passage site, but its erased network can have isolated sites; finite-network input covers n=0 as well.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PassageNextLowerBoundStatement

Status: open. Paper: `l:Iw`.

- **premises**: Unit norms of the concrete atoms are explicit; zero-weight atoms are allowed. Dot-product lower bounds are needed only where the spin weights are nonzero.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PassageSubtractionStatement

Status: proved. Paper: `l:Iw`.

- **premises**: Kernel-checked theorem `passageSubtraction` proves this closed node; see axioms.txt.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## OriginalDegreeStatement

Status: open. Paper: `l:Iw`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## OriginalFactorStructureStatement

Status: open. Paper: `l:Iw`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## OriginalRawEvaluationStatement

Status: open. Paper: `l:Iw`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## MomentContractionStatement

Status: open. Paper: `l:moments / l:Iw / c:reduce`.

- **premises**: Both absent-spin support and separate degree <=4 are mandatory. rationalMoment is not exact for arbitrary higher-degree monomials.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## MomentCovarianceTransferStatement

Status: open. Paper: `l:moments / l:Iw / c:reduce`.

- **premises**: Uses the supplied degree-four polynomial covariance, support, status and integrand invariance; does not rotate the finite atom set as a set.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ContractionAffineStatement

Status: open. Paper: `l:moments / l:Iw / c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ContractionSupportStatement

Status: open. Paper: `l:moments / l:Iw / c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ActiveStatusesStatement

Status: proved. Paper: `l:Iw`.

- **premises**: Kernel-checked theorem `activeStatuses` proves this closed node; see axioms.txt.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## BlochAlgebraStatement

Status: open. Paper: `l:inversion`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## BlochPositivityStatement

Status: open. Paper: `l:inversion`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: r=0 is included; no invertibility or nonzero A is assumed.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: The eigenvalue-square argument uses no division by r or sqrt r.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## SinglePauliTraceStatement

Status: proved. Paper: `l:inversion`.

- **premises**: Kernel-checked theorem `singlePauliTrace` proves this closed node; see axioms.txt.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PauliExpansionStatement

Status: open. Paper: `l:inversion`.

- **premises**: VectorAffine bounds the sum of the three coordinate exponents per token; scalar-coordinate multiaffineness would be insufficient. SupportedVectors excludes unrepresented tokens.
- **vacuity_and_degenerate**: For J empty the function type J->Fin4 is a singleton, yielding the constant term.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: pauliCoordinate uses a.val-1 only under a.val != 0; the Fin 4 bound proves this index is <3.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PauliProductTraceStatement

Status: open. Paper: `l:inversion`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## InversionPolynomialStatement

Status: open. Paper: `l:inversion`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ProductDensityPositiveStatement

Status: open. Paper: `l:inversion`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: For J empty there is one tensor basis function, not zero basis functions; the resulting matrix is [1].
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## TraceProductPositiveStatement

Status: open. Paper: `l:inversion`.

- **premises**: Both factors are PSD; no commutation or positive-definiteness premise is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: The arbitrary index type explicitly binds [Fintype n] and [DecidableEq n]; the conclusion uses those instances.

## InversionBallStatement

Status: proved. Paper: `l:inversion`.

- **premises**: Kernel-checked theorem `inversionBall` proves this closed node; see axioms.txt.
- **vacuity_and_degenerate**: Negation preserves normSq even at zero; membership in I is split explicitly.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ReducedDegreeStatement

Status: open. Paper: `c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ReducedFactorStructureStatement

Status: open. Paper: `c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PeripheralGeometryStatement

Status: open. Paper: `c:reduce`.

- **premises**: Requires Covered and both exact deletion rules; degree and neighbour statements refer to the original current internal bonds.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PeripheralFubiniStatement

Status: open. Paper: `c:reduce`.

- **premises**: Requires PeripheralGeometry. Deleted spins are mutually nonadjacent; next changes no deleted leaf law or bond, since none is a passage neighbour.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PeripheralAssignmentStatement

Status: open. Paper: `c:reduce`.

- **premises**: Concrete atom unit norms, LeafRule and PeripheralGeometry are explicit. A single choice of K and u precedes the next quantifier.
- **vacuity_and_degenerate**: If no leaf is deleted, K=1. Isolated leaves supply a positive factor; unused tokens are zero.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## SimultaneousLeafReconstructionStatement

Status: assembled. Paper: `c:reduce`.

- **premises**: Kernel-checked implication `simultaneousLeafReconstruction_of_nodes` assembles this intermediate from closed inputs. It is not another independent open obligation.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## BallChordStatement

Status: open. Paper: `c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Branch on v=0. Only the nonzero branch divides by norm v; the zero branch uses an explicit unit coordinate vector.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## AffineEvaluationStatement

Status: open. Paper: `c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ProductBallNonnegativeStatement

Status: open. Paper: `c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Zero convex weights are valid. The ambient 20-token function also represents constants and polynomials with no used tokens.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## DifferenceStructureStatement

Status: open. Paper: `c:reduce`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ReducedStructureStatement

Status: assembled. Paper: `c:reduce`.

- **premises**: Kernel-checked implication `reducedStructure_of_nodes` assembles this intermediate from closed inputs. It is not another independent open obligation.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## DifferenceEvaluationStatement

Status: proved. Paper: `c:reduce`.

- **premises**: Kernel-checked theorem `differenceEvaluation` proves this closed node; see axioms.txt.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## SectorSpinStableStatement

Status: open. Paper: `l:sector`.

- **premises**: No Covered assumption is needed: coordinate groups are always disjoint. Unused signs may repeat the same subspace; this does not claim an orthogonal sum over all signs.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## SectorWeightBasisStatement

Status: open. Paper: `l:sector`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: exchangeWeight and centralWeight are rational; the Z eigenvalue is complex and the integer-offset equality is real. The central half depends on the number of single groups.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## SpanWeightLatticeStatement

Status: open. Paper: `l:sector`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: For an empty spanning family the span is zero, so the nonzero eigenvector premise is impossible. No linear independence is assumed.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: The arbitrary basis-index type explicitly binds [Fintype beta].

## SpinAdjointStatement

Status: open. Paper: `l:sector`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## SpinCommutatorStatement

Status: open. Paper: `l:sector`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## WeightLadderTransferStatement

Status: open. Paper: `l:sector`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## CommonWeightEigenvectorStatement

Status: open. Paper: `l:sector`.

- **premises**: O and Z preserve S; both restricted symmetry conditions and O/Z commutation on S are explicit. The O eigenspace is nonzero by eigenvaluesOn membership.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## LadderWalkStatement

Status: open. Paper: `l:sector`.

- **premises**: kappa is exactly 0 or 1/2, spin stability and nonvanishing/shift facts are explicit. O commutes with both ladders on S. No multiplicity claim is made.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: Distances are integer offsets. Split the sign before converting a distance to Nat; never truncate m-kappa as a natural subtraction.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PositiveSpectrumStatement

Status: open. Paper: `l:sector`.

- **premises**: Restriction invariance and symmetry on S are explicit; the inherited inner product is used, not the unnormalized coordinate dot product.
- **vacuity_and_degenerate**: S=0 makes PositiveOn and the universal eigenvalue condition both vacuously true.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## CentralWeightHalfStatement

Status: proved. Paper: `l:sector`.

- **premises**: Kernel-checked theorem `centralWeightHalf` proves this closed node; see axioms.txt.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PauliHermitianStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## ReflectionParityStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PauliRealityStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## InversionCovarianceStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## AdjointPauliCoordinatesStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## AdjointPauliOrthogonalStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: The Pauli-coordinate equation and g-adjoint*g=1 are explicit. Square finite dimension supplies g*g-adjoint=1 when needed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PauliRotationTransferStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## CayleyTensorCommutationStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: sqrt(1+t squared)>0 for all real t; its finite tensor scalar power is nonzero, including exponent zero.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## TensorLinearCoefficientStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: For J empty the tensor polynomial is constant and its linear coefficient and token sum are both zero.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## SpinGeneratorTransferStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## MomentPauliInterchangeStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: Requires exact monomial moments, U/D statuses on V, internal support and degree four. External affineness is unnecessary because both sides select the same Pauli exponents.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PairExpansionFromRealizationStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: GroupInversion forces equal signs on the two retained slots. Unit atom norms are explicit; zero-weight U atoms must be omitted.
- **vacuity_and_degenerate**: The finite expansion may be empty only for the zero operator; D allows n=0.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## RetainedPairExpansionStatement

Status: assembled. Paper: `l:Ostruct`.

- **premises**: Kernel-checked implication `retainedPairExpansion_of_nodes` assembles this intermediate from closed inputs. It is not another independent open obligation.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## UnitPairSupportStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: j != k, normSq n=1 and eta squared=1 are explicit. Rank-one support would be false for a zero Bloch vector.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## EqualPairExchangeStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: All local mathematical premises are explicit in this closed definition; no other leaf proposition is assumed.
- **vacuity_and_degenerate**: n=0 and even j=k are included: equal-factor exchange still commutes.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PairExpansionTransferStatement

Status: open. Paper: `l:Ostruct`.

- **premises**: The remainder commutes with both exchange and the projection as explicit parts of PairExpansion. No positivity of complex coefficients is assumed.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No unguarded natural subtraction in this statement.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.

## PairTokensDistinctStatement

Status: proved. Paper: `l:Ostruct`.

- **premises**: Kernel-checked theorem `pairTokensDistinct` proves this closed node; see axioms.txt.
- **vacuity_and_degenerate**: Finite empty products and sums use their usual identities. Nonzero premises are present precisely at eigenvector or norm-positivity steps.
- **coercions**: Keep rational coefficients, real vector entries and complex matrix entries distinct; casts are ring homomorphisms, not floating-point conversions.
- **finite_sums**: Finset sums are used for polynomial support/sites; Fintype sums are used for assignments and tensor functions. Reindex via an explicit equivalence.
- **nat_subtraction**: No subtraction: groupLeader<=17 and groupSecond=min 19 (leader+1); omega proves equality is impossible, so the min does not identify slots.
- **division_by_zero**: Only positive fixed denominators occur unless a separately stated positive-normalizer hypothesis is used.
- **instances**: No section variables. Finite token subtypes carry their Fintype instances; arbitrary finite types explicitly bind Fintype/DecidableEq when needed.
