STATUS: PASS
BLOCKING: 0

DECL: goldenRatio PASS

`AKLT/Defs/Moment.lean:24` is exactly the paper's definition of φ in `sec2-moments.tex:10` (Definition `d:moment`): `(1 + √5) / 2`. The declared result type and `Real.sqrt` force all these numerals and arithmetic operations to be real; this is not natural-number division. Mathlib's `Real.sqrt` is the nonnegative square root, extended by zero on negative inputs (`Mathlib/Analysis/Real/Sqrt.lean:109`, `:144`, `:178`). Its argument here is the positive real number 5, so that extension is irrelevant. The denominator is the nonzero real number 2. This fixes the intended positive golden ratio, with no parameter or extra hypothesis.

DECL: icoRadius PASS

`AKLT/Defs/Moment.lean:27` is exactly `r = √(φ + 2)` from `sec2-moments.tex:10`, using the preceding, correct φ. Mathlib's square root selects the nonnegative root, and `Real.sqrt_pos` (`Mathlib/Analysis/Real/Sqrt.lean:286`) makes it strictly positive because φ + 2 > 0. Thus `icoRadius ≠ 0` and `icoRadius² = φ + 2`. This is the paper's actual normalization constant, rather than an unspecified choice of root; the identity is also used at `sec2-moments.tex:56`.

DECL: IcoLetter PASS

This is an auxiliary indexing type for the three groups and the two independent signs in `sec2-moments.tex:12`, with independence explicit at `sec2-moments.tex:16`. `Fin n` consists of the natural numbers strictly below n (`Mathlib/Data/Fin/Basic.lean:18`). The product in `AKLT/Defs/Moment.lean:30` is right-associated: `Fin 3 × (Fin 2 × Fin 2)`, so its projections give one group index and two separately selectable sign indices. The standard product `Fintype` enumerates the full Cartesian product (`Mathlib/Data/Fintype/Prod.lean:42`); `Fintype.card_prod` there at `:56` and `Fintype.card_fin` (`Mathlib/Data/Fintype/Card.lean:497`) give exactly 3·2·2 = 12 labels. There are no restricted sign pairs, extra labels, or finiteness hypotheses. With `icoVector` below this type is bijective with the paper's D, so subsequent sums over labels have the intended multiplicity one.

DECL: signValue PASS

This auxiliary function implements the independent ± choices in `sec2-moments.tex:12` and `:16`. On `Fin 2`, the only inputs are 0 and 1; `AKLT/Defs/Moment.lean:33` sends them respectively to the real numbers +1 and −1. In particular the negation is in ℝ, not modular negation in `Fin 2`. Fin numerals below the bound denote their ordinary bounded natural values (`Mathlib/Data/Fin/Basic.lean:402`), so the equality test at zero selects precisely the positive sign. Both signs occur, neither output is zero, and the two applications in `icoVector` use different product components. The paper imposes no ordering of sign labels, so this choice of which label means + is faithful.

DECL: icoVector PASS

`AKLT/Defs/Moment.lean:36`–`41` enumerates exactly the normalized triples in `sec2-moments.tex:12`. Writing ε and δ for the two independent outputs of `signValue`, group indices 0, 1, and 2 yield respectively `(0, ε, δφ)/r`, `(ε, δφ, 0)/r`, and `(δφ, 0, ε)/r`. The final branch is precisely group 2 because the group index belongs to `Fin 3`. Mathlib's `![x,y,z]` constructs a function `Fin 3 → ℝ` in that coordinate order (`Mathlib/Data/Fin/VecNotation.lean:15`, `:61`, `:74`, `:128`, `:135`); indices 0,1,2 correspond to the paper's first, second, and third coordinates.

The final lambda divides each real coordinate by r, exactly scalar multiplication by 1/r. Real division is totalized (`Mathlib/Algebra/GroupWithZero/Basic.lean:402` gives division by zero as zero), but r is strictly positive as checked above, so no collapse to the zero vector is possible. The identity φ² = φ + 1 gives each unnormalized triple squared Euclidean length `1 + φ² = φ + 2 = r²`, hence normalized squared length one. The Euclidean quantity used here is the explicit `dot`/`normSq` sum in `AKLT/Defs/Moment.lean:12`–`15`; no default norm on function spaces is being substituted. Each vector has exactly one zero coordinate, distinguishing the three groups; within a group the two nonzero coordinate signs distinguish the four labels. Thus all twelve images are distinct, and reversing both signs gives their antipodes, exactly as argued in `sec2-moments.tex:56`–`61`. The codomain `Vec3` does not bundle a unit-length proof, but every value is nevertheless the specified unit vector; no additional values or assumptions are introduced.

Non-blocking remarks:

- Read all of `AKLT/Defs/Moment.lean` and its project import `AKLT/Defs/Geometry.lean`, and inspected the relevant Mathlib meanings and downstream label/vector uses, including `MomentsStatement` in `AKLT/Blueprint/Top/Common.lean:13`. Only the five assigned declarations are judged here. Lean locations are relative to the supplied `lean/` directory, paper locations to `paper/`, and Mathlib locations to the permitted Mathlib source root.
- An exact Python check in the ring ℤ[φ] with φ² = φ + 1 confirmed twelve distinct unnormalized triples, one zero coordinate per triple, squared lengths φ + 2, and antipodal closure. No Lean processes were launched and no inputs were modified.
- These declarations contain no natural-number subtraction, hidden side conditions, or quantified hypotheses whose order or strength could alter the paper's meaning. There are no non-blocking discrepancies to report.
