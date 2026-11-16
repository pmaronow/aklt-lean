STATUS: PASS
BLOCKING: 0

Scope: reviewed `AKLT/Defs/Frame.lean` in full, its project import chain `Moment.lean` and `Geometry.lean` in full, and the uses of the three assigned declarations. Lean paths below are relative to `/home/ubuntu/aklt/review/FID_S/lean/`; paper paths are relative to `/home/ubuntu/aklt/review/FID_S/paper/`; Mathlib paths are relative to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`.

DECL: pauli PASS

`AKLT/Defs/Frame.lean:53–57` gives exactly the matrices displayed in `sec3-quantum-frames.tex:6–12` and `app-local-operator.tex:234–251` (Definition `d:Pauli`, including its convention σ₀ = I). The four elements of `Fin 4` are 0, 1, 2, 3: the first three branches select I, σ₁, σ₂, and the remaining branch selects σ₃. In particular σ₂ has upper-right entry −i and lower-left entry +i, as in both paper locations.

Checked the potentially consequential Mathlib conventions: `Matrix m n R` has row index first and column index second (`LinearAlgebra/Matrix/Defs.lean:54–58`); `!![a,b;c,d]` constructs rows (not columns), using `Matrix.of` (`LinearAlgebra/Matrix/Notation.lean:83–118`). Matrix `1` is the diagonal identity, not the constant function with value one (`Data/Matrix/Diagonal.lean:219–235`). `Complex.I` is (0,1) (`Basic/Complex/Basic.lean:239–253`), and the entries −1 and −I are complex additive negatives. Thus all sixteen entries across the four matrices have the intended values. The fixed two-dimensional index types are inhabited and finite; there is no empty-matrix or alternative-instance reading.

DECL: spinDensity PASS

`AKLT/Defs/Frame.lean:60–61` implements ρ(a) = (I + a·σ)/2 from `app-local-operator.tex:255` (`d:Pauli`) and the projection formula in `sec3-quantum-frames.tex:19–22,68–73`. Writing x = a 0, y = a 1, z = a 2, its entries are exactly

```text
             [ 1+z    x−iy ]
ρ(a) = 1/2 · [ x+iy    1−z ].
```

The sum is over all three elements of `Fin 3`. The constructed index `⟨k.val + 1, by omega⟩` has natural value 1, 2, or 3, so the coordinates in order select σ₁, σ₂, σ₃, with no wraparound or off-by-one shift. The finite-sum conventions are confirmed by the additive versions of `Fin.prod_univ_two` and `Fin.prod_univ_three` in `Algebra/BigOperators/Fin.lean:110–121`. Real coordinates enter ℂ through `Complex.ofReal`, r ↦ (r,0) (`Basic/Complex/Basic.lean:81–103`). Matrix addition and scalar multiplication operate entrywise (`LinearAlgebra/Matrix/Defs.lean:186–190,297–303`), so both occurrences of `•` have precisely the intended meaning.

The annotation `(1 / 2 : ℂ)` makes this complex field division, not natural-number division; 2 is nonzero. The expression contains no natural subtraction or variable denominator. At a = 0 it gives I/2, as intended. Its trace is one, and its eigenvalues are (1 ± √(x²+y²+z²))/2, matching `app-local-operator.tex:283–288`.

The paper introduces the density for |a| ≤ 1, whereas the Lean matrix-valued formula is total on `Vec3`. This does not assert positivity outside the ball or change the defined matrix on the paper's domain. The relevant positivity statement explicitly assumes `normSq u ≤ 1` (`AKLT/Blueprint/Top/Operator.lean:63–68`); `normSq` is the sum of the three real squares (`AKLT/Defs/Moment.lean:9–15`), hence exactly the paper's condition. The spinor use is on unit frame vectors. `productDensity` uses the same row/column entries factor by factor (`AKLT/Defs/FiniteNetwork.lean:62–65`), so the auxiliary definition supplies the paper's tensor-density factors without a transpose or conjugation change.

DECL: frameSpinor PASS

The counterpart is the finite choice in Definition `d:poly`, `sec3-quantum-frames.tex:19–22`, explained at lines 68–73: choose a unit ζ(a) with ζ(a)ζ(a)* = (I+a·σ)/2, only for the finitely many frame letters. The paper does not prescribe a phase or a closed formula. `AKLT/Defs/Frame.lean:65–69` makes one valid explicit choice for the frozen three frames. Its domain is `Fin 3 × IcoLetter`, with `IcoLetter = Fin 3 × Fin 2 × Fin 2` (`Moment.lean:29–41`): exactly three frames with twelve letters each. This is not a choice on the entire sphere. The three frames are those in `sec3-quantum-frames.tex:341–355`; their disjointness also ensures that choosing by these labels introduces no incompatible duplicate choices.

The vector v used here is the actual Tʲa (`Frame.lean:33–38`). Mathlib matrix multiplication and `mulVec` are the ordinary row-by-column product and action on column vectors (`Data/Matrix/Mul.lean:288–303,691–705`), so the natural exponents j.val = 0,1,2 implement the paper's rotations. The imported icosahedron coordinates agree with `sec2-moments.tex:8–16`. With φ = (1+√5)/2 and r = √(φ+2), one has φ² = φ+1 and r² = 1+φ². Thus every initial vector is unit; 99²+20² = 101² makes T orthogonal, so every v is unit as well. These are facts about the explicit data, not missing hypotheses on the definition.

In fact T fixes the third coordinate, so v 2 belongs to {0, ±1/r, ±φ/r}. Since φ > 1 and r² = 1+φ², all these values lie strictly between −1 and 1. Consequently both square-root arguments in the selected non-pole branch are positive, and √(2(1+v 2)) is nonzero. Mathlib's `Real.sqrt` is the nonnegative square root, returning zero on negative inputs (`Analysis/Real/Sqrt.lean:109–113,142–150,178,268–287`); the latter behavior cannot cause a degenerate value here. Casting its positive real value to ℂ preserves nonzeroness. Although complex division is total with inverse zero defined to be zero (`Basic/Complex/Basic.lean:675–714`), that convention is never used by this denominator.

For an explicit identity check, write v = (x,y,z), d = √(2(1+z)), and t = √((1+z)/2) = d/2. The returned spinor is ζ = (t,(x+iy)/d). Using x²+y²+z² = 1 gives

```text
ζ₀ conjugate(ζ₀) = (1+z)/2
ζ₀ conjugate(ζ₁) = (x−iy)/2
ζ₁ conjugate(ζ₀) = (x+iy)/2
ζ₁ conjugate(ζ₁) = (x²+y²)/(2(1+z)) = (1−z)/2.
```

Thus ζζ* = `spinDensity v`, and |ζ₀|²+|ζ₁|² = 1. The +i sign in the second coordinate is necessary and correct for the paper's σ₂. The pole branch, although unreachable for these particular frames, is also correct: a unit vector with z = −1 has x = y = 0, and (0,1) has outer product diag(0,1) = ρ(v).

`Spinor` is precisely `Fin 2 → ℂ`, and `![a,b]` puts a at coordinate 0 and b at coordinate 1 (`Data/Fin/VecNotation.lean:15–23,52–77,127–140`). The downstream requirement uses the Euclidean sum of squared moduli, not a function-space norm: `TightStatement` expressly requires `∑ k, Complex.normSq (frameSpinor j a k) = 1` and the entrywise outer-product identity (`AKLT/Blueprint/Top/Quantum.lean:32–38`). Mathlib `Complex.normSq` is re²+im², and scalar `star` is complex conjugation (`Basic/Complex/Basic.lean:456–460,500–516`). These match exactly the identities just checked. `frameEval` evaluates physical polynomials at these same spinors (`AKLT/Defs/FrameModel.lean:77–80`), as required by `sec3-quantum-frames.tex:279–282`. Fixing this permitted phase adds no restriction on the paper's phase-independent norm identities (`sec3-quantum-frames.tex:71–73`).

Non-blocking remarks: no correction is needed. The total domain of `spinDensity` and the particular phase chosen by `frameSpinor` are harmless implementation choices for their stated uses. All relevant finite domains have their fixed standard instances; none of these declarations depends on an empty domain, truncated natural subtraction, or a zero denominator. Quantified compatibility assumptions for arbitrary other frames remain explicit in `TightStatement`; the concrete frozen choices satisfy their identities directly.

Validation: besides the source comparison and algebra above, a small Python check using exact rational arithmetic in ℚ(√5) verified the rotation identity and the squared norms and nonzero planar parts of all 36 frame vectors. An independent 80-digit decimal evaluation checked all 36 spinor normalization and projection identities, with maximum residuals 1.7×10⁻⁷⁹ and 1.5×10⁻⁷⁹ respectively. These numerical checks supplement the algebraic argument; they are not a Lean proof. No Lean processes were launched, and no inputs were modified.
