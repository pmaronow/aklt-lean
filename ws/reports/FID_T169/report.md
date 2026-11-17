STATUS: PASS
BLOCKING: 0

DECL: binaryInverseSubstitutionPolynomial PASS

This is an auxiliary definition for the action in Definition `d:poly`, paper `sec3-quantum-frames.tex:14–25`. The paper prescribes `(U_g p)(z) = p(g^{-1}z)` and explicitly restricts `g` to SU(2) at line 25. The helper itself is correctly documented as an inverse-substitution operation on arbitrary complex matrices, rather than as the paper's action. Its sole substantive use is by `binaryActionPolynomial`, which imposes precisely that restriction (`AKLT/Defs/Polynomial.lean:25–36`).

The input array represents the polynomial

    P_p(X₀,X₁) = Σ_{j=0}^d p_j X₀^(d-j) X₁^j.

`BinaryForm d = Fin (d+1) → ℂ` and `binaryPolynomial` (`Polynomial.lean:9–23`) give every ordinary monomial coefficient independently. For every index, `j.val < d+1`, hence `j.val ≤ d`; natural subtraction `d - j.val` therefore has its intended value. The exponent pairs are distinct and sum to `d`. This represents exactly all homogeneous degree-d binary forms, including the zero form. Lean variable indices 0 and 1 correspond to the paper's `z_1` and `z_2`. No binomial normalization is inserted into the coefficients.

Mathlib's `MvPolynomial` is a formal polynomial ring, not a quotient of polynomial functions (`Mathlib/Algebra/MvPolynomial/Basic.lean:55–61,80–83`); `C` embeds a constant and `X i` is the degree-one variable (`Basic.lean:104–106,125–127`). `eval₂Hom C L` fixes coefficients and replaces each variable `X i` by `L i`, preserving sums, products and powers (`Mathlib/Algebra/MvPolynomial/Eval.lean:150–163,180–186`). Here `L i = Σ_j C ((g⁻¹) i j) * X j`. Consequently, evaluation at any spinor `z` gives exactly `binaryEval d p ((g⁻¹).mulVec z)`. The matrix-vector convention is column-vector multiplication, `(A.mulVec z) i = Σ_j A i j * z j` (`Mathlib/Data/Matrix/Mul.lean:691–708`). Thus neither the matrix indices nor the substitution direction are transposed, and the polynomial coefficients and variables are not conjugated.

The inverse is Mathlib's matrix inverse, defined by inverse determinant times adjugate, rather than entrywise reciprocal (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:168–179`). It is a two-sided inverse whenever the determinant is a unit (`NonsingularInverse.lean:209–219`). For a singular complex matrix it is zero (`NonsingularInverse.lean:175–176`), so the helper has a total extension outside the paper's domain. This causes no mismatch in its actual use: its caller supplies a matrix of determinant one. No invertibility instance or additional hypothesis is silently required.

DECL: binaryActionPolynomial PASS

The matching definition is `d:poly`, paper `sec3-quantum-frames.tex:14–25`: arbitrary nonnegative integer degree, ordinary monomial coordinates, action `p(z) ↦ p(g^{-1}z)`, and `g ∈ SU(2)`. Lean takes exactly `d : ℕ`, an arbitrary `p : BinaryForm d`, and `g : Matrix.specialUnitaryGroup (Fin 2) ℂ` (`AKLT/Defs/Polynomial.lean:32–36`).

Mathlib defines `specialUnitaryGroup` as the intersection of the unitary matrices and the determinant-one kernel; membership is exactly unitarity together with `det = 1` (`Mathlib/LinearAlgebra/UnitaryGroup.lean:253–264`). Unitarity means `star A * A = 1` and `A * star A = 1` (`Mathlib/Algebra/Star/Unitary.lean:57–66`). Matrix star is conjugate transpose (`Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:409–418`), and complex star is ordinary complex conjugation (`Mathlib/Basic/Complex/Basic.lean:456–460,499–501`). This is precisely the usual complex SU(2), with no omitted or added condition. The Mathlib comment concerning invertibility of 2 causes no restriction over ℂ.

The coercion to `Matrix (Fin 2) (Fin 2) ℂ` retains the underlying matrix. Its determinant remains one, so the helper's matrix inverse is the genuine inverse (equivalently the conjugate transpose), and the singular branch is impossible. Applying the helper expansion above gives exactly the paper's formula for every spinor. As an explicit sign check, for `g = [[0,1],[-1,0]]`, the inverse substitution is `(z₁,z₂) ↦ (-z₂,z₁)`, hence `z₁^(d-j)z₂^j ↦ (-z₂)^(d-j)z₁^j`. The diagonal matrix in `sec3-quantum-frames.tex:38–40` likewise gives the stated multiplier `exp(i t (j-d/2))`.

There are no hidden positivity, nonzero-form, positive-degree or frame assumptions. All sums are over the fixed finite types `Fin 2` and `Fin (d+1)`, with their ordinary finite instances; no empty or arbitrary support choice is involved. At `d = 0` the result is the unchanged constant, as required by the paper's degree-zero case (`sec3-quantum-frames.tex:63`). For every degree, the linear substitution preserves homogeneous degree, with the zero polynomial allowed. Returning an ambient `MvPolynomial` rather than a coefficient array loses no constraint: the defining expression already produces precisely the required homogeneous polynomial. The action also has the intended order: `U_g(U_h p)(z) = p(h⁻¹g⁻¹z) = U_(gh)p(z)`.

Non-blocking remarks: No correction is needed. The unrestricted helper's singular-matrix extension is intentional and does not enlarge the domain of the paper-facing action. I read the entire `Polynomial.lean` file and its project import closure (`Frame.lean`, `Moment.lean`, `Geometry.lean`, and `Challenge/Main.lean`), and searched the supplied Lean sources for uses of both declarations. This review used source-level expansion and Mathlib definitions; no Lean compilation was run, and no input was modified.
