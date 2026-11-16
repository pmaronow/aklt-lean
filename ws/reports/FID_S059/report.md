STATUS: FAIL
BLOCKING: 1

DECL: BinaryForm PASS

Paper: `sec3-quantum-frames.tex:14–18,25–32` (Definition `d:poly`). The paper's complex vector space of homogeneous binary polynomials is represented faithfully by its ordinary monomial coefficients: `Fin (d + 1) → ℂ` has precisely one coefficient for each integer `0 ≤ j ≤ d`. Under `binaryPolynomial`, these are the coefficients of the distinct monomials `z₁^(d-j) z₂^j`; every homogeneous degree-`d` polynomial has a unique such representation. Zero is included, as required for a vector space. The parameter `d : ℕ` agrees with the paper's nonnegative integer domain; `d = 0` gives one constant coefficient. No finiteness hypothesis or empty index type changes this interpretation. The paper's metric is supplied separately by `binaryNormSq`, rather than by a generic norm on the coefficient function type.

DECL: binaryNormSq PASS

Paper: `sec3-quantum-frames.tex:16–17,27–35`, also `314–326`. Orthogonality of the monomials with squared norms `1 / choose d j` gives exactly `∑ j, |p_j|² / choose d j`. Mathlib's `Complex.normSq` is the real number `re(z)² + im(z)²` (`Mathlib/Basic/Complex/Basic.lean:508–517`), and equals the squared complex norm (`Mathlib/Analysis/Complex/Norm.lean:149`). The denominator is cast to `ℝ` before division, so this is real division, not natural-number division. Since `j : Fin (d + 1)` entails `j.val ≤ d`, `Nat.choose_pos` (`Mathlib/Data/Nat/Choose/Basic.lean:117–120`) makes every denominator strictly positive, including both endpoints and `d = 0`. Thus totalized division by zero cannot erase a coefficient. The sum is over all of the finite index type: Mathlib's `∑ j, ...` means `Finset.sum Finset.univ` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:169–175`). No extra normalization or binomial coefficient is introduced.

DECL: binaryEval PASS

Paper: `sec3-quantum-frames.tex:15–18` for the monomials and evaluation convention, and `274–281,285–296` for their use in the frame evaluation map. Imported `Spinor` is exactly `Fin 2 → ℂ` (`AKLT/Defs/Frame.lean:49–50`), so Lean coordinates `0,1` correspond to paper coordinates `1,2`. The definition evaluates the ordinary monomial expansion with coefficient `p j`, without conjugation or orthonormal-basis scaling. Although subtraction is in `ℕ`, `j.val ≤ d` prevents truncation: the exponents are the intended `d-j` and `j`, summing to `d`. Evaluation is valid on arbitrary complex spinors; the unit-spinor condition belongs to the later frame identities, not to polynomial evaluation itself. Natural powers give exponent-zero factors the value one, including at zero coordinates, as required for polynomial evaluation and the constant case `d = 0`.

DECL: binaryPolynomial PASS

Paper: `sec3-quantum-frames.tex:15–17,27–32`. This auxiliary definition realizes the coefficient representation as the actual polynomial in the paper. Mathlib's `MvPolynomial (Fin 2) ℂ` is the formal commutative polynomial ring with natural-number exponent vectors (`Mathlib/Algebra/MvPolynomial/Basic.lean:80–83`); `C` embeds a scalar as a constant and `X i` is variable `i` (`105–106,125–127`). Consequently each summand is precisely `p_j X₀^(d-j) X₁^j`. The same index bound prevents subtraction underflow, every term is homogeneous of degree `d`, and distinct `j` give distinct exponent vectors. The zero polynomial is allowed. Mathlib's evaluation maps constants and variables to their prescribed values and preserves sums, products and powers (`Mathlib/Algebra/MvPolynomial/Eval.lean:270–297`), so evaluating this polynomial gives `binaryEval d p`. Returning the ambient polynomial ring does not change the object constructed.

DECL: binaryActionPolynomial FAIL

Paper: `sec3-quantum-frames.tex:17–18,25` specifies `(U_g p)(z) = p(g⁻¹z)` with **`g ∈ SU(2)`**; `33–35` explains the resulting unitary action. Lean instead takes an unrestricted `Matrix (Fin 2) (Fin 2) ℂ` (`AKLT/Defs/Polynomial.lean:26–29`), with no special-unitary membership, invertibility hypothesis, or corresponding instance.

The substitution formula itself is correct on the paper's domain. `MvPolynomial.eval₂Hom C f` fixes complex coefficients and replaces `X i` by `f i` (`Mathlib/Algebra/MvPolynomial/Eval.lean:158–163,180–186`). Here that replacement is `∑ j, C (g⁻¹ i j) * X j`, the `i`th coordinate of the inverse acting on a column vector, with no transpose or conjugation error; compare `Mathlib/Data/Matrix/Mul.lean:691–708`.

However, the broader domain admits a degenerate meaning absent from the paper. Mathlib's matrix inverse is explicitly the inverse when invertible and **zero otherwise** (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:168–176`); in particular `Matrix.inv_zero` states `0⁻¹ = 0` (`495–503`). Take `d = 1`, `p 0 = 1`, `p 1 = 0`, and `g = 0`. Then `binaryPolynomial 1 p = X 0`, but `binaryActionPolynomial 1 0 p = 0`, so a form with `binaryNormSq 1 p = 1` is annihilated. This cannot be an element of the paper's unitary group action. Even an invertibility-only restriction would remain broader than the stated domain: `g = 2I` sends this form to `(1/2) X 0`, changing its squared norm to `1/4`.

This is one blocking domain/side-condition mismatch, despite agreement of the formula on `SU(2)`. To state the paper's action exactly, accept `Matrix.specialUnitaryGroup (Fin 2) ℂ` or require special-unitary membership. Mathlib defines that group by unitarity and determinant one (`Mathlib/LinearAlgebra/UnitaryGroup.lean:253–264`). An unrestricted substitution helper can be retained separately, but it does not by itself provide the restricted action of `d:poly`.

Non-blocking remarks:

- Read the whole assigned file and its project import chain: `Frame.lean`, `Moment.lean`, `Geometry.lean`, and `Challenge/Main.lean`. Also checked the consumers in `Blueprint/Top/Quantum.lean` and the associated frame-model definitions. Only the five assigned declarations are judged here.
- `TightStatement` uses `BinaryForm 4`, `binaryEval`, and `binaryNormSq` with explicit unit-spinor/projection hypotheses (`AKLT/Blueprint/Top/Quantum.lean:36–40`), consistent with paper `sec3-quantum-frames.tex:274–283`. It does not accidentally use a generic norm on the coefficient array.
- No other declaration in the supplied Lean tree uses `binaryActionPolynomial`; consequently there is no downstream membership hypothesis that restricts its matrix argument. The failure above concerns that definition's advertised paper action, not a claim that the separate tight-frame interface is false.
- Verification used the supplied Lean and paper sources and the allowed Mathlib sources. No inputs were modified, and no Lean processes were launched.
