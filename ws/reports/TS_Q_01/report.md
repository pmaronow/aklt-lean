STATUS: COMPLETE

| Leaf (namespace `AKLT.Blueprint.Q`) | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| [OrthogonalFamilyStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesFrames.lean:25) | TRUE | easy | `RᵀR=I` supplies a left inverse, preserves the stated squared norm, and preserves antipodal witnesses. |
| [OneSiteMomentEncodingStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesFrames.lean:36) | TRUE | medium | A single variable rename works for every matrix `R`; the singleton U product functional is exactly the twelve-label average. |
| [IcoDistanceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesFrames.lean:50) | TRUE | medium | The distinct-pair squared distances are `4` and `2 ± 2/√5`, all strictly greater than one. |
| [RotationDisplacementStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesFrames.lean:55) | TRUE | easy | For `k=1,2`, the planar squared-displacement coefficients are `4/101` and `1600/10201`. |
| [SelfRotationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesFrames.lean:61) | TRUE | medium | The minimum planar squared length is `1/(φ+2)`; the specified positive-sign label attains `frameBound` at `k=1`. |
| [DisplacedDistanceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesFrames.lean:68) | TRUE | medium | The Euclidean triangle estimate gives `1-dot u w > 3721/20402 > 9/50`. |
| [RelativeRotationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesFrames.lean:76) | TRUE | easy | Cancel the smaller common power; when the index order reverses, exchange the two labels. |
| [SpinorChoiceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/NodesTight.lean:12) | TRUE | medium | The south-pole branch and the positive-denominator north chart both satisfy the exact Pauli density and unit norm. |

All eight statements are self-sufficient. No missing premise, counterexample, unintended vacuity, or statement correction was found. The full Lean names, reasons, fixes, and two-line proof routes are recorded in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_Q_01/verdicts.jsonl).

The repository inspected was `/home/ubuntu/aklt/repo`, branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The mathematical comparison used the local manuscript: [the three-frame lemma and its proof](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:341), [the spinor convention and existence argument](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:14), and [the moment definitions and identities](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:8). No repository files were modified and no leaf proofs were written.

**Definitions traced.** The full application-specific dependency closure of these leaves is:

| Source | Relevant definitions read |
| --- | --- |
| [Defs/Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8) | `Vec3`, `dot`, `normSq`, `goldenRatio`, `icoRadius`, `IcoLetter`, `signValue`, `icoVector`, `moment`, `Status`, `SpinLetter`, `spinVector`, `spinWeight`, `DegreeFour`, `SeparateDegreeFour`, `productFunctional`. |
| [Defs/Frame.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Frame.lean:32) | `frameRotation`, `frameVector`, `frameBound`, `Spinor`, `pauli`, `spinDensity`. |
| [Q/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Q/Definitions.lean:12) | `compatible`, `chosenSpinor`. |

The underlying Mathlib definitions of matrix transpose and `mulVec`, multivariate-polynomial evaluation, renaming and total degree, and `Complex.normSq` were also checked. The eight leaves contain no additional mathematical typeclass premises. `productFunctional`'s `Fintype` instance is instantiated at `Fin 1`; it has not disappeared from a generic quantifier. Facts about the fixed matrix or fixed ico vectors can be established from their definitions; they do not require another unproved blueprint leaf as a premise.

**OrthogonalFamilyStatement.** The matrix hypothesis gives `Rᵀ(Rx)=x` and `dot (Rx) (Ry)=dot x y`. Its determinant need not be one. The supplied injectivity, unit-length equations, and antipodal partners therefore suffice. The hypotheses are consistent: take the identity matrix and the explicitly defined ico family.

Route, line 1: use the left inverse to transfer injectivity and expand the dot-product preservation identity.
Route, line 2: specialize to equal vectors for `normSq`, and send each supplied antipodal partner through `mulVec_neg`.

**OneSiteMomentEncodingStatement.** Choose `q = MvPolynomial.rename (fun k : Fin 3 => ((0 : Fin 1), k)) p`. Its monomial degree at the only site is its total degree, at most four. The domain of the one-site sum has thirteen configurations: twelve `some` ico labels with weight `1/12`, and `none` with weight zero. This is exactly `moment`, even after substitution by an arbitrary matrix. The same `q` works for every `R`, including singular matrices. The statement asserts an encoding identity; it does not equate rotated and unrotated moments. The zero polynomial and constants cause no degree exception.

Route, line 1: transport the total-degree bound through the rename and identify total degree with the sole site's degree.
Route, line 2: apply `eval_rename`, collapse the singleton function domain, and expand the U weights in both equalities.

**IcoDistanceStatement.** The exact enumeration of all 132 ordered distinct-label pairs gives 60 distances `2-2/√5`, 60 distances `2+2/√5`, and 12 distances `4`. The minimum exceeds one since `√5>2`. This uses the actual independent signs and the positive normalizing radius `r=√(φ+2)`; no hidden injectivity or unit-length premise is needed.

Route, line 1: split the three coordinate families and independent signs, using `φ²=φ+1` and `r²=φ+2>0`.
Route, line 2: reduce the squared distances to the three values above and use `√5>2`.

**RotationDisplacementStatement.** The natural bounds restrict `k` to exactly 1 or 2. With `T=frameRotation`, direct multiplication gives `(Tᵏ-I)ᵀ(Tᵏ-I)=diag(cₖ,cₖ,0)`, where `c₁=4/101` and `c₂=1600/10201=(40/101)²`. The unit equation bounds the planar squared length by one. The second bound is attained, for example at `(1,0,0)`.

Route, line 1: split the two exponents and expand the explicit matrix and three-coordinate squared norm.
Route, line 2: use `v₀²+v₁²=1-v₂²≤1` and compare the rational coefficients.

**SelfRotationStatement.** For a unit ico vector `u`, the loss equals `δₖ(u₀²+u₁²)`, with `δ₁=2/101` and `δ₂=800/10201≥δ₁`. In coordinate-family order, the planar squared lengths are `1/(φ+2)`, `1`, and `φ²/(φ+2)`. Their minimum is the first. Rationalization gives `2/(101(φ+2))=(5-√5)/505`. The nested label `(0,0,0)` means the first family with both signs positive, hence exactly `(0,1,φ)/r`; frames 0 and 1 at that label attain the claimed equality.

Route, line 1: compute the loss for the two exponents and three coordinate families, then bound the planar squared length below.
Route, line 2: rationalize the resulting minimum to `frameBound` and evaluate the specified witness.

**DisplacedDistanceStatement.** In the Euclidean geometry defined by `dot`, the input separation and displacement imply `|u-w|>1-40/101=61/101`. Since `u,w` are unit, half its square is `1-dot u w`; the margin over `9/50` is strictly greater than `608/255025`. All hypotheses can hold together, for example `u=(1,0,0)` and `v=w=(-1,0,0)`. An entirely coordinate-based route avoids converting between norm APIs.

Route, line 1: sum the nonnegative squares `(2(uᵢ-wᵢ)-3(wᵢ-vᵢ))²` to obtain `6 normSq(u-v)≤10 normSq(u-w)+15 normSq(w-v)`.
Route, line 2: a failure of the conclusion gives `normSq(u-w)≤9/25`; inserting both bounds makes the right side less than 6, contradicting `normSq(u-v)>1`.

**RelativeRotationStatement.** For `i.val<j.val`, choose `k=j.val-i.val` and `(u,v)=(a,b)`. For the reverse order choose `k=i.val-j.val` and `(u,v)=(b,a)`. Dot-product symmetry and cancellation of the smaller common power give the equality. The six ordered unequal frame-index pairs all yield `k=1` or `k=2`. Orthogonality follows by exact rational arithmetic on `T` and is also already proved by `rotation` in the source module.

Route, line 1: establish `TᵀT=I` and dot-product preservation for its powers.
Route, line 2: order the indices, exchange dot factors if needed, and choose the positive difference and corresponding labels.

**SpinorChoiceStatement.** Write `v=(x,y,z)`. The unit premise gives `-1≤z≤1`. At `z=-1` it forces `x=y=0`, and the chosen spinor `(0,1)` is correct. Otherwise `1+z>0`; putting `t=√(2(1+z))>0`, the chosen formula becomes `(t/2,(x+iy)/t)`. Its density is `[[1+z,x-iy],[x+iy,1-z]]/2`, with exactly the signs of the defined Pauli matrices, and its real sum of complex squared norms is one. The universal choice is allowed to be discontinuous; the paper's finite choice does not demand a continuous section of the sphere.

Route, line 1: split the pole and establish positive square roots, their factor-of-two relation, and nonzero complex denominators off the pole.
Route, line 2: expand `compatible` and the Pauli matrices entrywise, using `x²+y²=1-z²` and the square-root equations.

**Lean traps and boundary checks.**

- `Vec3` is `Fin 3 → ℝ`. Its default function-space norm is the sup norm, whereas `AKLT.Defs.normSq` is the sum of three squares. In particular, the displacement and triangle calculations must use `normSq` directly or explicitly move to `EuclideanSpace ℝ (Fin 3)` via `WithLp.toLp 2`. An unqualified use of `norm_sub_le` on `Vec3` would use the wrong norm.
- All geometric divisions are real divisions. Explicit elaboration confirmed that `9/50` and `40/101` in the metric statement are in `ℝ`; none is natural-number division. The frame matrix entries likewise have type `ℝ`. The squares and matrix powers have natural exponents.
- The two sign factors of `IcoLetter = Fin 3 × (Fin 2 × Fin 2)` are independent. Access them as `.2.1` and `.2.2`. Sums in `moment` use the twelve labels, not the image finset `icoSet`; no deduplication occurs. Finite index instances are available and nonempty.
- `productFunctional` sums over the entire function type `Fin 1 → Option IcoLetter`, including its zero-weight atom. Reindex this sum using the singleton-domain equivalence; it is not definitionally a sum over `IcoLetter`. `SeparateDegreeFour` is a bound on the sum of three coordinate exponents at each site, not a separate bound on each individual coordinate.
- Use classical decidability for polynomial support/reindexing and for reasoning about real equality. The definitions already make the required classical choices. No extra mathematical assumption is needed.
- In `RelativeRotationStatement`, make the index-order split before subtracting natural values. For reverse order, swap the labels. `Fin` disequality transfers to value disequality by injectivity; natural subtraction without the ordering would truncate.
- For `SpinorChoiceStatement`, `Real.sqrt` is real before casting to `ℂ`; justify nonnegativity and nonzero denominators before division simplification. `compatible` mixes a real norm equation with a complex matrix equation, and uses `z k * star (z l)`, so off-diagonal conjugation signs matter. At the south pole, establish the vanishing transverse coordinates before using the branch.

**Verification evidence.** The inspection-only [Lean module](/home/ubuntu/aklt/reports/TS_Q_01/scratch/Inspect.lean) ran successfully with Lean `4.35.0-rc2`, importing the existing built repository modules through a local packages symlink. It printed all eight elaborated propositions, checked the encoding candidate and relevant APIs, and confirmed cardinalities 12, 13, and 13 for `IcoLetter`, `SpinLetter`, and the one-site configuration type. Its [output](/home/ubuntu/aklt/reports/TS_Q_01/scratch/lean_inspection.txt) contains no errors or warnings. Only one Lean process was used; no repository module was rebuilt.

The exact-arithmetic [Python diagnostics](/home/ubuntu/aklt/reports/TS_Q_01/scratch/symbolic_checks.py), using SymPy 1.14.0 in `/tmp/ts_q_01_sympy`, checked all 132 distinct-label distances, 24 self-rotation losses and the equality witness, the two displacement matrices, all six relative-rotation matrix identities, the strict rational distance margin, and both spinor branches. The north-chart density and norm residuals reduced exactly to zero modulo the unit and square-root equations. All checks passed; their [JSON output](/home/ubuntu/aklt/reports/TS_Q_01/scratch/symbolic_checks.json) is retained. The verdicts rely on the mathematical routes above, with these checks supplying additional evidence; no completed Lean leaf proofs are claimed.
