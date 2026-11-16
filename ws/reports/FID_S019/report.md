STATUS: PASS
BLOCKING: 0

DECL: tokenMatrix PASS

This is the correct auxiliary realization of the one-factor operator denoted by a superscript `(i)` in `paper/app-local-operator.tex:256–257` (Definition `d:Pauli`), in the tensor coordinates of the Pauli expansion at lines 249–251. Its entry is exactly
`A (σ j) (τ j) * ∏ k ≠ j, δ(σ k, τ k)`:
the condition tests agreement at every other token, and deliberately imposes no agreement at `j`. Thus it places `A` at that factor and identities at all other factors, including the correct off-diagonal entries.

The coercion of a finset `J` to a type is its membership subtype, so `j : J` is an actual selected token, and `J → Fin 2` indexes all binary tensor basis states. Membership proofs do not create extra tokens. I checked `Mathlib/Data/Finset/Defs.lean:157–181`, `Mathlib/Data/Fintype/Sets.lean:226–231`, and `Mathlib/Data/Fintype/Pi.lean:134–136`: the sums and matrix coordinates use all elements of the finite types. In particular unused labels from `Fin 20` add no tensor factors. The finite label set accommodates every group from Definition `d:reduction` (`paper/app-local-operator.tex:146–157`). For a singleton `J` the agreement condition is vacuous and the matrix is exactly `A`; an empty `J` has no possible argument `j`, as intended.

DECL: totalSpinZ PASS

This is exactly `S_z = (1/2) ∑ᵢ σ₃⁽ⁱ⁾` in `paper/app-local-operator.tex:256`. `lean/AKLT/Defs/Frame.lean:53–57` gives `pauli 3 = diag(1,-1)`, so coordinate `0` is `e_+`, coordinate `1` is `e_-`, and a binary state has magnetic weight `|J|/2 - #{j : σ j = 1}`. These signs agree with the single and pair weights at `paper/app-local-operator.tex:450–458`.

I checked `Mathlib/Analysis/InnerProductSpace/PiL2.lean:114–115,1242–1243`, `Mathlib/Analysis/Normed/Lp/Matrix.lean:30–45`, and `Mathlib/Data/Matrix/Mul.lean:698–708`. `Matrix.toEuclideanLin` acts by ordinary matrix multiplication on column coordinates, with output at `σ` equal to `∑ τ, M σ τ * ψ τ`; it introduces no transpose, conjugation, or basis rescaling. `EuclideanSpace ℂ (J → Fin 2)` has the usual tensor-coordinate Hermitian inner product, a sum of coordinate inner products (`PiL2.lean:84–105`). The coefficient `1 / 2` is complex field division by the nonzero scalar two. There is no natural-number division or subtraction and no volume normalization. For empty `J` the state index has one element, the Hilbert space is `ℂ`, and the operator is zero, matching `paper/app-local-operator.tex:16–18,374`.

DECL: totalSpinPlus PASS

This is exactly `S_+ = ∑ᵢ (σ₁⁽ⁱ⁾ + i σ₂⁽ⁱ⁾)/2` in `paper/app-local-operator.tex:257`. The matrices at `lean/AKLT/Defs/Frame.lean:55–56` match the explicit paper matrices at `paper/app-local-operator.tex:236–238`. Consequently `(σ₁ + iσ₂)/2` is `[[0,1],[0,0]]`: it sends `e_-` to `e_+` and kills `e_+`, with the raising sign specified at paper line 458. On an unnormalized symmetric pair it sends `v_-` to `v₀` and `v₀` to `2v_+`, and kills the exterior vector, exactly as at paper lines 453–456.

The lift is linear in its matrix argument, so the scalar outside the finite sum gives precisely the paper's per-factor division by two. Matrix addition and complex scalar multiplication are entrywise. The column action and usual Hilbert coordinates are those checked for `totalSpinZ` in `Mathlib/Analysis/Normed/Lp/Matrix.lean:44–45` and `Mathlib/Analysis/InnerProductSpace/PiL2.lean:84–115,1242–1243`. No adjoint reverses the ladder. The denominator is the fixed nonzero complex number two, and the empty sum is the intended zero operator (paper line 374).

DECL: totalSpinMinus PASS

This is exactly `S_- = ∑ᵢ (σ₁⁽ⁱ⁾ - i σ₂⁽ⁱ⁾)/2` in `paper/app-local-operator.tex:257`. With the same explicit Pauli convention, its one-factor matrix is `[[0,0],[1,0]]`. Thus it sends `e_+` to `e_-` and kills `e_-`; on a symmetric pair it sends `v_+` to `v₀` and `v₀` to `2v_-`, and kills the exterior vector. These are precisely the actions at `paper/app-local-operator.tex:453–459`, including the factors two caused by the unnormalized pair basis.

The checked Mathlib meanings are ordinary column multiplication (`Mathlib/Analysis/Normed/Lp/Matrix.lean:44–45`, `Mathlib/Data/Matrix/Mul.lean:707–708`) and the standard coordinate inner product (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:84–115`). In particular this operator is the adjoint of `totalSpinPlus` in the intended metric, consistent with paper line 464. Scalar placement, fixed nonzero denominator, finite indexing, and the empty-sum convention all agree with the paper.

DECL: centralSpace PASS

This is exactly `V_ε° = ker(S_z - κ I)|V_ε` in Definition `d:exchange`, `paper/app-local-operator.tex:416–429`. Mathlib's submodule infimum is set intersection (`Mathlib/Algebra/Module/Submodule/Lattice.lean:211–216`). Its ordinary eigenspace is `ker(f - μ • 1)` and membership means `f ψ = μ • ψ` (`Mathlib/LinearAlgebra/Eigenspace/Basic.lean:422–429,468–469`). Therefore membership here says precisely that `ψ` lies in the supported exchange sector and has weight `κ`; it is neither a generalized eigenspace nor a nonzero-eigenvector predicate.

I traced both ingredients through `lean/AKLT/Defs/Operator.lean:20–51,159–210` and `lean/AKLT/Defs/FiniteNetwork.lean:81–85`. `centralWeight` counts exactly the single groups, returning rational zero for an even count and rational `1/2` otherwise. `Even` on naturals is ordinary parity (`Mathlib/Algebra/Group/Nat/Even.lean:28`); casting the rational weight into `ℂ` preserves these exact values. A pair contributes two distinct tokens. The corner leaders are `0,2,4,6`, their seconds are `1,3,5,7`, and tip leaders are `8,11,14,17`; there are no collisions and the `min 19` totalization never changes a pair's second index.

`exchangeSpace` is the complex span of exactly the paper's tensor basis vectors: two single vectors, three symmetric-pair vectors, or the exterior vector with coefficients `+1,-1`. A retained U pair is always symmetric; for a retained D pair, `ε = false` selects the exterior square and `ε = true` the symmetric square. Signs at other groups are unused. `Submodule.span` is the smallest containing linear subspace (`Mathlib/LinearAlgebra/Span/Defs.lean:44–47`), and `WithLp.toLp` preserves coordinates (`Mathlib/Analysis/Normed/Lp/WithLp.lean:47–76`). Thus the unnormalized vectors retain their actual inherited norms, exactly as required at `paper/app-local-operator.tex:432–440`.

The group basis vectors have weights `±1/2` for singles, `1,0,-1` for symmetric pairs, and zero for exterior pairs. They are nonzero, mutually orthogonal within a sector, and span it. Consequently the intersection selects precisely the span of basis vectors whose total weight is `κ`, agreeing also with paper lines 437–438. The algebraic construction is meaningful for every supplied pattern and either representation; it needs no positivity or coveredness hypothesis. The use in `lean/AKLT/Blueprint/Top/Operator.lean:93–105` is correspondingly a statement about arbitrary such tensor sectors, as in `paper/app-local-operator.tex:470–478`. With no groups the single empty tensor basis vector is the scalar one, `κ = 0`, and the central space is all of `ℂ`, not the zero space. More generally a central vector always exists: choose weight-zero vectors for all pairs and balance the singles to weight zero or positive one half.

Non-blocking remarks.

I read all of `FiniteNetwork.lean` and its local import closure: `Probability`, `Operator`, `Pattern`, `Frame`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`; I inspected the relevant Mathlib definitions and the operator interface uses. Paths beginning `paper/` and `lean/` refer to `/home/ubuntu/aklt/review/FID_S/`; Mathlib paths refer to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/`.

An exact-rational Python check passed 1,252 lift-entry comparisons for one through four tokens, all displayed single/pair magnetic weights and ladder actions, and the empty-tensor spin sums. It also checked 1,823 basis vectors across all 55 combinations of single, symmetric-pair, and exterior-pair counts with at most eight tokens: weights, disjoint supports within each sector, and existence of central vectors all agreed. These finite checks supplement the general coordinate arguments above; no Lean compilation was run. No blocking or other fidelity discrepancies were found in the five assigned declarations. Inputs were not modified.
