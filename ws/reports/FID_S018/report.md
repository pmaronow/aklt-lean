STATUS: PASS
BLOCKING: 0

DECL: productDensity PASS

The paper's product density is the tensor product of the matrices rho(u_i) in `app-local-operator.tex:269–275`, using rho(a) = (I + a·sigma)/2 from Definition `d:Pauli` at `app-local-operator.tex:246–258`. Lean's `Frame.lean:53–61` uses precisely the displayed Pauli matrices, with coordinates 0,1,2 corresponding to the paper's x,y,z coordinates. In particular its density is the matrix [[1+z, x-iy], [x+iy, 1-z]]/2, including the correct imaginary signs and normalization. The division is in C and its denominator 2 is nonzero.

`FiniteNetwork.lean:63–65` gives the tensor product's entries: the product of rho(u_j)[sigma_j,tau_j] over the subtype of tokens in J. This agrees with Mathlib's Kronecker entry convention (`LinearAlgebra/Matrix/Kronecker.lean:283–285`). The coercion of J to a type selects exactly its members; its `Fintype` instance and the finite function instance make `J → Fin 2` the full set of binary tensor configurations, with 2^|J| elements (`Data/Fintype/Sets.lean:226`, `Data/Fintype/Pi.lean:134`). Rows and columns use the same convention as `pauliOperator`.

For J empty, there is one binary configuration, the empty product is 1, and the resulting matrix is the one-dimensional identity with trace 1. This matches `app-local-operator.tex:16–18,314–315`; Mathlib's trace is the sum of diagonal entries (`LinearAlgebra/Matrix/Trace.lean:45–46`). Defining this formula for arbitrary real vectors is harmless: its use in `InversionStatement` (`Blueprint/Top/Operator.lean:64–71`) explicitly imposes the closed-ball condition at every token in J. Here `normSq` is the Euclidean sum of squares (`Moment.lean:9–15`), not the function-space supremum norm.

DECL: invertVectors PASS

Definition `d:Pauli` in `app-local-operator.tex:253–254` inverts exactly the selected vector variables. `FiniteNetwork.lean:68–69` negates u_j precisely when j belongs to I and leaves every other vector unchanged. Negation on `Vec3 = Fin 3 → R` is pointwise, so all three coordinates change sign together. There is no coordinate permutation or conjugation. This is the same substitution made by `invertPolynomial` (`Operator.lean:120–124`), and applying it twice returns the original assignment, as required in `app-local-operator.tex:301–303`.

The surrounding inversion statement supplies I subset J (`Blueprint/Top/Operator.lean:65–69`); values outside J do not enter the product density or the supported polynomial. No norm restriction is needed to define inversion, and the closed ball is preserved by negation. The fixed twenty-token ambient assignment accommodates the original twenty slots and every reduced token set in this appendix.

DECL: PositiveOn PASS

This auxiliary predicate expresses the positive definiteness used in Lemma `l:sector`, `app-local-operator.tex:470–478`, with the ambient Hermitian inner product specified at `app-local-operator.tex:432–434`. Its meaning is exactly: for each nonzero vector psi belonging to S, Re<psi,O psi> > 0. Mathlib's `EuclideanSpace C iota` is the finite L2 coordinate space, and its inner product is the sum of the coordinate inner products (`Analysis/InnerProductSpace/PiL2.lean:84–115`). The scalar convention is conjugate-linear in the first argument (`Analysis/InnerProductSpace/Basic.lean:915–927`), so the expression is Re(psi* O psi), with the intended sign and order.

The predicate does not independently require Hermiticity. Its uses in `SectorStatement` do explicitly assume that O preserves S and is Hermitian on S (`Blueprint/Top/Operator.lean:99–100`). Consequently the quadratic form is real there, and the predicate is equivalent to positive definiteness of that restriction. The central space is a subspace of S, so the same applies to the other occurrence. No positive value is required at the zero vector, and no unintended uniform lower bound is added. A zero-dimensional subspace satisfies the predicate vacuously, as positive definiteness on that space should; the concrete sectors themselves are nonzero.

DECL: eigenvaluesOn PASS

The auxiliary set in `FiniteNetwork.lean:77–79` is exactly the eigenvalue set of the restriction to an invariant S: mu belongs precisely when there is a nonzero psi in S with O psi = mu psi. Mathlib uses the same equation for eigenspace membership and the same nonzero condition for eigenvectors (`LinearAlgebra/Eigenspace/Basic.lean:422–440,468–469`). Membership in S is imposed on the witness itself, and the equation holds in the ambient space.

This matches the equality of eigenvalue sets, explicitly without multiplicities, in Lemma `l:sector`, `app-local-operator.tex:473–476`. `SectorStatement` supplies invariance of S and concludes invariance of the central space before asserting the equality (`Blueprint/Top/Operator.lean:99–105`), so these are actual restricted operators. Using complex scalars is appropriate for the complex Hilbert space; Hermiticity makes the occurring eigenvalues real. Zero is included only if there is a nonzero kernel vector. Excluding the zero witness prevents every scalar from becoming an eigenvalue. For the zero subspace the set is correctly empty.

DECL: exchangeSpace PASS

Definition `d:exchange`, `app-local-operator.tex:416–440`, specifies the complex tensor sector generated by singles, symmetric U-pairs, and the selected symmetric or exterior D-pairs, embedded in the full tensor Hilbert space. `FiniteNetwork.lean:82–85` takes exactly the complex span of these tensor basis vectors in the ambient Euclidean space. Mathlib's `Submodule.span` is the smallest complex submodule containing the specified range (`LinearAlgebra/Span/Defs.lean:45–47`); it does not impose extra equations or change the inner product.

I checked the basis construction in `Operator.lean:159–210`: a single has the two coordinate vectors; a symmetric pair has coordinates (1,0,0,0), (0,1,1,0), (0,0,0,1); an exterior pair has (0,1,-1,0). Thus 0 is e_+, 1 is e_-, and the exterior sign agrees with `app-local-operator.tex:426–429`. Only a retained D-pair with epsilon=false uses the exterior vector; epsilon=true selects its symmetric square. U-pairs are always symmetric. Taking products of these local entries gives exactly the tensor basis over all groups.

The token choices are disjoint: corner pairs use {0,1}, {2,3}, {4,5}, {6,7}, and tip singles use 8,11,14,17 (`Operator.lean:30–51`). Reduction removes isolated groups and replaces precisely the prescribed leaves, matching `app-local-operator.tex:146–158`. The `min 19` in `groupSecond` cannot collapse a retained corner pair. All group basis sizes are 1,2,3, and all index types are finite.

`WithLp.toLp 2` preserves the coordinates (`Analysis/Normed/Lp/WithLp.lean:47–76`), so the middle symmetric and exterior vectors keep squared norm 2; they are not silently normalized. The ambient L2 inner product is the paper's inherited one. If there are no groups, both configuration and basis types are singletons, and the spanning vector is the scalar 1, giving C rather than the zero space. Finally, `centralSpace` intersects this space with the actual Sz eigenspace (`FiniteNetwork.lean:102–105`), consistent with the paper's central-weight restriction.

Non-blocking remarks:

- `ExchangeSigns` stores unused Boolean choices at singles and U-pairs. These choices yield identical spaces, so the representation is redundant but the defined sector and all uses under review have the intended meaning.
- The generic positivity and eigenvalue helpers rely on their callers for Hermiticity and invariance. Those hypotheses are present in their only statement-level use; no missing side condition was found.
- Read the complete declaration file, its transitive AKLT imports, and the relevant operator interfaces. Source inspection was supplemented by 64 exact dyadic Pauli/inversion trace checks and checks of the pair exchange signs, Gram norms, disjoint token indices, and empty tensor indexing. No Lean process was run, and no input was modified.
