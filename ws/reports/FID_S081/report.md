STATUS: PASS
BLOCKING: 0

DECL: truePhaseSuffix PASS

This is the suffix factor in `l:phase-expansion`, paper `app-input-contracts.tex:467–468,507–513`, using `d:phaseweights` at `app-input-contracts.tex:421–440`. For a split after L departures, it computes the row vector concentrated at the specified phase, multiplied by the transition matrices at indices L through n−1, and finally by the terminal vector (0,0,1,1). It correctly excludes the prefix weight, which the caller supplies separately (`AKLT/Blueprint/Top/Computation.lean:91–94`).

Mathlib's `List.finRange n` lists each `Fin n` once in increasing index order (`Mathlib/Data/List/FinRange.lean:29–33`); `drop L` removes the first L entries, and `foldl` updates the accumulated vector in path order, with coefficient from old phase χ to new phase ψ. The final finite sum includes every terminal phase. Revisit classification takes priority over straight/turn classification, and `phaseTransition` gives precisely the paper's diagonal table and only the A→C turning and B→D straight responses (`AKLT/Defs/Stationary.lean:16–34`). The whole word w remains the argument to revisit and reward calculations: departure counts use indices strictly before the current index, and dead sites mean the centre or two previous departures. Thus history is retained across the split, as the paper explicitly requires. The live-pair rule, rational coefficient table, and exact dyadic h match `sec7-recursion.tex:279–284,516–536,572–578`; Mathlib's `powersetCard 2` means subsets of cardinality exactly two (`Mathlib/Data/Finset/Powerset.lean:196–203`), without ordered-pair duplication.

At L=n the fold is empty and the result is the terminal reward of the specified phase, as an empty suffix requires. The splitting interface explicitly assumes L≤n. The guarded predecessor in `wordIncoming` uses natural subtraction only when the index is positive, so it does not misclassify index zero. All phase arithmetic is exact rational arithmetic; the thresholds being inverted and all displayed denominators are strictly positive.

DECL: trueContinuationSum PASS

This is the complete finite-horizon true suffix sum in `l:stationary-domination`, paper `app-input-contracts.tex:554–561,635–644`, also used at `app-input-contracts.tex:996–1007`. It sums every suffix word of every length r with 0≤r≤R, conditional on the concatenation with P being a true completed trail, and weights it by the suffix phase factor just reviewed. It does not multiply in a second prefix factor.

Mathlib's `Finset.range (R+1)` contains exactly the naturals through R (`Mathlib/Data/Finset/Range.lean:52–65,98`). The finite function-type instance enumerates all words `Fin r → Compass`, exactly once (`Mathlib/Data/Fintype/Pi.lean:28–45,133–136`); for r=0 there is one empty word. In `appendWords`, indices below L select P and the other indices select v at index i−L. That subtraction occurs only with i≥L and has the correct bound i−L<r, so there is no truncation error. `ClosedTrail` checks injectivity of unoriented bonds on the entire concatenation, centre avoidance through the endpoint, the prescribed endpoint, and target avoidance at every earlier time (`AKLT/Defs/Kernel.lean:15–18`). It therefore enforces first hit and all prefix–suffix bond conflicts, rather than merely testing the suffix independently. Its start, target and incoming direction match `sec7-recursion.tex:517–525`.

The applicable interface supplies a surviving prefix, its first direction, a correct quotient, and L≥12=m+2 (`AKLT/Blueprint/Top/Computation.lean:106–109`), matching the paper's domain. For such a prefix, the r=0 summand is zero because its endpoint is not the target. Including length zero is consequently consistent with the stationary comparison and adds no completed trail.

DECL: stationaryReward PASS

This is exactly `g(φ,q,x)=1_{x=v} g_φ` in `d:stationary-walk`, paper `app-input-contracts.tex:516–534`, with `g_φ=(0,0,1,1)` from `app-input-contracts.tex:437–438`. Ignoring the memory-class argument is required by this formula. `kernelTarget` is (1,0) for B and (0,1) for C, as prescribed at `sec7-recursion.tex:517–518`.

The comparison is equality in `Plane = ℤ × ℤ`, with ordinary integer coordinates, so support is precisely the physical target, with no spatial identification. The centre and target are distinct, hence the centre has zero reward. `Fin 3741` is the nonempty finite quotient-class index, not a restriction on lattice positions. The values are exact rational zeros and ones, with no division or coercion ambiguity.

DECL: stationaryContinuationSum PASS

This is the stationary stopped sum through suffix horizon R in `l:stationary-domination`, paper `app-input-contracts.tex:557–561,640–644`, and the expression ∑_{j=0}^n T^j g in `l:Bellman-soundness`, `app-input-contracts.tex:648–679`. Mathlib's function iteration acts here on the entire curried function space `Phase → Fin 3741 → Plane → ℚ`; its zeroth iterate is the identity and subsequent iterates compose the backward operator (`Mathlib/Logic/Function/Iterate.lean:40–65`). Thus the j=0 term is g itself and the horizon includes exactly R transitions, without an off-by-one shift.

`stationaryApply` sums separately over the four actual directions and all next phases, using successor class and position x+d (`AKLT/Defs/Stationary.lean:53–67`), matching the backward orientation and parallel-edge convention at `app-input-contracts.tex:540–550`. The inherited coefficients implement the permanent initial-bond and known-site rules, the memory kinds, and the centre-dead relaxed reward. Rows at both centre and target are zero. Since the reward vanishes away from the target, a path that hits either terminal earlier cannot later contribute: these iterates count precisely first-hit target rewards, as explained at `app-input-contracts.tex:673–684`.

Each row has finitely many direction/phase indices. Consequently every finite iterate and horizon sum is a finite exact rational value even though the lattice is infinite; no finite spatial quotient, convergence assumption, probability normalization, or division is introduced. Correctness of Q and the allowed initial direction are supplied by the comparison and certificate interfaces (`AKLT/Blueprint/Top/Computation.lean:106–109,125–132`).

DECL: listBackward PASS

This is a faithful auxiliary representation of the nonnegative, finitely branching weighted backward operator in `l:Bellman-soundness`, paper `app-input-contracts.tex:648–660,664–678`. An edge `(t,w)` contributes w·F(t) to the row at s, exactly the required backward action. Mathlib's `List.map` and `List.sum` preserve one contribution per list occurrence; `sum []=0` and `sum (a::l)=a+sum l` (the existing additive list operations registered in `Mathlib/Algebra/BigOperators/Group/List/Defs.lean:14–16,26–27`). Repeated endpoints or repeated edge entries therefore retain parallel-edge multiplicity. Nothing turns the list into a set or averages its entries.

Every row is finite because it is a list, while the state type α may be infinite and needs neither a `Fintype` nor a decidable equality instance. Real coefficients and real function values give the paper's finite-valued weighted operator without imposing stochastic row sums. The generic definition appropriately leaves nonnegativity and terminal conditions to its user: `BellmanSoundnessStatement` explicitly requires nonnegative edge weights, empty terminal rows, nonnegative terminal-supported g, nonnegative F, and g+TF≤F (`AKLT/Blueprint/Top/Computation.lean:114–119`). Thus signed weights or nonterminal rewards cannot silently enter that application.

Non-blocking remarks:

- The definitions are total outside some paper domains (for example, `truePhaseSuffix` with L>n, arbitrary P, or an unchecked quotient). Their relevant interfaces impose the paper's side conditions; the reviewed uses do not exploit these extensions.
- At known sites, the inherited stationary coefficient can retain an edge into the centre. This does not change the reviewed continuation sum: g and every iterate T^j g vanish at the centre because its row is zero. Such an edge always contributes zero, consistent with `app-input-contracts.tex:549–550`, which permits deleting these edges because their continuation value is zero.
- Reviewed the complete `Computational.lean` file and its transitive AKLT imports: `Stationary`, `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. The verdict concerns only the five assigned declarations. This was a source-level fidelity audit; no Lean processes were launched and no inputs were modified. Paper paths are relative to the supplied `paper/` directory, AKLT paths to the supplied `lean/` directory, and Mathlib paths to the permitted Mathlib source root.
