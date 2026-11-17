STATUS: PASS
BLOCKING: 0

DECL: stationaryCoefficientV2 PASS

The definition at `lean/AKLT/Defs/Stationary.lean:171–178` matches `d:stationary-walk`, `paper/app-input-contracts.tex:517–553`, with the phase weights at `paper/app-input-contracts.tex:422–455` and the response rule at `paper/sec7-recursion.tex:517–537`.

The start, centre, and targets are exactly `u=(-1,0)`, `c=(0,0)`, and `v=(1,0)` for B or `(0,1)` for C (`Defs/Kernel.lean:8–12`; `paper/sec7-recursion.tex:518–521`). `Plane` is `ℤ × ℤ`, and the four compass steps have the paper's absolute E,N,W,S signs (`Defs/Geometry.lean:8,17–36`; `paper/app-input-contracts.tex:21–34`). Mathlib's product addition and subtraction are componentwise (`Mathlib/Algebra/Notation/Prod.lean:65–82,112–128`, including their additive versions). Thus `x + d.step` is the actual destination and `x - incoming.step` is the arrival site; these are integer operations, without truncated natural subtraction or a spatial quotient.

Every forbidden automaton direction, every outgoing edge from either terminal, and every edge into the centre has coefficient zero. In particular, the centre-destination test precedes the known-site branch, so an edge from `u` into `c` is zero regardless of the continuation function. This agrees with `paper/app-input-contracts.tex:522–535`. At `u` and `u+d₀`, equality of the two endpoint `Finset`s forbids the initial unoriented bond in both directions. A detected revisit is killed. Every remaining edge there is exactly `1/5` in the same phase, with no response (`paper/app-input-contracts.tex:525–528`). The endpoint sets have two distinct elements because all compass displacements are nonzero; set equality introduces no directed-bond convention.

Elsewhere `phaseTransition` implements exactly the four diagonal rows: A uses `(x_s/3,x_t/3,1/5)`, B and C use `(x_s/3,1/3,1/5)`, and D uses `(1/3,1/3,1/5)`. Its only off-diagonal entries are A→C on a turn and B→D on a straight passage, with coefficient `x_τ κ_h/3`. Revisit entries are diagonal and independent of the computed response reward, as required by `paper/app-input-contracts.tex:422–441`.

The auxiliary `relaxedReward` is the right reward for these edges. It removes the arrival and outgoing sites from the four neighbours, deletes only the centre from the remaining two sites, and then inserts the distinguished outgoing site. Mathlib's `Finset.mem_powersetCard` says that `powersetCard 2` enumerates exactly the two-element subsets (`Mathlib/Data/Finset/Powerset.lean:198–203`), each once. With two live non-outgoing neighbours, the pair without the outgoing site receives `a_τ` and the other two receive `b_τ`; with one, the sole pair receives `b'_τ`; with none, the sum is empty. On an admitted non-revisit edge the outgoing site differs from the arrival site. The centre cannot be the outgoing site because of the outer guard. Among distinct neighbours of the same site, sharing a coordinate is precisely being opposite, so `responsePairType` supplies B for opposite pairs and C for perpendicular pairs. This is exactly the explicit reward formula at `paper/app-input-contracts.tex:723–745`.

The rational constants agree with `paper/sec7-recursion.tex:280–293,572–578`: inverse thresholds `1000/961` and `200/187`, the six alpha/beta/beta-prime entries, and the exact dyadic `h_C=5404319552844595/4503599627370496`. All divisors and thresholds are strictly positive. No zero-division or floating approximation changes an entry.

DECL: stationaryApplyV2 PASS

`lean/AKLT/Defs/Stationary.lean:183–186` is precisely the backward sum displayed at `paper/app-input-contracts.tex:541–550`: source indices `(φ,a,x)`, coefficient indexed by outgoing direction and next phase, and continuation evaluated at `(ψ,Q.successor a d,x+d.step)`.

Mathlib's unrestricted finite-sum notation sums over `Finset.univ` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:18–30,170–172`; `Mathlib/Data/Fintype/Defs.lean:92–97`). The explicit `Fintype` instances for `Compass` and `Phase` enumerate their four constructors. Consequently the sum includes all sixteen direction/next-phase choices, including zero entries. Different directions remain separate even when their quotient successors coincide, exactly as required by `paper/app-input-contracts.tex:541–548` and `315–356`. There is no division by a class size, reversal of the operator, or summation over lattice positions.

`F` is an arbitrary rational-valued function. No condition on its centre value is imposed or needed: every coefficient into the centre is already zero, and both terminal rows are identically zero. Exact rational arithmetic is sufficient for the rational potentials and finite stopped sums using this auxiliary operator. The definition does not restrict `F` to stored sites, nonnegative values, or periodic functions.

DECL: StationaryData.PassesV2 PASS

`lean/AKLT/Defs/Stationary.lean:191–206`, together with its array and extension definitions at lines 76–102, expresses all and only the arithmetic checks of `d:stationary-certificate`, `paper/app-input-contracts.tex:688–721`:

1. Every cap `Z` is strictly positive.
2. The C and D caps are at least `V` for every class.
3. Every phase/class free row satisfies `∑ p(t) Z_dest ≤ D₃ Z_source`.
4. Every stored entry satisfies `0 ≤ U ≤ Z`; the lower inequality is built into its type `ℕ`.
5. Every phase/class centre entry is zero and every target entry is `V g_φ`, with `g=(0,0,1,1)`.
6. Every stored nonterminal phase/class/site row satisfies `∑ p(t) Ũ_dest ≤ D₃ U_source`, using the V2 coefficients.

All these conditions are conjoined, with universal quantifiers over all the indicated indices. In the last clause the two implications exclude exactly the centre and target. They do not restrict other rows or introduce an existential choice of successor values. Positivity of the caps and the C,D target values exclude the unintended all-zero certificate.

The frozen constants are exactly `R=70`, `V=2^16=65536`, and `D₃=2^48=281474976710656`. Mathlib's `Finset.Icc` includes both endpoints (`Mathlib/Order/Interval/Finset/Defs.lean:300–302`), its integer instance has the ordinary integer interval meaning (`Mathlib/Data/Int/Interval.lean:29–44`), and `Finset.product` is the Cartesian product (`Mathlib/Data/Finset/Prod.lean:46–62`). Thus `square (0,0) 70` is exactly `{-70,…,70}²`, with 19881 sites. Coercion of that finset to a type gives the subtype of its members (`Mathlib/Data/Finset/Defs.lean:157–181`), so the stored-site quantifiers cover precisely this square. Both terminals are inside it, and checking `extended` at the terminals is therefore equivalent to checking their stored `U` entries.

`extended` uses the stored value inside and the corresponding cap outside, at the actual successor position, as prescribed at `paper/app-input-contracts.tex:693–694,707–710,794–797`. There is no spatial wrapping. The terminal equality's cast to `ℚ` preserves the natural entry exactly, and its right-hand side is exactly 0 or V. Every other certificate sum, product, and inequality is over unbounded natural numbers, equivalent here to the paper's inequalities between nonnegative integers. No natural subtraction or integer division occurs in these row checks.

`coefficientCeiling t` is `Nat.ceil (D₃*t)`. This is the least natural upper bound, not a floor or a nearest-integer operation (`Mathlib/Algebra/Order/Floor/Defs.lean:120–148`). All coefficients used here are nonnegative, so it equals the ordinary integer ceiling in the paper (`Mathlib/Algebra/Order/Floor/Ring.lean:911–921`; rational floor instance in `Mathlib/Data/Rat/Floor.lean:38–51`). Thus natural truncation on negative arguments has no effect. A zero coefficient has ceiling zero. Each coefficient is formed after its response-pair sum and rounded separately for each direction and next phase, matching `paper/app-input-contracts.tex:695–698,717–752`. The operators themselves retain their exact rational coefficients.

Non-blocking remarks:

- Read the entire target file and its project import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Judgments above concern only the three assigned declarations.
- These auxiliary definitions accept general quotient data and compass directions. Their mathematical uses impose `Q.Correct`, memory 10, 3741 classes, and `d₀ ≠ east` (`Blueprint/Top/ComputationV2.lean:41–81`). This supplies the paper's regenerated-automaton and N/W/S conditions rather than assuming correctness inside the data structure. In particular, correctness identifies allowed non-revisit incoming directions; mixed arrivals on revisit-only classes do not affect any coefficient. General totalization outside that context introduces no weakened assertion in these definitions. A `MemoryQuotient m 0` cannot exist: its `project` would map the nonempty direction-word type into `Fin 0`.
- As independent arithmetic checks, Python exact fractions confirmed all 48 nonreversing incoming/outgoing/centre-location reward cases and 338688 coefficient comparisons across both targets, the three permitted initial directions, all phases, local geometry, and admissibility/kind branches. The four diagonal ceiling numerators reproduced `97632666219444, 100347585280092, 93824992236886, 56294995342132` (`paper/app-input-contracts.tex:753–757`). These checks support the definition review; they do not assert verification of archived certificate arrays. No Lean process was run and no input was modified.
