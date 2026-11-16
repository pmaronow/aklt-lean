STATUS: FAIL
BLOCKING: 1

One blocking issue, B1, affects both `stationaryCoefficient` and `stationaryApply`: the known-site branch retains a nonzero edge from the start into the centre. The other three declarations pass.

DECL: relaxedReward PASS

This auxiliary implements the reward in `d:kernel` (`sec7-recursion.tex:516–536`) with the chosen dead set, as required by `d:stationary-walk` (`app-input-contracts.tex:529–537`) and its explicit reconstruction formula (`app-input-contracts.tex:722–739`). The arrival site is `x - incoming.step`, whereas the outgoing site is `x + outgoing.step`; thus the incoming-direction sign convention is correct. `Plane` is the actual integer lattice, with componentwise arithmetic, not a quotient.

Mathlib's `Finset.erase` removes the specified element (`Mathlib/Data/Finset/Erase.lean:49–58`), and finite-set difference removes exactly the dead elements (`Mathlib/Data/Finset/SDiff.lean:48–59`). `powersetCard 2` enumerates each unordered two-element subset once (`Mathlib/Data/Finset/Powerset.lean:196–203`). Consequently, with two live non-outgoing neighbours, the non-outgoing pair receives alpha and the two outgoing pairs receive beta; with one, the sole pair receives beta-prime; with none, the sum is empty and is zero. `responsePairType` classifies these distinct neighbouring pairs as B precisely when they are opposite, and otherwise as C. The exact alpha/beta/beta-prime table matches `sec7-recursion.tex:279–292`, and `kernelWitness` matches the dyadic h in `sec7-recursion.tex:572–578`.

The helper deliberately retains the outgoing site regardless of `dead`. Its relevant calls have a live outgoing neighbour: the free call has an empty dead set, and the ordinary stationary branch excludes an outgoing centre. Non-reversal on admitted non-revisit edges follows from `Q.Correct`, so the two other neighbours are indeed distinct. Arbitrary off-domain arguments to this auxiliary do not create an additional defect.

DECL: freeCoefficient PASS

Matches `d:stationary-walk`, `app-input-contracts.tex:535–537`, with the phase table at `app-input-contracts.tex:421–438`. A false Boolean admissibility flag gives zero; a true flag uses the automaton kind. The phase diagonal is exactly the four-row table, every revisit stays in its phase with weight 1/5, and the only nonzero phase changes are A to C on turns and B to D on straight passages, with the stipulated passage factor times reward divided by three.

Using the origin with no dead sites is valid because the reward and pair types are translation invariant. On admitted non-revisit edges the computed rewards are exactly `a_s + 2*b_s*h_C` and `b_t + (a_t+b_t)*h_C`, as stated at `app-input-contracts.tex:443–454`. `Q.arrival` is needed only on those edges; the response argument has no effect on a revisit coefficient. This agrees with the quotient's final-direction condition (`app-input-contracts.tex:314–340`; `Automaton.lean:78–84`). All weights are exact rational numbers, without rounding.

DECL: stationaryCoefficient FAIL

B1: `d:stationary-walk` specifies zero contribution for a transition into c (`app-input-contracts.tex:532`) and gives the backward row formula at `app-input-contracts.tex:540–550`. In Lean, the test `x + d.step = kernelCentre` occurs at `Stationary.lean:59`, only after the known-site branch at lines 56–58 has returned its coefficient. Thus it does not apply at the start u.

This discrepancy occurs with a correct quotient and the paper's allowed first directions. Let m=10, let w be ten north steps, and take the class `a = Q.project w` for any correct quotient. The raw window has distinct bonds, no earlier departure from its endpoint, and an admissible east extension. Hence `Q.Correct` forces `Q.allowed a east = true`, `Q.kind a east = turn`, and `Q.arrival a = north`. Set `d₀ = north`, `x = kernelStart = (-1,0)`, and `d = east`. Then the destination is c=(0,0), but this edge is not the initial bond `{(-1,0),(-1,1)}` and is not a memory-detected revisit. For every phase phi, Lean therefore returns

`stationaryCoefficient Q X north phi a (-1,0) east phi = 1/5`,

instead of the zero-centre-edge coefficient, for either X. This is not an example involving an incorrect quotient or a forbidden d₀. Finset bond equality is unordered, so the initial-bond comparison itself correctly excludes both orientations; it simply does not exclude this different bond.

The remaining branches match the paper: c and v have zero outgoing rows; inadmissible directions vanish; both known sites enforce the permanent initial-bond and detected-revisit rules with same-phase weight 1/5; ordinary sites use the prescribed centre-dead response. To obtain the stated zero-centre-edge operator, the destination-centre guard must apply before either position branch.

DECL: stationaryApply FAIL

The finite summation and destination indices themselves match `app-input-contracts.tex:540–548`: current phase and class determine the coefficient, and the continuation is evaluated at the next phase, quotient successor, and actual position `x + d.step`. However, B1 makes this a different operator on its declared function domain.

Using the correct-quotient state from the preceding counterexample, take the nonnegative rational function `F psi b y = 1` when `psi = Phase.A` and `y = kernelCentre`, and zero otherwise, independently of b. The only contributing term in the row at phase A, class a, and u is the east, same-phase edge. Lean gives `stationaryApply Q X north F Phase.A a kernelStart = 1/5`; the paper's operator with zero contribution into c gives zero.

The sentence permitting deletion of centre edges (`app-input-contracts.tex:550`) explains why retaining such an edge is harmless on continuation functions that vanish at c. It does not establish equality on arbitrary functions H in the displayed row formula. `stationaryApply` accepts every rational-valued F and carries no condition `F psi b kernelCentre = 0`. Thus that convention cannot repair exact equality on the declared domain. This is the same blocking issue B1, not a second independent defect.

DECL: freeApply PASS

Matches the position-free backward operator of `app-input-contracts.tex:535–537`, with the separate-direction convention explained at `app-input-contracts.tex:540–548` and `app-input-contracts.tex:342–355`. Mathlib's finite-type sum is a sum over `Finset.univ` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:63–70`). The local Fintype instances enumerate exactly four compass directions and four phases, so this is precisely the finite sum of sixteen direction/next-phase terms. Distinct directions remain separate even if their quotient successors coincide. There is no class-size normalization, matrix transpose, spatial identification, or infinite-sum convention. The coefficient is the passing `freeCoefficient`, and the continuation uses exactly the quotient successor.

Non-blocking remarks:

- Read all of `Stationary.lean` and its transitive AKLT imports: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, and `Geometry`. Judgments above concern only the five assigned declarations.
- The generic definitions accept quotient data without assuming correctness. Their paper-facing uses in `Blueprint/Top/Computation.lean:99–108` and `:125–132` explicitly require `Q.Correct` and `d₀ ≠ east`. The unrestricted data parameters are therefore not an additional blocking issue. The B1 example satisfies these conditions.
- All divisions relevant here occur in ℚ, whose Mathlib field instance is `Mathlib/Algebra/Field/Rat.lean:27`. The denominators 3, 5, 1000, 200, 10^6, and 4503599627370496, and both inverted local thresholds, are nonzero. No division-by-zero totalization is used. There is no natural-number subtraction in the five declarations; lattice subtraction is componentwise integer subtraction (the additive counterparts generated in `Mathlib/Algebra/Notation/Prod.lean:112–128`). The imported last-direction index m−1 is used under m>0; the paper-facing memory is ten.
- Exact-rational Python checks compared the helper with the paper's separate three-, two-, and one-neighbour cases in 144 configurations (all admitted incoming/outgoing choices, all subsets of the two other neighbours, at three translated sites). All matched. Another 36 comparisons verified the two free-reward formulas. A direct check of the ten-north-step raw window confirmed the admissibility and geometry used in B1. No Lean processes were launched.
- B1 does not alter the current certificate row values, because their centre values are constrained to zero (`app-input-contracts.tex:704–705`; `Stationary.lean:111–112`). The failure concerns the exact coefficients and unrestricted backward operator requested for this review. Inputs were not modified.
