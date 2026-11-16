STATUS: PASS
BLOCKING: 0

DECL: stepRatio PASS

Paper: `sec6-walks.tex:240`–254 (`d:ratios`), especially the post-step/pre-step quotient at lines 241–242; the trace operation is specified at `sec6-walks.tex:50`–68 (`d:trace`).

`AKLT/Defs/Response.lean:29`–30 specializes `traceRatio` to the two-vertex list `[y, o]`. Unfolding `traceNetwork` (`Domain.lean:94`–96) performs exactly one `traceStep`, then stops at the singleton list. Consequently the value is

`Z_(traceStep D y o)^bullet[1] / Z_D^bullet[1]`,

with the required orientation, rather than its reciprocal or the pinned/free ratio. `traceStep` (`Domain.lean:88`–91) deletes the selected bond at both ends, changes U to D, and removes a D departure. Under the paper's departure restriction, a D departure has no other present bond, so this is exactly its deletion rule. The site laws have total mass one: U has twelve weights `1/12`; D has twelve weights `1/20` and zero-atom weight `2/5` (`Moment.lean:58`–69; paper `sec2-moments.tex:8`–19). No `1/3` or `1/5` trace coefficient is inserted into this quotient, as required by the mass-free convention.

The same original `G` and pin assignment are passed to both partitions. `Network.partition` (`Domain.lean:63`–70) interprets `true` as pinned and `false` as free. Every surviving original leg is retained, including at a protected arrival site; deleting an internal bond creates no pin. Internal bonds are counted once using east/north orientations (`Geometry.lean:46`–55). This orientation only enumerates unoriented bonds; the scalar product is symmetric.

Mathlib division is real field division, with `a / 0 = 0` (`Mathlib/Algebra/GroupWithZero/Basic.lean:398`–402). That convention does not alter this quotient on its intended domain. Its uses in `Blueprint/Top/Coefficients.lean:32`–38 require `D.Auxiliary`, an admissible departure outside the original protected layer, and a present outgoing neighbour. These are the paper's conditions (`sec6-walks.tex:32`–42, 59–86). Both networks retain the local degree bounds and have strictly positive normalizers by `sec2-moments.tex:126`–157. There is no natural-number division or subtraction in this definition.

DECL: removedPairMean PASS

Paper: the pre-step network with the departure site removed is `E'` at `sec6-walks.tex:244`–251. Its pair observable is `P_ab = n_a · n_b` there; the pinned-minus-free pair responses are defined at `sec6-walks.tex:286`–288. This auxiliary definition supplies exactly `E_(E')^bullet P_ab` for those uses.

`removeSite` (`Response.lean:25`–26) changes only the status of `y` to X. Mathlib's `Function.update` changes the value at precisely its designated argument and preserves all others (`Mathlib/Logic/Function/Basic.lean:643`–654, 668–671). Active sites are `G.filter (status ≠ X)`. Since `Network.Present` requires both endpoints active, this status update removes every bond incident to `y`; stale kept entries pointing at `y` have no effect (`Domain.lean:15`–27). All other statuses, bonds and original pins remain the pre-step ones. In particular, this does not substitute the post-step D law at `y` for deletion.

`Network.expectation` is the partition with the inserted observable divided by the same partition with observable one (`Domain.lean:73`–75), matching `sec2-moments.tex:112`–117. The inserted `dot` is the Euclidean scalar product, explicitly `∑ i : Fin 3, a i * b i` (`Moment.lean:9`–12); `Fin 3` enumerates coordinates 0, 1, 2, merely relabelling the paper's three coordinates. There is no complex conjugation, sign change, or ambient lattice scalar product.

The finite-site subtype and function-space instances enumerate all configurations, rather than selecting a configuration: see `Mathlib/Data/Fintype/Sets.lean:226`–231 and `Mathlib/Data/Fintype/Pi.lean:133`–142. `SpinLetter = Option IcoLetter` enumerates all twelve icosahedral labels and the zero label (`Mathlib/Data/Fintype/Option.lean:29`–41). The zero label has zero mass at U, so using this common support gives exactly the paper's U/D product sums. The twelve vectors and weights are the explicit ones of `sec2-moments.tex:8`–19, with independent signs, not unspecified moment substitutes.

At every relevant use, `y` is outside S, and the inserted endpoints are distinct present neighbours of `y` in the pre-step network (`Coefficients.lean:33`, 39–51, 59–76). They survive removal and have at most three remaining factors each and no original leg (`sec6-walks.tex:334`–357). Thus neither the extension of spins by zero at removed sites nor division by zero changes the observable or expectation. Removing `y` preserves validity and normalizer positivity.

DECL: responseI PASS

Paper: `I = 1 + (P_fg + P_fo + P_go)/3` at `sec6-walks.tex:246`–251, and `I^bullet = E_(E')^bullet I` at `sec6-walks.tex:317`–320. The Lean scalar is this latter expected value, also used explicitly at `sec7-recursion.tex:418`–428.

`Response.lean:38`–41 is

`1 + (E'^[bullet](P_fg) + E'^[bullet](P_fo) + E'^[bullet](P_go)) / 3`.

All three means use the identical departure-deleted network, original pins and pin/free choice. Finite-sum linearity and `E'[1] = 1` identify this with the paper's `I^bullet`; positivity of the denominator, checked above, justifies the constant term. The three unordered pairs each occur once, the distinguished outgoing endpoint is `o`, and the other endpoints are `f, g`. Their order is consistent with both downstream coefficient identities.

The arithmetic is in ℝ, so `/ 3` is multiplication by the real reciprocal of three, not natural or integer division. The relevant interfaces require U status, the exact neighbour set `{o, f, g}`, and all three pairwise inequalities (`Coefficients.lean:44`–45, 68`). These exclude repeated endpoints and missing neighbours. The paper proves `41/50 ≤ I^bullet ≤ 34/25` (`sec6-walks.tex:334`–354), in particular strict positivity. No additional hypothesis such as consistent kept sets or the optimized local input is imposed on the uniform response definition.

DECL: responseJ PASS

Paper: `J = 1 + P_fg/5` at `sec6-walks.tex:246`–251, and `J^bullet = E_(E')^bullet J` at `sec6-walks.tex:317`–320; see also `sec7-recursion.tex:418`–420, 464–467.

`Response.lean:44`–45 is exactly `1 + E'^[bullet](P_fg) / 5`, hence the expected `J^bullet` by normalization and finite-sum linearity. It uses the pre-step network with `y` removed. It does not compute the pair mean in the post-step network, which would reweight the remaining spins by J. The outgoing endpoint does not appear in J, correctly: only the two retained neighbours `f, g` enter the post-step D-site sum (`sec6-walks.tex:259`–268).

The divisor is the nonzero real numeral five, matching the D law's second moment `(3/5)(1/3) = 1/5`. The inherited dot product, pins, finite enumeration and positivity checks are those above. On the three-neighbour domain the endpoints are distinct and present, and `116/125 ≤ J^bullet ≤ 134/125` (`sec6-walks.tex:349`–354). Thus its normalization and use as a logarithmic-mean argument are nondegenerate.

DECL: responseBeta PASS

Paper: `sec6-walks.tex:303`–332, especially the coefficient `1/(3 L_I)` at lines 317–332. The canonical choice is reiterated explicitly in `sec7-recursion.tex:425`–448, equation `e:rec-typed-coefficients`: `beta_j = 1/(3 L(I^tau, I^0))`, including coincident arguments and vanishing responses.

`Response.lean:48`–50 uses precisely the pinned expected I first and the free expected I second, in the same departure-deleted network, and divides one by three times their logarithmic mean. The local `logarithmicMean` (`Response.lean:8`–9) has the paper's off-diagonal formula `(x-y)/(Real.log x-Real.log y)` and diagonal value `x`. It is not an arbitrary coefficient witnessing the response identity or a numerical upper bound.

Mathlib's `Real.log` is the ordinary natural logarithm on positive reals (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:39`–53). Its extensions `log 0 = 0` and `log x = log |x|` for negative x are irrelevant here: the three-neighbour response hypotheses give both I arguments at least `41/50 > 0`. `Real.log` is strictly increasing and injective on positive reals (`Log/Basic.lean:249`–258), so distinct arguments give a nonzero log difference. Equal arguments use the explicit diagonal branch; in particular `I^tau = I^0 = 1` gives beta `1/3`, not zero or an indeterminate quotient. The logarithmic mean is positive in both branches, so neither division uses Mathlib's zero-denominator convention.

The sign agrees with the paper. Since `rho^bullet = J^bullet/I^bullet`, the response is `log rho^0 - log rho^tau = (I^tau-I^0)/L_I - (J^tau-J^0)/L_J`; the two outgoing-pair differences consequently have positive coefficient `1/(3 L_I)`. The interface uses exactly this logarithm order and pinned-minus-free differences (`Coefficients.lean:48`–51). The uniform coefficient does not assume H1 or a straight/turn type; those enter only the separate improved bounds, as in the paper.

Non-blocking remarks:

- The five definitions are total functions on raw `Network` data and arbitrary plane indices. Their mathematical uses supply validity and departure/neighbour hypotheses explicitly (`Coefficients.lean:32`–51, `Coefficients.lean:59`–76). Values outside that domain do not assert a paper theorem. No extra validity, pin, or finiteness premise is silently supplied by a typeclass. In particular, this assessment does not assume arbitrary raw networks have positive normalizers.
- The names `responseI` and `responseJ` stand for the expected scalars `I^bullet, J^bullet`, rather than the spin-dependent polynomials I and J in the definition. This is the right object for every occurrence found, including the canonical beta formula and the typed inequalities; see `sec7-recursion.tex:418`–448.
- These hypotheses are satisfiable. For example, take `G = {-3,...,3}²`, full kept sets, all statuses U except `(0,-1)` removed. The origin is outside S and has the three distinct present neighbours east, north and west; the removed site is outside S as well. This is an ordinary consistent domain and hence an auxiliary network, for arbitrary original unit pins. Thus the three-neighbour case is not vacuous.
- All geometry uses the ambient plane `ℤ × ℤ`; all volumes and spin enumerations are finite. Unit pins are exactly real three-vectors with `dot a a = 1`, which is the paper's unit sphere. Interior endpoints of original legs lie in S, so the partition's active-original-leg test agrees with the paper's protected-leg product on these networks. Empty products are one and the configuration space over an empty set of sites has one empty assignment, matching `sec2-moments.tex:20`–23, 117. There is no relevant truncated ℕ subtraction, spatial quotient, infinite sum, or arbitrary finiteness-instance parameter in the five definitions.
- Read all of `Response.lean` and its project import chain `Pattern → Trails → Domain → PinModel → Moment → Geometry`, and checked the relevant interface uses and Mathlib source semantics. No Lean processes were run; the findings concern statement/definition fidelity, not proof completion. Inputs were not modified.
