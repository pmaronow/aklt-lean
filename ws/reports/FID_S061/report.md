STATUS: PASS
BLOCKING: 0

Reviewed the whole `AKLT/Defs/Probability.lean` file and the relevant callers. Paper paths below are relative to `/home/ubuntu/aklt/review/FID_S/paper/`; Lean paths are relative to `/home/ubuntu/aklt/review/FID_S/lean/`; Mathlib paths are relative to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`. The file imports only the Mathlib umbrella; the relevant Mathlib meanings are identified below.

DECL: Weight PASS

`AKLT/Defs/Probability.lean:9` is an auxiliary abbreviation for a real coefficient function `Ω → ℝ`, rather than an assertion that the coefficients already form a probability. This is the right carrier for the unnormalized products in Definition `d:framemodel` (`sec3-quantum-frames.tex:490`, formulas at lines 495–505) and the partition summands in Definition `d:pinmodel` (`sec2-moments.tex:106–115`). It also accommodates the unnormalized reference coefficients used by `torusReference` (`AKLT/Defs/FrameModel.lean:73–75`). Thus normalization or positivity must not be built into this carrier.

Mathlib's `ℝ` is the ordinary real number type, constructed from the rational Cauchy completion (`Basic/Real/Basic.lean:33–41`), with its field structure at line 481. The abbreviation introduces no coercion, support restriction, quotient, or hidden probability hypothesis. Although the carrier itself allows arbitrary `Ω`, all four reviewed operations/predicates involving sums explicitly require `[Fintype Ω]`. Its generality does not introduce an infinite summation into any of them.

DECL: normalize PASS

`AKLT/Defs/Probability.lean:12–13` defines exactly `w(x)/Z`, with `Z = ∑ y, w(y)`. This is the normalization in Definition `d:framemodel` (`sec3-quantum-frames.tex:495–505`) and in the normalized partition functional of Definition `d:pinmodel` (`sec2-moments.tex:113–115`). The actual unnormalized coefficient, including reference site masses, is divided by its actual total; there is no additional uniform average or omitted factor. The direct law constructors use precisely this helper (`AKLT/Defs/FrameModel.lean:45–47,69–71`).

Checked Mathlib semantics: the bare sum notation expands to `Finset.sum Finset.univ` (`Algebra/BigOperators/Group/Finset/Defs.lean:120–129,198–210`). A `Fintype` lists every element without duplicates, and `Finset.univ` is that list (`Data/Fintype/Defs.lean:51–62,90–97`). Division is real field division, with zero inverse (`Basic/Real/Basic.lean:476–488`). In particular, `a/0 = 0` (`Algebra/GroupWithZero/Basic.lean:402`), so a zero-total weight normalizes to the zero function, including when signed coefficients cancel. The helper does not claim this result is a probability.

This total extension causes no mismatch in its uses: the frame laws are considered under proper colouring, and the paper explicitly proves every summand and normalizer positive (`sec3-quantum-frames.tex:519–524`; compare the proper-colouring hypotheses and probability conclusions in `AKLT/Blueprint/Top/Quantum.lean:82–101`). The finite-network use is under validity, with positive partition sums explicitly asserted (`AKLT/Blueprint/Top/Common.lean:35–45`), matching `sec2-moments.tex:126–157`. Conditioning uses the same quotient on the paper's positive conditioning events (`sec1-result.tex:139–140`; `app-finite.tex:12–16`). For nonzero total, summing the normalized coefficients gives `Z/Z = 1`; distributing the division through the sum is Mathlib's `Finset.sum_div` (`Algebra/BigOperators/Field.lean:26–27`).

DECL: PositiveProbability PASS

`AKLT/Defs/Probability.lean:16–17` asserts both strict positivity at every state and total mass exactly one. This is precisely a strictly positive probability on a finite state space, as used in `app-finite.tex:4–16,23–26`, and the full-support assertion in Definition `d:framemodel` (`sec3-quantum-frames.tex:508,519–524`). The universal quantifier covers every state, not merely the support, and the normalization is an independent conjunct.

The inequalities and constants are in `ℝ`, with its ordinary strict order and nontriviality (`Basic/Real/Basic.lean:266,337–341,471`). The finite-sum meaning is the one checked above. `Fintype` alone permits an empty type, but its sum is zero: Mathlib generates `sum_empty`/`sum_of_isEmpty` from the additive counterparts at `Algebra/BigOperators/Group/Finset/Defs.lean:378–389,753–754`. Consequently an empty state space cannot satisfy the mass-one conjunct; there is no vacuous positive probability. On a singleton the predicate requires mass one and is satisfied, as the paper intends. An empty set of sites has one empty configuration, rather than an empty state space (`sec2-moments.tex:22–23`; `sec3-quantum-frames.tex:523–524`). No additional nonemptiness hypothesis is needed.

DECL: Probability PASS

`AKLT/Defs/Probability.lean:20–21` asserts nonnegative real mass at every state and total mass one. This is the general finite probability used in Definition `d:moment` (`sec2-moments.tex:16–27`), the finite-probability convention (`sec1-result.tex:131–135`), and Lemma `l:finitecoupling` (`app-finite.tex:68–83`). Allowing zero atoms is essential for general finite probabilities; strict positivity is reserved for the separate predicate above.

Mathlib's real `≤` is the usual non-strict order (`Basic/Real/Basic.lean:293–305,471`). The sum includes every state exactly once under `[Fintype Ω]`. Nonnegativity and mass one imply each atom is at most one, so a separate upper-bound clause would be redundant. Negative mass and the zero law fail the predicate. The empty-type case again fails because its total is zero; singleton mass one succeeds. Thus omitting an explicit `Nonempty Ω` neither weakens the probability condition nor produces a degenerate reading.

DECL: expectation PASS

`AKLT/Defs/Probability.lean:24–25` is the auxiliary real-valued expectation `∑ x, p(x) f(x)`. This agrees with the paper's finite-sum convention (`sec2-moments.tex:14–19,31–33`) and the normalized expectation `Z[f]/Z` in Definition `d:pinmodel` (`sec2-moments.tex:106–115`): substituting `p = normalize w` gives exactly that quotient. It also agrees with the probability functional notation `μ(f)` used in `app-finite.tex:39–47`.

Mathlib evaluates this as a finite sum of ordinary real products (`Algebra/BigOperators/Group/Finset/Defs.lean:59–69,198–210`; `Basic/Real/Basic.lean:98–107,228`). There is no extra cardinality division, conjugation, sign, truncation, or coercion into extended nonnegative reals. Finite domains and real-valued observables need no integrability or measurability hypotheses. The absence of a bundled proof that `p` is a probability makes this a weighted-sum helper; it asserts no probability property of arbitrary inputs. Its restriction to real observables is appropriate: the same file separately defines `complexMean` for complex observables and uses it in complex variance (`AKLT/Defs/Probability.lean:31–37`), matching the paper's complex convention (`sec1-result.tex:140–141`; `app-finite.tex:26`). There are no callers of this real helper elsewhere in the supplied Lean files that would require a broader domain.

Non-blocking remarks:

- “Finite weights” in the `Weight` docstring describes its intended use; finiteness is enforced by the consuming declarations, not by the abbreviation itself.
- The arithmetic in all five declarations is real arithmetic. None contains natural-number subtraction, a site-count normalization, or an index/sign convention that could change the stated quantities. `open scoped ENNReal` does not change these explicitly real types.
- This was a source-level fidelity review; no Lean processes were launched and no input files were modified.
