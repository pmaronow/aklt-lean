STATUS: PASS
BLOCKING: 0

DECL: Phase PASS
The paper's Definition `d:phaseweights` lists exactly A, B, C, D (`paper/app-input-contracts.tex:421–422`); its stationary state space uses the same four phases (`paper/app-input-contracts.tex:519–520`). `AKLT/Defs/Stationary.lean:10–14` defines four distinct nullary constructors and enumerates all four in its `Fintype` instance. These are independent of the separate two-constructor `PairType`, so the shared letters B and C cause no identification. Mathlib's `Fintype` consists of a duplicate-free finite set and a completeness proof (`Mathlib/Data/Fintype/Defs.lean:53–61`), and `Finset.univ` is that set (`:90–97`). Consequently phase sums range over exactly these four distinct states, once each. There is no empty-state or missing-state interpretation. Derived equality and representation add no mathematical hypotheses.

DECL: phaseTerminal PASS
The paper specifies terminal reward `g = (0,0,1,1)` in phase order A, B, C, D (`paper/app-input-contracts.tex:437–438`). The four branches at `AKLT/Defs/Stationary.lean:17` give exactly those values. The codomain is Mathlib's exact rational field, with distinct zero and one (`Mathlib/Algebra/Field/Rat.lean:27–36`; `Mathlib/Data/Rat/Defs.lean:138–145`). This is a reward function, with no normalization or additional type-dependent factor. Its use in the target boundary condition and in `stationaryReward` agrees with the paper's spatial terminal reward (`paper/app-input-contracts.tex:533–534`).

DECL: phaseInitial PASS
The paper starts with weight one in each of A and B (`paper/app-input-contracts.tex:437–438`), explicitly displaying `(1,1,0,0)` in its prefix recursion (`paper/app-input-contracts.tex:854–857`). `AKLT/Defs/Stationary.lean:20` gives precisely this vector. The literals are exact rational field elements, using the same Mathlib meanings checked for `phaseTerminal`. In particular the total initial weight is two; the definition does not divide it into a probability distribution. `prefixPhases` uses this vector directly as its initial accumulator (`AKLT/Defs/Stationary.lean:121–125`). No extra initial states or hypotheses are introduced.

DECL: phaseDiagonal PASS
Definition `d:phaseweights` gives the diagonal table in straight, turn, revisit order (`paper/app-input-contracts.tex:423–430`). Expanding `AKLT/Defs/Stationary.lean:23–28` gives exactly:

| Phase | straight | turn | revisit |
| --- | --- | --- | --- |
| A | x_s/3 | x_t/3 | 1/5 |
| B | x_s/3 | 1/3 | 1/5 |
| C | x_s/3 | 1/3 | 1/5 |
| D | 1/3 | 1/3 | 1/5 |

The leading revisit test applies to every phase before the wildcard branch. `StepKind` has exactly the three intended constructors (`AKLT/Defs/Automaton.lean:34–36`), so there are no additional kinds hidden by that wildcard. The imported `passageFactor true` and `passageFactor false` are respectively `(961/1000)⁻¹ = 1000/961` and `(187/200)⁻¹ = 200/187` (`AKLT/Defs/Trails.lean:9–12`), matching the appendix's fixed thresholds (`paper/app-input-contracts.tex:3–5`) and the definition of x (`paper/sec6-walks.tex:655–664`). Mathlib rational inverse and division have the usual field meanings (`Mathlib/Algebra/Field/Rat.lean:27–36`; `Mathlib/Data/Rat/Defs.lean:122–130`). Thus the scaled entries are exactly `1000/2883` and `200/561`, and the literal divisions are rational division, not natural-number division. Every denominator is nonzero. All twelve entries agree.

DECL: phaseTransition PASS
The paper adds precisely A → C on a turning first departure, with weight `x_t κ_h/3`, and B → D on a straight first departure, with weight `x_s κ_h/3`; all other phase changes are forbidden, including every change at a revisit (`paper/app-input-contracts.tex:432–436`). `AKLT/Defs/Stationary.lean:31–34` first supplies the correct diagonal when source and destination coincide, then implements just these two off-diagonal entries, then zero. Since `.turn` and `.straight` exclude `.revisit`, a revisit has transition matrix `(1/5) I`, independently of reward. The argument `φ` is the source and `ψ` the destination: `prefixPhases` forms `∑ φ, p φ * phaseTransition ... φ ψ`, while the backward operators multiply by the continuation at `ψ`. This agrees with both the backward row formula (`paper/app-input-contracts.tex:540–547`) and the explicit forward updates (`:880–897`), where old A contributes to new C on a turn and old B contributes to new D on a straight departure.

Multiplication and division here are in the exact rational field, so `passageFactor ... * reward / 3` is precisely the paper's coefficient. The reward is not divided by, rounded, or inserted into any diagonal entry. Source inspection and an independent rational-arithmetic transcription checked all 48 kind/source/destination entries as affine functions of reward, hence for every rational reward, including zero.

Non-blocking remarks:

- Read the whole `Stationary.lean` and its complete project import chain: `Automaton`, `Kernel`, `Trails`, `Domain`, `PinModel`, `Moment`, `Geometry`. Also inspected the downstream phase uses in `Computational.lean` and `Blueprint/Top/Computation.lean`. Only the five assigned declarations are judged here.
- The generic coefficient helper accepts any rational reward. Its true-trail callers supply `witnessKappa`, the finite sum of actual live-pair coefficients times the fixed h-vector, matching `paper/app-input-contracts.tex:439–443` and `paper/sec7-recursion.tex:523–536,572–578`. Free and stationary callers supply the corresponding relaxed reward, as required by `paper/app-input-contracts.tex:528–537`. These rewards are nonnegative rational sums; allowing the helper to evaluate other scalars does not assert nonnegativity for them or change any specified weight.
- The actual kind selection tests earlier departures before straight/turn classification. `wordStraight` compares outgoing direction with the incoming displacement, matching `paper/sec6-walks.tex:661–669`. The predecessor subtraction in the imported `wordIncoming` is guarded by a nonzero-index branch (`AKLT/Defs/Trails.lean:39–44`); none of the five assigned declarations uses natural subtraction or an index that can underflow.
- Mathlib's `∑ φ : Phase` is a finite sum over `Finset.univ` (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:24–31`). There is no infinite-sum convention, convergence hypothesis, class-size division, arbitrary finiteness premise, or quantifier-order issue in these definitions.
- Verification was by source review and the small exact rational branch cross-check; no Lean process was run. Inputs were not modified.
