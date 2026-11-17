STATUS: COMPLETE

| Leaf | Paper label | Verdict | Difficulty |
| --- | --- | --- | --- |
| `AKLT.Blueprint.Gap.FarBoundaryEqualityStatement` | `l:stopped` | TRUE | easy |
| `AKLT.Blueprint.Gap.StoppedHammingConversionStatement` | `l:hamming` | TRUE | easy |

Both leaves are true as written and self-sufficient. Neither needs a correction. Verdicts, reasons, and two-line proof routes are also recorded in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_GAP_08/verdicts.jsonl). No proofs were written and the repository was not modified.

The source inspected was `/home/ubuntu/aklt/repo`, branch `main`, HEAD `7a3393531c12080d76aefbdab300ac0c2df834b7`. Exact elaborated declarations are preserved in [inspection.log](/home/ubuntu/aklt/reports/TS_GAP_08/scratch/inspection.log).

`FarBoundaryEqualityStatement` is defined at [NodesShell.lean:140](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:140). Its hypotheses explicitly include `RegularSpec P`, an exterior site `y`, distance different from one, and two total assignments agreeing off `y`. The third conjunct of `RegularSpec` gives equality of laws when assignments agree on the exterior sites at distance at most one. Since an exterior site has positive integer distance from each square site, the stated distance exclusion places `y` outside that neighbourhood. All the sites relevant to range one therefore have the required agreement. The positivity and conditioning-consistency conjuncts of `RegularSpec` supply more than this leaf needs. This matches the far-site clause of `l:stopped` in [sec4-periodic-gap.tex:70](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:70) and its argument at [lines 75 onward](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:75).

Its proof route is:

1. Use the `ℕ∞` infimum definition of distance and `y ∉ square a u` to exclude `y` from the range-one exterior neighbourhood.
2. Apply the range-one conjunct of `RegularSpec` to the supplied agreement off `y`.

Lean traps for this leaf are:

- `setDistance` takes values in `ℕ∞` and is an infimum of natural distances; a real metric-space distance lemma does not apply directly. Proving its lower bound by `le_iInf` avoids any need to choose a minimizing site.
- `supDist` is the maximum of the natural absolute values of integer coordinate differences. Its zero-distance property is valid; there is no truncated natural coordinate subtraction.
- `u = 0` is allowed and gives a singleton square. There is no missing positive-radius premise or empty-square exception.
- `Config P.Letter` is a dependent assignment on the whole plane. The range-one hypothesis only tests exterior sites, so the use of total assignments causes no boundary ambiguity.

`StoppedHammingConversionStatement` is defined at [NodesShell.lean:148](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:148). Every requirement for using `StoppedEstimate` with `u = n^8` and `h = n` is explicit: the size threshold, `4 ≤ n`, the upper bound by `shellSpacing`, the distance-one condition, and agreement off the changed site. The radius identity identifies its target with the stated `farSites` at radius `(n : ℝ)^3`. Writing `δ = p * α^(16*l)`, the hypotheses give `0 ≤ d ≤ δ ≤ 1`, which is exactly the condition needed to enlarge the stopped failure bound from base `1-δ` to base `1-d`.

The remaining step is finite Hamming counting for that same full-law coupling. The explicitly supplied `Probability` premise normalizes the coupling, and the two cardinality bounds are also explicit. No range-one, finite-energy, window, or regularity assertion has to be recovered from an unstated paper convention. This is the conversion in [sec4-periodic-gap.tex:284](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:284) through the cost estimate at [line 296](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:296), using the elementary localization estimate in [app-finite.tex:116](/home/ubuntu/aklt/manuscript-v2/app-finite.tex:116).

Its proof route is:

1. Obtain the stopped coupling at `h = n`, rewrite its far-site radius, and enlarge its disagreement bound by monotonicity of natural powers.
2. Sum the pointwise near/far Hamming bound under that coupling and insert the two given cardinality estimates.

Lean traps for this leaf are:

- `Coupling` contains nonnegative entries and two marginals, with no normalization field. Here `∀ a η, Probability (P.law (square a (n^8)) η)` ensures total coupling mass one. Omitting that premise would invalidate the usual expectation argument for general weights.
- `Finset.univ` in the complement is over the subtype `↥(square a (n^8))`. Likewise, `Fintype.card (square a (n^8))` counts physical square sites. Neither expression requires a `Fintype Plane` instance or counts configurations.
- `PlaneSpec.finite` and `PlaneSpec.inhabited` are stored fields, with instances provided for each `P.Letter x`. The finite dependent configuration spaces therefore have the required instances. Lean inspection confirmed that both leaves are closed declarations of type `Prop`, with no silently dropped alphabet assumptions.
- `n^8` inside `square` and the size bound is a natural power. The radii and cardinality bounds are real, with explicit natural-to-real casts. The exponent `n-3` is natural subtraction, and `4 ≤ n` makes it positive. There is no rational coercion, real-power convention, or division in this conversion.
- `0 ≤ d ≤ δ ≤ 1` is sufficient even when `p` or `α` separately lack positivity hypotheses. The cases `d = 0`, `δ = 0`, `δ = 1`, and `d = 1` are valid; positive exponent avoids a zero-base/zero-exponent issue.
- Use `classical` for the agreement tests and finite filters. Equality is compared only between letters at the same site, so dependent alphabets cause no cross-site comparison.
- The imported `HammingLocalizationStatement` is a proposition, not an available proof. This leaf remains self-sufficient: its elementary pointwise counting estimate can be established directly and summed. No other leaf is assumed as a theorem.

All project definitions reached by unfolding the statements were read, including the unused positivity and conditioning parts of `RegularSpec`:

| Source | Definitions inspected |
| --- | --- |
| [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:15) | `Config`, `restrict`, `AgreeOn`, `PlaneSpec` and its instances, `PlaneConfig`, `fill`, `RegularSpec`, `couplingCost`, `disagreement`, `farSites`, `StoppedEstimate` |
| [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) | `Plane`, `supDist`, `setDistance`, `square`, `shellSpacing`, `geometryThreshold` |
| [Defs/Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9) | `Weight`, `normalize`, `PositiveProbability`, `Probability`, `hamming`, `Coupling` |
| [Defs/FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:42) | `conditionOn` |
| [Defs/FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:50) | `marginal` |

The hypotheses are consistent. For example, singleton site alphabets with the unique unit-mass law at every volume, independent of the boundary, give a regular specification and zero stopped disagreement. For the conversion, `l = Mstar = 0`, `n = 4`, and `p = α = d = 1` meet the numerical and counting requirements: `n^8 = 16^4`, `shellSpacing (n^8) = 16`, and `n * 16 = n^3`. For the far-boundary leaf, `a = (0,0)`, `u = 0`, and `y = (2,0)` realize its exterior-distance hypotheses. Neither verdict relies on contradictory hypotheses or an empty domain.

Validation used one Lean process to inspect the existing declarations under Lean `v4.35.0-rc2`; it exited successfully. The scratch environment links `.lake/packages` to the repository's packages and reads the existing compiled imports. [Inspect.lean](/home/ubuntu/aklt/reports/TS_GAP_08/scratch/Inspect.lean) contains only inspection commands. Small-case diagnostics in [sanity_checks.py](/home/ubuntu/aklt/reports/TS_GAP_08/scratch/sanity_checks.py) passed 672 exterior-distance checks, 2,603 Hamming-localization checks, and 180 exact rational power comparisons; see [sanity.log](/home/ubuntu/aklt/reports/TS_GAP_08/scratch/sanity.log). These checks include radius zero, empty/full far sets, singleton and site-dependent alphabets, and the power endpoints. They are diagnostics rather than formal proofs of the leaves.
