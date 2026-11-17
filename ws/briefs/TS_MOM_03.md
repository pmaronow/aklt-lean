# TS_MOM_03 — truth sweep of blueprint leaves

**Your leaves:**
- `AKLT.Blueprint.Mom.FactorizedConditioningStatement` (module `AKLT.Blueprint.Mom.NodesFinite`, paper label l:finitefacts)
- `AKLT.Blueprint.Mom.TripleNormalizerStatement` (module `AKLT.Blueprint.Mom.NodesMean`, paper label l:35)
- `AKLT.Blueprint.Mom.TripleNumeratorStatement` (module `AKLT.Blueprint.Mom.NodesMean`, paper label l:35)
- `AKLT.Blueprint.Mom.TripleGeometryStatement` (module `AKLT.Blueprint.Mom.NodesMean`, paper label l:35)
- `AKLT.Blueprint.Mom.TripleSOSIdentityStatement` (module `AKLT.Blueprint.Mom.NodesMean`, paper label l:35)
- `AKLT.Blueprint.Mom.BallFieldSplitStatement` (module `AKLT.Blueprint.Mom.NodesMean`, paper label l:35)
- `AKLT.Blueprint.Mom.ProductMixtureStatement` (module `AKLT.Blueprint.Mom.NodesMean`, paper label l:35)
- `AKLT.Blueprint.Mom.PositiveMixtureEstimateStatement` (module `AKLT.Blueprint.Mom.NodesMean`, paper label l:35; l:finitefacts)

Your working directory is `/home/ubuntu/aklt/reports/TS_MOM_03/`.

## Truth sweep brief (common part)

**Context.** A Lean 4 blueprint splits a mathematics paper's proof into closed leaf statements
(`def <Name>Statement : Prop`), each to be proved by a separate writer who sees only that statement. Before writers
start, each leaf must be checked for TRUTH and SELF-SUFFICIENCY. The repository is `/home/ubuntu/aklt/repo`
(read-only for you; branch `main`; statement layer in `AKLT/Defs`, `AKLT/Blueprint/Top`, blueprints in
`AKLT/Blueprint/<Part>/`); the paper is `/home/ubuntu/aklt/manuscript-v2/` (main.pdf and .tex).

**For each of your leaves** (listed above with module and paper label), read its exact Lean statement and every
definition it unfolds to, and decide:
- `TRUE` — the statement is true as written and provable from its own hypotheses by the paper's argument;
- `UNDER-PREMISED` — the conclusion needs facts that are not among its hypotheses (name them);
- `FALSE` — give a concrete counterexample (small cases, degenerate/empty cases, `ℕ` subtraction, division by
  zero, wrong quantifier order, coercions, a definition that does not mean what the paper means);
- `VACUOUS` — true for a trivial reason the paper does not intend (contradictory hypotheses, empty domain);
- `UNSURE` — say what you could not settle.
Also flag Lean traps (instance arguments silently dropped, `Finset` vs `Fintype`, `Classical` decidability,
real vs rational coercions) and give, for TRUE leaves, a two-line proof route and difficulty (easy/medium/hard).
You may test small cases in Python or in Lean (scratch copies under your working directory; link Mathlib packages
from `/home/ubuntu/aklt/repo/.lake/packages` by symlink; build only single modules; at most 2 Lean processes).

**Deliverable.** In your working directory: `verdicts.jsonl`, one JSON object per leaf, written as you go:
`{"leaf": "<full Lean name>", "verdict": "TRUE|UNDER-PREMISED|FALSE|VACUOUS|UNSURE", "reason": "...",
"fix": "<corrected statement or missing premise, if any>", "route": "...", "difficulty": "easy|medium|hard"}`;
and `report.md` whose first line is `STATUS: COMPLETE` or `STATUS: PARTIAL (reason)` followed by a table of the
verdicts. Do not write proofs. Do not launch sub-agents. Do not modify the repository.
