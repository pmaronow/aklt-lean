# TS_WIN_04 — truth sweep of blueprint leaves

**Your leaves:**
- `AKLT.Blueprint.Win.CrossFactsStatement` (module `AKLT.Blueprint.Win.NodesTopology`, paper label l:thicken)
- `AKLT.Blueprint.Win.CrossOverlapStatement` (module `AKLT.Blueprint.Win.NodesTopology`, paper label l:thicken)
- `AKLT.Blueprint.Win.CrossUnionStatement` (module `AKLT.Blueprint.Win.NodesTopology`, paper label l:thicken)
- `AKLT.Blueprint.Win.NeighbourDecayStatement` (module `AKLT.Blueprint.Win.NodesTopology`, paper label l:thicken)
- `AKLT.Blueprint.Win.CrossWeightSumStatement` (module `AKLT.Blueprint.Win.NodesTopology`, paper label l:thicken)
- `AKLT.Blueprint.Win.ConnectedEnumerationStatement` (module `AKLT.Blueprint.Win.NodesTopology`, paper label l:Xconn)
- `AKLT.Blueprint.Win.CutScalesStatement` (module `AKLT.Blueprint.Win.NodesTaper`, paper label l:cutgeom)
- `AKLT.Blueprint.Win.CoreConnectedStatement` (module `AKLT.Blueprint.Win.NodesTaper`, paper label l:cutgeom)

Your working directory is `/home/ubuntu/aklt/reports/TS_WIN_04/`.

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
