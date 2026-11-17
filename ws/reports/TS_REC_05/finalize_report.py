"""Format the completed audit from the incrementally recorded verdicts."""

import json
from pathlib import Path

root = Path(__file__).parent
order = [
    "CoveredIntegratedLowerStatement",
    "BetaPrimeAnalyticStatement",
    "BetaAnalyticStatement",
    "AlphaAnalyticStatement",
    "UStepMomentStatement",
    "DStepMomentStatement",
    "TraceDynamicsStatement",
    "TraceCoefficientStatement",
]
entries = [json.loads(line) for line in (root / "verdicts.jsonl").read_text().splitlines()]
by_name = {e["leaf"].rsplit(".", 1)[1]: e for e in entries}
# This rating includes establishing the evolving-status invariant in a
# standalone proof, rather than assuming another unproved leaf as a premise.
by_name["TraceCoefficientStatement"]["difficulty"] = "hard"
entries = [by_name[name] for name in order]
(root / "verdicts.jsonl").write_text(
    "".join(json.dumps(e, ensure_ascii=False) + "\n" for e in entries)
)

locations = {
    "CoveredIntegratedLowerStatement": ("NodesLocal", 52, "l:response-typed", 395),
    "BetaPrimeAnalyticStatement": ("NodesLocal", 65, "l:response-typed", 497),
    "BetaAnalyticStatement": ("NodesLocal", 71, "l:response-typed", 480),
    "AlphaAnalyticStatement": ("NodesLocal", 78, "l:response-typed", 480),
    "UStepMomentStatement": ("NodesWalk", 11, "l:stepid", 100),
    "DStepMomentStatement": ("NodesWalk", 19, "l:stepid", 143),
    "TraceDynamicsStatement": ("NodesWalk", 27, "d:trace", 50),
    "TraceCoefficientStatement": ("NodesWalk", 38, "d:trace", 90),
}
traps = {
    "CoveredIntegratedLowerStatement": (
        "Unpack all proof fields of `Departure`; they supply auxiliary validity, admissibility and the present outgoing bond. "
        "Use `CoveredDepartureV2`, including its intersection with `G`: outside directions are original legs, whose pins remain in `Network.partition`. "
        "The threshold is a rational cast to a real. Rotation sends canonical north to `incoming`, so pattern straightness equals `outgoing = incoming`. "
        "Cancellation uses the positive removed-site partition; positivity of `J` is also derivable (even the coarse bound `J ≥ 4/5` suffices). "
        "Classical finite choices in the mixture introduce no additional hypothesis."
    ),
    "BetaPrimeAnalyticStatement": (
        "`logarithmicMean` has an explicit diagonal branch. Handle equal arguments before clearing a logarithm difference; "
        "a denominator sign cannot be assumed for unequal arguments until their order is known. "
        "All divisions here are real, and `0 < c` also makes `It` strictly positive."
    ),
    "BetaAnalyticStatement": (
        "Infer positivity before reversing inequalities under reciprocals. The fractions `3/5` and `116/125` are real in this statement. "
        "The two lower bounds on `Jt` and `J₀`, together with `c > 0`, supply every required positivity fact."
    ),
    "AlphaAnalyticStatement": (
        "Keep the same `Jt,J₀` subtraction while lowering `It,I₀`; then compare the entire function `G_c`. "
        "Independent bounds on the positive and subtracted terms do not give this sharper estimate. "
        "Both conditions `3/5 ≤ c` and `c ≤ 1` support the monotonicity argument, and diagonal values are included."
    ),
    "UStepMomentStatement": (
        "The residual product is a `Finset` product over `Finset.univ.erase i`, rather than a product over the full `Fintype`. "
        "At `k = 0`, the product on the left is one but its inserted linear factor has mean zero; the outer sum on the right is empty. "
        "`SpinLetter` includes a zero atom of weight zero for U and weight `2/5` for D; omitting that D atom would change its constant moment. "
        "The vectors are arbitrary real vectors, so positivity of the individual linear factors is unnecessary."
    ),
    "DStepMomentStatement": (
        "Keep the explicit restriction `k ≤ 1`; this deletion formula does not extend to general larger `k`. "
        "The second moment is `1/5`, since each of the twelve nonzero D labels has weight `1/20`. "
        "`Fin 0` contributes an empty sum, and the zero atom contributes nothing to the inserted linear factor."
    ),
    "TraceDynamicsStatement": (
        "`StoppedNetworkTrail` tests presence in the initial network; presence in each prefix must be established using distinct unoriented `wordBond`s. "
        "Use the prohibition of departures from the original `protectedSites G`, which is present even for arbitrary `T`. "
        "`prefixNetwork ... j` takes `j+1` vertices and performs `j` trace steps. "
        "The terminal prefix is required to be auxiliary, while admissibility is required only at departures indexed by `Fin n`. "
        "The initial D bound is at most one, not the general auxiliary D bound of two."
    ),
    "TraceCoefficientStatement": (
        "`traceCoefficient` and its displayed factors are rational, and both exponents are natural. "
        "`ND` filters the full `Finset.univ : Finset (Fin n)` by evolving prefix status, not initial status or lattice revisit count. "
        "Its equality test has the ordinary `DecidableEq Status` instance. The proof must exclude the recursive X branch before asserting positivity. "
        "Factoring each D contribution directly avoids natural subtraction and its truncation behavior."
    ),
}

lines = [
    "STATUS: COMPLETE",
    "",
    "All eight leaves are TRUE as written. No statement correction or additional mathematical premise is needed. "
    "Difficulty rates a standalone Lean development from the concrete definitions; the coefficient leaf includes establishing its prefix-status invariant.",
    "",
    "| Leaf | Verdict | Difficulty | Paper label |",
    "|---|---|---|---|",
]
for e in entries:
    short = e["leaf"].rsplit(".", 1)[1]
    lines.append(f"| `{e['leaf']}` | {e['verdict']} | {e['difficulty']} | `{locations[short][2]}` |")

lines += [
    "",
    "The audit followed the exact statements and their concrete dependency chains: "
    "[Rec definitions](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:15), "
    "[geometry](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:9), "
    "[site laws and vectors](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9), "
    "[original pins](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:10), "
    "[networks and tracing](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10), "
    "[direction words and stopped trails](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:24), "
    "[covered patterns](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:9), "
    "[H1](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/Response.lean:10), and "
    "[logarithmic means and responses](/home/ubuntu/aklt/repo/AKLT/Defs/Response.lean:9). "
    "Helper facts in the routes below are consequences of these definitions. H1 is an explicit premise of the covered leaf; "
    "that leaf is classified as the stated conditional, without independently certifying H1.",
    "",
    "The conclusions have substantive admissible instances. The analytic hypotheses allow equality at their lower endpoints; "
    "the moment formulas allow arbitrary vectors and nonempty index types; and interior auxiliary networks admit positive-length stopped trails. "
    "For example, a U square with one adjacent interior site removed and the passage flag toward it erased admits a straight covered departure away from the removed site "
    "and a trail to its protected layer. Empty cases are compatible with the formulas rather than making the universal assertions trivial.",
]

for e in entries:
    short = e["leaf"].rsplit(".", 1)[1]
    module, line, label, paper_line = locations[short]
    paper = "sec7-recursion" if module == "NodesLocal" else "sec6-walks"
    lines += [
        "",
        f"**`{short}` — {e['verdict']}, {e['difficulty']}.** "
        f"[Lean source](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/{module}.lean:{line}); "
        f"[paper argument](/home/ubuntu/aklt/manuscript-v2/{paper}.tex:{paper_line}). "
        + e["reason"],
        "",
        "Proof route: " + e["route"].replace("\n", "  \n"),
        "",
        "Lean checks: " + traps[short],
    ]

lines += [
    "",
    "Across these leaves, all finite index types are concrete (`Fin k`, `SpinLetter`, active-site subtypes and compass directions). "
    "Lean printed all eight definitions with the intended quantifiers and hypotheses; there is no silently dropped instance parameter. "
    "Classical reasoning may be used for finite reindexing and choices without strengthening any proposition.",
    "",
    "Validation completed with one Lean process and no proof declarations. "
    "[Inspect.lean](/home/ubuntu/aklt/reports/TS_REC_05/lean-scratch/Inspect.lean) imports the existing compiled module and prints the eight statements; "
    "[compiler output](/home/ubuntu/aklt/reports/TS_REC_05/lean-scratch/inspect-output.txt) contains the printed definitions, and Lean returned exit code zero. "
    "[checks.py](/home/ubuntu/aklt/reports/TS_REC_05/checks.py) passed 600 numerical moment cases, "
    "1,648 numerical analytic inequalities and 45,272 exact-rational trace-prefix checks across 7,680 valid configurations of a lattice square with a tail. "
    "The trace cases include 32 prefixes with repeated departures and 24,072 zero-length prefixes. "
    "[Recorded results](/home/ubuntu/aklt/reports/TS_REC_05/checks-result.json) distinguish these supporting checks from the general mathematical audit. "
    "The repository and manuscript were read only; generated files and package symlinks are confined to this working directory.",
    "",
]
(root / "report.md").write_text("\n".join(lines))
print("Wrote the completed report and the eight verdicts in the requested leaf order.")
