#!/usr/bin/env python3
"""EDIT_4: remove certificate-pending markers and align verification-status wording."""
import pathlib
import sys

ROOT = pathlib.Path("/home/ubuntu/aklt/manuscript-v2")

EDITS = {
    "main.tex": [
        (
            "\\newcommand{\\certpending}[1]{\\textbf{[certificate check pending]}}\n",
            "",
        ),
        (
            "prefix sums. The accompanying formalization uses the Lean kernel\n"
            "to verify the finite certificate checks; pending checks are marked\n"
            "explicitly.\n",
            "prefix sums. The theorem, including these finite checks, has been\n"
            "formalized in Lean~4 and checked by the Lean kernel.\n",
        ),
    ],
    "sec1-result.tex": [
        (
            "inequalities and finite prefix sums. The accompanying formalization\n"
            "uses the Lean kernel to verify the finite certificate checks; pending\n"
            "checks are marked explicitly. The polynomial realization of the spin space,\n",
            "inequalities and finite prefix sums. Theorem~\\ref{t:main}, including\n"
            "the finite certificate checks for these inputs, has been formalized\n"
            "in Lean~4 and checked by the Lean kernel. Section~\\ref{s:inputs}\n"
            "describes the accompanying Lean formalization. % CHECK: add repository reference\n"
            "The polynomial realization of the spin space,\n",
        ),
    ],
    "sec8-inputs.tex": [
        (
            "\\section{Exact computational inputs}\n",
            "\\section{Exact computational inputs}\\label{s:inputs}\n",
        ),
        (
            "below and in Appendix C, with positive rational denominators cleared.\n"
            "The accompanying formalization uses proofs checked by the Lean\n"
            "kernel to verify these assertions. Each check whose kernel proof is\n"
            "pending is marked \\textbf{[certificate check pending]}. The soundness\n"
            "arguments prove deterministic implications from these finite assertions.\n",
            "below and in Appendix C, with positive rational denominators cleared.\n"
            "The soundness arguments prove deterministic implications from these\n"
            "finite assertions.\n"
            "\n"
            "Theorem~\\ref{t:main}, including the three inputs (H1), (H2), and\n"
            "(H3\\(_h\\)) and their certificates, has been formalized in Lean~4\n"
            "(version 4.35.0-rc2, with Mathlib) and checked by the Lean kernel.\n"
            "The accompanying Lean formalization % CHECK: add repository reference\n"
            "uses only the standard axioms \\texttt{propext},\n"
            "\\texttt{Classical.choice}, and \\texttt{Quot.sound}, and it does not\n"
            "use \\texttt{native\\_decide}. The certificates are checked inside the\n"
            "Lean kernel, not by external programs. The certificate for (H1)\n"
            "covers all \\(7962\\) local patterns and their \\(12173\\) sector\n"
            "blocks; its kernel check took about \\(139\\) CPU-hours. The\n"
            "certificate for (H3\\(_h\\)) consists of \\(5035\\) generated modules;\n"
            "its kernel check took about \\(19.5\\) CPU-hours. The kernel check\n"
            "for (H2) took seconds. Everything in the formalization except the\n"
            "certificates for (H1) and (H3\\(_h\\)), in particular the derivation\n"
            "of Theorem~\\ref{t:main} from the three inputs, has also been checked\n"
            "by two independent implementations of the Lean kernel.\n",
        ),
        ("\\certpending{h1-pattern-enumeration}\n", ""),
        ("\\certpending{h1-pattern-coverage}\n", ""),
        ("\\certpending{h1-sector-reconstruction}\n", ""),
        ("\\certpending{h1-direct-dominance}\n", ""),
        ("\\certpending{h1-gram-residual}\n", ""),
        ("\\certpending{h1-bareiss}\n", ""),
        (
            "arithmetic tests. The finite assertions specified above constitute\n"
            "the local certificate, verified by the Lean kernel in the accompanying\n"
            "formalization, with pending checks marked at their specifications.\n",
            "arithmetic tests. The finite assertions specified above constitute\n"
            "the local certificate, verified by the Lean kernel.\n",
        ),
        (
            "the prescribed comparisons. Each certificate is a proof of the\n"
            "specified finite assertions checked by the Lean kernel in the\n"
            "accompanying formalization. The placeholders identify the pending\n"
            "kernel checks. None of these arguments assumes a physical window\n"
            "estimate, a frame finite-energy bound, or a spectral-gap conclusion.\n",
            "the prescribed comparisons. Each certificate is a proof of the\n"
            "specified finite assertions, checked by the Lean kernel as described\n"
            "at the beginning of this section. None of these arguments assumes\n"
            "a physical window estimate, a frame finite-energy bound, or a\n"
            "spectral-gap conclusion.\n",
        ),
    ],
    "app-input-contracts.tex": [
        (
            "of those checks. The accompanying formalization verifies these finite\n"
            "assertions by proofs checked by the Lean kernel; pending checks are\n"
            "marked at their full arithmetic specifications. An executable's exit\n",
            "of those checks. These finite assertions are verified by proofs\n"
            "checked by the Lean kernel, as described at the beginning of\n"
            "Section~\\ref{s:inputs}. An executable's exit\n",
        ),
        (
            "without repetition, and their integer values are positive.\n"
            "\\certpending{h2-vector-indexing}\n"
            "Every regenerated row satisfies the displayed integer inequality.\n"
            "\\certpending{h2-row-inequalities}\n",
            "without repetition; their integer values are positive; and every\n"
            "regenerated row satisfies the displayed integer inequality.\n",
        ),
        ("\\certpending{h2-vector-extrema}\n", ""),
        ("\\certpending{h2-maximizing-row}\n", ""),
        ("\\certpending{h3-window-enumeration}\n", ""),
        ("\\certpending{h3-quotient-indexing}\n", ""),
        ("\\certpending{h3-quotient-transitions}\n", ""),
        ("\\certpending{h3-transition-ceilings}\n", ""),
        (
            "check with the displayed constants. \\certpending{h3-prefix-denominator}\n"
            "Multiplying phase weights by\n",
            "check with the displayed constants. Multiplying phase weights by\n",
        ),
        ("\\certpending{h3-array-indexing}\n", ""),
        (
            "bounds. \\certpending{h3-free-rows}\n"
            "For each of the \\(4\\cdot3741\\cdot19881\\) stored\n"
            "phase/class/site indices, require \\(0\\le U\\le Z\\) and the specified\n"
            "center and target equalities. \\certpending{h3-caps-and-terminals}\n"
            "Require the nonterminal stationary row inequality when appropriate.\n"
            "The coefficients are regenerated\n",
            "bounds. For each of the \\(4\\cdot3741\\cdot19881\\) stored\n"
            "phase/class/site indices, require \\(0\\le U\\le Z\\), the specified\n"
            "center and target equalities, and the nonterminal stationary row\n"
            "inequality when appropriate. The coefficients are regenerated\n",
        ),
        ("\\certpending{h3-local-rows}\n", ""),
        ("\\certpending{h3-prefix-enumeration}\n", ""),
        (
            "rounding convention. \\certpending{h3-prefix-values}\n"
            "A compact lookup is accepted only with the\n"
            "entry-by-entry identity with the full potential described after\n"
            "Definition~\\ref{d:prefix-bound}.\n"
            "\\certpending{h3-prefix-lookup}\n",
            "rounding convention. A compact lookup is accepted only with the\n"
            "entry-by-entry identity with the full potential described after\n"
            "Definition~\\ref{d:prefix-bound}.\n",
        ),
        (
            "constitute the stationary certificates. Their proofs are checked by\n"
            "the Lean kernel in the accompanying formalization, with pending\n"
            "checks marked above.\n",
            "constitute the stationary certificates. Their proofs are checked by\n"
            "the Lean kernel.\n",
        ),
    ],
}


def main():
    new_texts = {}
    for name, edits in EDITS.items():
        path = ROOT / name
        text = path.read_text()
        for old, new in edits:
            count = text.count(old)
            if count != 1:
                sys.exit(f"{name}: expected exactly one occurrence, found {count}:\n{old}")
            text = text.replace(old, new)
        new_texts[name] = text
    for name, text in new_texts.items():
        (ROOT / name).write_text(text)
        print(f"edited {name}: {len(EDITS[name])} replacements")


if __name__ == "__main__":
    main()
