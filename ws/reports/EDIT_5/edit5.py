#!/usr/bin/env python3
"""EDIT_5: apply the EDIT4_DELTA reviewer's exact replacements.

Each target is matched literally, with any run of whitespace in the target
allowed to match any run of whitespace in the file (line breaks may differ).
Every target must occur exactly once; otherwise nothing is written.
"""
import json
import re
import sys

ROOT = "/home/ubuntu/aklt/manuscript-v2/"

EDITS = [
    # (finding, file, old, new, delete_leading_ws)
    ("1 (sec8:9-11)", "sec8-inputs.tex",
     r"""The certificates consist of the finite
integer equalities, inequalities, and divisibility tests specified
below and in Appendix C, with positive rational denominators cleared.""",
     r"""The finite tests specified below and in Appendix C use integer
equalities, inequalities, and divisibility tests, with positive
rational denominators cleared.""", False),

    ("5 (sec8:21-22)", "sec8-inputs.tex",
     r"""The certificates are checked inside the
Lean kernel, not by external programs.""",
     r"""The certificate proofs are checked by the Lean kernel; external
programs generate and encode witness data.""", False),

    ("3 (sec8:22-27)", "sec8-inputs.tex",
     r"""The certificate for (H1)
covers all \(7962\) local patterns and their \(12173\) sector
blocks; its kernel check took about \(139\) CPU-hours. The
certificate for (H3\(_h\)) consists of \(5035\) generated modules;
its kernel check took about \(19.5\) CPU-hours. The kernel check
for (H2) took seconds.""",
     r"""The certificate for (H1) covers all \(7962\) local patterns and
their \(12173\) sector blocks; successful Lean builds of its
numerical certificate library used about \(139\) CPU-hours.
The production manifest for (H3\(_h\)) contains \(5032\) generated
modules and three hand-written bridge modules; successful Lean
builds of these modules used about \(19.5\) CPU-hours. The
exhaustive kernel computation for (H2) took about four minutes.""", False),

    ("4 (sec8:27-30)", "sec8-inputs.tex",
     r"""Everything in the formalization except the
certificates for (H1) and (H3\(_h\)), in particular the derivation
of Theorem~\ref{t:main} from the three inputs, has also been checked
by two independent implementations of the Lean kernel.""",
     r"""At commit~\texttt{63d176a}, the part of the formalization independent
of the (H1) and (H3\(_h\)) certificate proofs, including the
conditional derivation of Theorem~\ref{t:main} and the (H2) proof,
was also checked by con-ron and NanoDa, two independent
implementations of the Lean kernel. These rechecks exclude the
(H1) and (H3\(_h\)) certificate proofs and the subsequent closing
and packaging modules.""", False),

    ("1 (sec8:32-38)", "sec8-inputs.tex",
     r"""For the local input we use the archived representation and inversion
choices, and the division-free Gram/residual format wherever its
witness is available. For a block without a supplied nonzero Gram
factor which is not directly diagonally dominant, we use the
Bareiss fallback permitted by Lemma~\ref{l:integercheck}. The local
certificate consists of the coverage, reconstruction, and positivity
checks on these data specified below.""",
     r"""The local verification described below uses the archived
representation and inversion choices, the two supplied nonzero
Gram factors, and the Bareiss fallback permitted by
Lemma~\ref{l:integercheck}. The Lean certificate uses the same
patterns, choices, and reconstructed matrices, with zero Gram
factors for the \(8439\) directly dominant blocks and nonzero
Gram factors for all \(3734\) remaining blocks. It therefore
proves the same local input without running the numerical
Bareiss fallback.""", False),

    ("1 (sec8:139)", "sec8-inputs.tex",
     r"""These are the only two nonzero factors used.""",
     r"""These are the only two nonzero factors supplied in the original archive.""", False),

    ("2 (sec8:163-165, deletion)", "sec8-inputs.tex",
     r"""As an additional finite check,
all \(3734\) blocks failing the direct dominance test, including
the two with supplied nonzero factors, pass this fallback too.""",
     "", True),

    ("1 (sec8:181-182)", "sec8-inputs.tex",
     r"""The finite assertions specified above constitute
the local certificate, verified by the Lean kernel.""",
     r"""The finite assertions specified above constitute the archived local
verification. The accompanying Lean certificate proves the same
local input by the reconstructed-matrix Gram/residual checks
described at the beginning of this section.""", False),

    ("1 (sec8:331-336)", "sec8-inputs.tex",
     r"""The H1 calculation uses
the frozen representation and inversion records. Its residual
tests require all rows, and its fallback requires every division
exact and every pivot positive. The fallback discharges exactly
the blocks without supplied nonzero Gram factors, using the fixed
representation and inversion records.""",
     r"""The archived H1 calculation uses the frozen representation and
inversion records. Its residual tests require all rows, and its
fallback requires every division exact and every pivot positive.
The fallback discharges exactly the blocks without supplied
nonzero Gram factors, using the fixed representation and inversion
records. The Lean certificate uses Gram/residual witnesses for all
blocks and checks their mathematical reconstruction and coverage.""", False),

    ("1 (sec8:351-353)", "sec8-inputs.tex",
     r"""Each certificate is a proof of the
specified finite assertions, checked by the Lean kernel as described
at the beginning of this section.""",
     r"""Each Lean certificate proves its computational input from the
finite integer assertions used in that certificate, with the (H1)
witness format described at the beginning of this section.""", False),

    ("5 (app-input-contracts:16-18)", "app-input-contracts.tex",
     r"""These finite assertions are verified by proofs
checked by the Lean kernel, as described at the beginning of
Section~\ref{s:inputs}.""",
     r"""In Lean, the archived (H2) integer vector is expanded to all
\(916\) raw windows and checked directly, and the archived
(H3\(_h\)) automaton and stationary arrays are checked through
their literal encodings. The resulting proofs are checked by the
Lean kernel, as described at the beginning of Section~\ref{s:inputs}.""", False),
]


def pattern(old, delete_leading_ws):
    toks = old.split()
    pat = r"\s+".join(re.escape(t) for t in toks)
    if delete_leading_ws:
        pat = r"[ \t]+" + pat  # the sentence follows a space mid-line
    return re.compile(pat)


def main():
    texts = {}
    for _, f, _, _, _ in EDITS:
        if f not in texts:
            with open(ROOT + f, encoding="utf-8") as fh:
                texts[f] = fh.read()
    log = []
    failures = []
    # first pass: check every target exactly once against the original text
    for finding, f, old, new, dl in EDITS:
        n = len(pattern(old, dl).findall(texts[f]))
        if n != 1:
            failures.append((finding, f, n))
    if failures:
        for fnd, f, n in failures:
            print(f"TARGET NOT UNIQUE: finding {fnd} in {f}: {n} matches")
        sys.exit(1)
    # second pass: apply in order, re-asserting uniqueness each time
    for finding, f, old, new, dl in EDITS:
        p = pattern(old, dl)
        ms = list(p.finditer(texts[f]))
        assert len(ms) == 1, (finding, len(ms))
        m = ms[0]
        line = texts[f].count("\n", 0, m.start()) + 1
        texts[f] = texts[f][:m.start()] + new + texts[f][m.end():]
        log.append({"finding": finding, "file": f, "start_line": line,
                    "old": m.group(0), "new": new})
    for f, t in texts.items():
        with open(ROOT + f, "w", encoding="utf-8") as fh:
            fh.write(t)
    with open("/home/ubuntu/aklt/reports/EDIT_5/edits.json", "w") as fh:
        json.dump(log, fh, indent=1)
    for e in log:
        print(f"OK finding {e['finding']}: {e['file']} line {e['start_line']}")


if __name__ == "__main__":
    main()
