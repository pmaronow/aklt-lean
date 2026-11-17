#!/usr/bin/env python3
"""Reproducible statement, interface, and exact-arithmetic checks for REV_A2."""

from fractions import Fraction
from math import factorial
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent
PLAN = ROOT.parent / "REV-PLAN" / "PLAN.md"
SECTION_LABELS = [
    "d:shells", "d:W", "l:stopped", "p:surgery", "l:hamming",
    "t:periodic", "t:mainW",
]
APPENDIX_LABELS = [
    "l:CE", "l:finitecoupling", "l:surgery", "l:density",
    "l:comparison", "l:contraction",
]
LABELS = SECTION_LABELS + APPENDIX_LABELS
EXTERNAL = {
    "d:frame", "d:framemodel", "l:boxlift", "l:colour", "l:planeenergy",
    "l:shellgeom", "l:star", "l:threeframes", "p:toruskernel", "t:QD",
    "t:cutMOS", "t:inputs", "t:main", "t:rec",
}
CROSS_LANE = {"l:shellgeom", "t:cutMOS", "t:inputs", "t:rec"}
ALLOWED_CROSS_LANE = {
    "l:moments", "t:inputs", "t:rec", "l:shellgeom", "t:cutMOS",
}


def check_statements():
    plan = PLAN.read_text()
    blocks = {}
    for block in re.findall(r"```latex\n(.*?)\n```", plan, re.S):
        match = re.search(r"\\label\{([^}]+)\}", block)
        if match and match.group(1) in LABELS:
            blocks[match.group(1)] = block
    section = (ROOT / "sec4-periodic-gap.tex").read_text()
    appendix = (ROOT / "app-finite.tex").read_text()
    combined = section + "\n" + appendix
    assert set(blocks) == set(LABELS)
    for label in LABELS:
        assert combined.count("\\label{" + label + "}") == 1, label
        assert blocks[label] in combined, label
    for source, labels in ((section, SECTION_LABELS), (appendix, APPENDIX_LABELS)):
        positions = [source.index("\\label{" + label + "}") for label in labels]
        assert positions == sorted(positions)
    assert len(re.findall(r"\\begin\{proof\}", section)) == 6
    assert len(re.findall(r"\\begin\{proof\}", appendix)) == 6
    assert "% PROOF" not in combined
    refs = set(re.findall(r"\\(?:ref|eqref)\{([^}]+)\}", combined))
    local = set(re.findall(r"\\label\{([^}]+)\}", combined))
    assert refs - local == EXTERNAL
    assert CROSS_LANE <= ALLOWED_CROSS_LANE
    print("PASS: 13 verbatim statement environments in plan order; 12 proofs.")
    print("PASS: external labels match the declared interface imports.")


def check_geometry_and_constants():
    cases = 0
    for radius in range(1, 9):
        # Include the smallest allowed periods and each parity combination.
        for dl in (0, 1):
            for dn in (0, 1):
                period_l = 2 * radius + 3 + dl
                period_n = 2 * radius + 3 + dn
                containing = near = 0
                for ax in range(period_l):
                    for ay in range(period_n):
                        square = {
                            ((ax + dx) % period_l, (ay + dy) % period_n)
                            for dx in range(-radius, radius + 1)
                            for dy in range(-radius, radius + 1)
                        }
                        assert len(square) == (2 * radius + 1) ** 2
                        if (0, 0) in square:
                            containing += 1
                        else:
                            distance = min(
                                max(min(x, period_l - x), min(y, period_n - y))
                                for x, y in square
                            )
                            near += distance == 1
                t = (2 * radius + 1) ** 2
                s = 8 * radius + 8
                assert containing == t
                assert near == s
                assert Fraction(s * radius, 1000 * t) < Fraction(1, 500)
                cases += 1
    print(f"PASS: direct periodic placement enumeration in {cases} cases.")

    for n in (44, 45, 224):
        for d in (Fraction(1, 2), Fraction(1, 3), Fraction(1, 10), Fraction(1, 100)):
            assert (1 - d) ** (n - 3) <= Fraction(2 ** 20 * factorial(20), n ** 20) / d ** 20
    # Exact rational normalizations used after the geometric estimate.
    assert Fraction(1, 2) * Fraction(499, 500) == Fraction(499, 1000)
    assert 25 * 2000 == 50000
    for n in (44, 45, 224):
        assert n - 22 >= Fraction(n, 2)
    print("PASS: exact tail-inequality samples and normalization identities.")


def check_same_lane_contracts():
    """Audit the six contracts absent from the referee's restricted bundle."""
    plan_blocks = {}
    for block in re.findall(r"```latex\n(.*?)\n```", PLAN.read_text(), re.S):
        match = re.search(r"\\label\{([^}]+)\}", block)
        if match:
            plan_blocks[match.group(1)] = block
    quantum = ROOT.parent / "REV_A1" / "sec3-quantum-frames.tex"
    result = ROOT.parent / "REV_A1" / "sec1-result.tex"
    for label in ("l:star", "t:QD", "p:toruskernel", "l:colour", "l:boxlift", "t:main"):
        source_path = result if label == "t:main" else quantum
        source = source_path.read_text()
        block = plan_blocks[label]
        assert block in source, (label, source_path)
        assert source.count("\\label{" + label + "}") == 1, label
        if label != "t:main":
            remainder = source[source.index(block) + len(block):].lstrip()
            assert remainder.startswith("\\begin{proof}"), label
    print("PASS: six referee-flagged contracts match PLAN.md in their Lane A files;")
    print("      all five imported results have proofs there, and the main target is stated.")


def check_wrapper_and_log():
    baseline = Path("/home/ubuntu/aklt/manuscript-corrected/main.tex").read_text()
    wrapper = (ROOT / "check.tex").read_text()
    assert wrapper.split("\\begin{document}")[0] == baseline.split("\\begin{document}")[0]
    log_path = ROOT / "check.log"
    if log_path.exists():
        log = log_path.read_text()
        assert "Output written on check.pdf" in log
        assert "Overfull" not in log
        assert "Underfull" not in log
        assert "multiply defined" not in log
        assert "Label(s) may have changed" not in log
        assert not any(line.startswith("!") for line in log.splitlines())
        undefined = set(re.findall(r"LaTeX Warning: Reference `([^']+)'", log))
        assert undefined == EXTERNAL, sorted(undefined)
        print("PASS: amsart compile; only the 14 expected external labels are undefined.")
    print("PASS: wrapper uses the unchanged baseline macro preamble.")


if __name__ == "__main__":
    check_statements()
    check_same_lane_contracts()
    check_geometry_and_constants()
    check_wrapper_and_log()
