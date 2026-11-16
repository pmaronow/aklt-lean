"""Round 2 generator contract checks; no campaign proof is constructed here."""

import copy
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("gen_final", HERE / "gen_final.py")
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)


def rejects(function, *args):
    try:
        function(*args)
    except (ValueError, RuntimeError):
        return
    raise AssertionError("Expected rejection")


root = HERE.parent.parent
rows, _ = gen.read_contract(root, gen.DEFAULT_LEAVES)
gen.discover(root, rows, {})
assert len(rows) == 420
assert sum(row["kind"] == "leaf" for row in rows) == 416
assert [row["lean_name"] for row in rows if not row["proof_exists"]] == list(gen.CERTIFICATES)
conditional = gen.conditional_arguments(rows)
source = gen.render_conditional(conditional)
assert source == (HERE / "Conditional.lean").read_text()
assert len(re.findall(r"^theorem ", source, re.M)) == 1
names = re.findall(r"\(AKLT\.W\.([A-Z0-9]+)\.main\)", source)
assert len(names) == len(set(names)) == 416
header, application = source.split("  mainV2_of_open\n", 1)
certificates = re.findall(r"\((h\w+) : (AKLT\.Blueprint\.Top\.\w+)\)", header)
assert [name for _, name in certificates] == list(gen.CERTIFICATES)
arguments = application.split("\n\n#print", 1)[0].splitlines()
assert len(arguments) == 420
for row, argument in zip(rows, arguments):
    expected = (f"(AKLT.W.{row['key']}.main)" if row["kind"] == "leaf" else row["parameter"])
    assert argument.strip() == expected
print("PASS: 416 distinct canonical proofs, exactly four ordered certificates, all 420 argument positions")

missing = copy.deepcopy(rows)
missing[0]["proof_candidates"] = []
assert not gen.conditional_arguments(missing)[0]["proof_exists"]
changed = copy.deepcopy(rows)
changed[-1]["kind"] = "bridge"
rejects(gen.conditional_arguments, changed)
print("PASS: missing canonical leaf and unexpected bridge are rejected")

# Qualified names below deliberately have the wrong certificate types. Discovery
# accepts named terms; final Lean validation, rather than discovery, checks types.
# This tests all four override names without inventing a certificate proof.
named = {name.removeprefix(gen.TOP): "AKLT.W.Q001.main" for name in gen.CERTIFICATES}
overridden = copy.deepcopy(rows)
gen.discover(root, overridden, named)
for row in overridden:
    if row["kind"] == "certificate":
        assert row["proof"]["module"] == "AKLT.W.Q001.Main"
        assert row["proof"]["term"] == "AKLT.W.Q001.main"
main = gen.render(overridden)
assert "theorem main : AKLT.Challenge.MainStatementV2 :=" in main
assert sum(line.strip() == "(AKLT.W.Q001.main)" for line in main.splitlines()) == 5
assert not (HERE / "Main.lean").exists()
rejects(gen.discover, root, copy.deepcopy(rows), {
    "CertificateStatement": "AKLT.W.Q001.main",
    gen.TOP + "CertificateStatement": "AKLT.W.Q001.main",
})
rejects(gen.discover, root, copy.deepcopy(rows), {"CertificateStatement": "by trivial"})
gen.discover(root, copy.deepcopy(rows), {
    "Q001": {"module": "AKLT.W.Q001.Main", "term": "AKLT.W.Q001.main"},
})
print("PASS: all four named certificate overrides, Main rendering, legacy override objects, invalid/duplicate rejection")

gen.check_dependencies("'t' depends on axioms: [propext, Classical.choice, Quot.sound]")
rejects(gen.check_dependencies, "'t' depends on axioms: [propext, sorryAx]")
print("PASS: dependency allowlist")
print("All round 2 generator tests passed; Main.lean remains absent.")
