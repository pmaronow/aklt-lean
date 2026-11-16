#!/usr/bin/env python3
"""Generate Main.lean when complete, or Conditional.lean from all leaf proofs.

Run from any directory. Missing proofs give exit status 1; invalid configuration
or failed Lean checks give status 2. Main.lean is replaced only after validation.
--conditional instead writes a theorem with exactly four certificate arguments;
build it with `lake build AKLT.Final.Conditional` to recheck all 416 leaf terms.
The active leaf map, not its scheduler's state field, determines membership.
Only project modules are compiled, sequentially; prebuilt external libraries
are imported without invoking their build systems.

Optional --proofs JSON (a filename or an inline object) maps a leaf key,
hypothesis name, or statement name to
{"module": "AKLT.Cert.H1.Main", "term": "AKLT.Cert.H1.certificate"}.
The four certificate statement names may be short or fully qualified. Values
may also be qualified proof names, with their module discovered from the tree.
Terms may also be projections such as "(AKLT.Cert.H1.main).1". Without overrides,
the script discovers the canonical W proofs and directly typed declarations.
It also splits a directly typed Top.CertificateStatementV2 proof automatically.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
DEFAULT_ROOT = HERE.parent.parent
DEFAULT_LEAVES = Path("/home/ubuntu/aklt/state/lw/leaves.json")
PARTS = {"Q", "GAP", "WIN", "MOM", "REC", "H1M", "H3M"}
TOP = "AKLT.Blueprint.Top."
EXTRA = {
    TOP + "CertificateStatement": ("certificate", "H1"),
    TOP + "Automaton10StatementV2": ("certificate", "H3"),
    TOP + "StationaryCheckStatementV2": ("certificate", "H3"),
}
CERTIFICATES = (
    TOP + "H1FiniteDataStatementV2",
    TOP + "CertificateStatement",
    TOP + "Automaton10StatementV2",
    TOP + "StationaryCheckStatementV2",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
TERM = re.compile(rf"(?:{NAME}|\({NAME}\))(?:\.[12])*")


def strip_comments(text: str) -> str:
    """Remove nested Lean comments while preserving line boundaries."""
    result, depth, i = [], 0, 0
    while i < len(text):
        pair = text[i:i + 2]
        if pair == "/-":
            depth += 1
            result.append("  ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            result.append("  ")
            i += 2
        elif depth:
            result.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                break
            result.append(" " * (end - i))
            i = end
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unterminated Lean block comment")
    return "".join(result)


def read_contract(root: Path, leaves_path: Path) -> tuple[list[dict], dict]:
    leaves = json.loads(leaves_path.read_text())
    active = {
        key: item for key, item in leaves.items()
        if item["part"] in PARTS
        and item.get("state") not in {"superseded", "retired", "obsolete"}
        and not item.get("superseded_by")
    }
    if len({item["node"] for item in active.values()}) != len(active):
        raise ValueError("Duplicate statement names in active leaf map")
    source = (root / "AKLT/Final/Skeleton.lean").read_text()
    clean = strip_comments(source)
    match = re.search(
        r"theorem mainV2_of_open\s+(.*?)\s*:\s*"
        r"AKLT\.Challenge\.MainStatementV2\s*:=\s*by\b", clean, re.S
    )
    if not match:
        raise ValueError("Cannot read mainV2_of_open's explicit signature")
    signature = match[1]
    binder = re.compile(rf"\((h\w+)\s*:\s*({NAME})\)")
    if binder.sub("", signature).strip():
        raise ValueError("Unrecognized or dependent hypothesis in Skeleton.lean")
    by_node = {item["node"]: (key, item) for key, item in active.items()}
    hypotheses, seen = [], set()
    body = clean[match.end():]
    for position, (parameter, name) in enumerate(binder.findall(signature), 1):
        if name in seen:
            raise ValueError(f"Duplicate hypothesis: {name}")
        seen.add(name)
        row = {
            "position": position, "parameter": parameter, "lean_name": name,
            "referenced_in_assembly_body": bool(re.search(rf"\b{parameter}\b", body)),
        }
        if name in by_node:
            key, item = by_node[name]
            row.update(
                key=key, kind="certificate" if name == TOP + "H1FiniteDataStatementV2" else "leaf",
                part={"GAP": "Gap", "WIN": "Win", "MOM": "Mom", "REC": "Rec",
                      "H1M": "H1", "H3M": "H3"}.get(item["part"], item["part"]),
                statement_module=item["module"], scheduler_state=item.get("state"),
            )
        elif name in EXTRA:
            kind, part = EXTRA[name]
            row.update(key=None, kind=kind, part=part, statement_module=(
                "AKLT.Blueprint.Top.Operator" if part == "H1"
                else "AKLT.Blueprint.Top.ComputationV2"
            ))
        elif name.startswith("AKLT.Final.Bridge_"):
            row.update(key=None, kind="bridge", part="Final", statement_module="AKLT.Final.Skeleton")
        else:
            raise ValueError(f"Unexpected non-leaf hypothesis: {name}")
        hypotheses.append(row)
    missing = set(by_node) - seen
    if missing:
        raise ValueError("Leaf map changed; revise Skeleton.lean before generating: "
                         + ", ".join(sorted(missing)))
    if not set(EXTRA) <= seen:
        raise ValueError("Skeleton.lean is missing a designated certificate contract")
    return hypotheses, {
        "leaf_map": str(leaves_path),
        "leaf_map_sha256": hashlib.sha256(leaves_path.read_bytes()).hexdigest(),
        "skeleton_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "active_mapped_obligations": len(active),
    }


def declarations(root: Path):
    """Find public, closed declarations with a directly named statement type.

    This is discovery, not a replacement for elaboration. Lean checks every
    selected term, including aliases and the disambiguation of short names.
    """
    event = re.compile(
        rf"^[ \t]*(?:namespace\s+(?P<namespace>{NAME})|"
        r"(?P<section>(?:noncomputable\s+)?section)\b|(?P<end>end)\b|"
        rf"(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+"
        rf"(?P<decl>{NAME})\s*:\s*(?P<type>{NAME})\s*(?::=|where))", re.M
    )
    for path in sorted((root / "AKLT").rglob("*.lean")):
        if root / "AKLT/Final" in path.parents:
            continue
        text = strip_comments(path.read_text())
        stack = []
        for match in event.finditer(text):
            if match["namespace"]:
                stack.append(match["namespace"])
            elif match["section"]:
                stack.append("")
            elif match["end"]:
                if stack:
                    stack.pop()
            elif match["decl"]:
                namespace = ".".join(part for part in stack if part)
                name = match["decl"]
                name = name.removeprefix("_root_.") if name.startswith("_root_.") else (
                    namespace + "." + name if namespace else name
                )
                yield {
                    "module": ".".join(path.relative_to(root).with_suffix("").parts),
                    "term": name, "declared_type": match["type"],
                    "source": str(path.relative_to(root)),
                }


def discover(root: Path, hypotheses: list[dict], overrides: dict) -> None:
    wanted = {row["lean_name"] for row in hypotheses}
    candidates = {name: [] for name in wanted}
    combined = TOP + "CertificateStatementV2"
    public_proofs = list(declarations(root))
    modules_by_name = {proof["term"]: proof["module"] for proof in public_proofs}
    aliases = {name.removeprefix(TOP): name for name in CERTIFICATES}
    normalized = {}
    for key, value in overrides.items():
        key = aliases.get(key, key)
        if key in normalized:
            raise ValueError(f"Duplicate proof override for {key}")
        if isinstance(value, str):
            if not TERM.fullmatch(value):
                raise ValueError("Proof overrides must be closed declaration names/projections")
            name = re.search(NAME, value)[0]
            module = modules_by_name.get(name)
            if module is None:
                raise ValueError(f"Cannot find the module declaring {name}; use an explicit module/term object")
            value = {"module": module, "term": value}
        normalized[key] = value
    overrides = normalized
    for proof in public_proofs:
        declared = proof["declared_type"]
        matches = [name for name in wanted | {combined}
                   if name == declared or name.endswith("." + declared)]
        # Ambiguous short types require an explicit override.
        if len(matches) != 1:
            continue
        target = matches[0]
        if target == combined:
            for name, projection in [(TOP + "CertificateStatement", 1),
                                     (TOP + "H1FiniteDataStatementV2", 2)]:
                if name in candidates:
                    candidates[name].append(dict(proof, term=f"({proof['term']}).{projection}"))
        else:
            candidates[target].append(proof)
    unused_overrides = set(overrides)
    for row in hypotheses:
        options = candidates[row["lean_name"]]
        canonical = f"AKLT.W.{row['key']}.main" if row["key"] else None
        options.sort(key=lambda item: (item["term"] != canonical, item["term"]))
        keys = [key for key in [row["key"], row["parameter"], row["lean_name"]] if key in overrides]
        if len(keys) > 1:
            raise ValueError(f"Multiple proof overrides for {row['lean_name']}")
        if keys:
            unused_overrides.remove(keys[0])
            proof = overrides[keys[0]]
            if not isinstance(proof, dict) or not isinstance(proof.get("module"), str) or not isinstance(proof.get("term"), str):
                raise ValueError(f"Invalid override for {keys[0]}")
            if not re.fullmatch(NAME, proof["module"]) or not TERM.fullmatch(proof["term"]):
                raise ValueError("Overrides must use a module and a closed declaration/projection")
            source = Path(*proof["module"].split(".")).with_suffix(".lean")
            if not proof["module"].startswith("AKLT.") or not (root / source).is_file():
                raise ValueError(f"Project proof source does not exist: {source}")
            if proof["module"].startswith("AKLT.Final.") and row["kind"] != "bridge":
                raise ValueError("Final modules cannot supply leaf/certificate overrides")
            options = [dict(proof, source=str(source), declared_type=None)]
        row["proof_exists"] = bool(options)
        row["proof_status"] = "source_found_not_rechecked" if options else "missing"
        row["proof_candidates"] = options
        row["proof"] = options[0] if options else None
    if unused_overrides:
        raise ValueError("Unknown proof overrides: " + ", ".join(sorted(unused_overrides)))


def render(hypotheses: list[dict]) -> str:
    modules = sorted({row["proof"]["module"] for row in hypotheses})
    imports = ["AKLT.Final.Skeleton"] + [m for m in modules if m != "AKLT.Final.Skeleton"]
    return "\n".join([
        *("import " + module for module in imports), "",
        "/-! Generated by gen_final.py after Lean type and dependency checks. -/",
        "namespace AKLT.Final", "",
        "theorem main : AKLT.Challenge.MainStatementV2 :=", "  mainV2_of_open",
        *(f"    ({row['proof']['term']})" for row in hypotheses), "",
        "#print axioms main", "", "end AKLT.Final", "",
    ])


def conditional_arguments(hypotheses: list[dict]) -> list[dict]:
    """Fix exactly the certificate boundary and canonical W leaf terms."""
    certificates = [row for row in hypotheses if row["kind"] == "certificate"]
    if tuple(row["lean_name"] for row in certificates) != CERTIFICATES:
        raise ValueError("Conditional generation requires exactly the four certificates in skeleton order")
    if any(row["kind"] not in {"leaf", "certificate"} for row in hypotheses):
        raise ValueError("Conditional generation cannot leave any bridge assumption")
    result = []
    for row in hypotheses:
        row = dict(row)
        if row["kind"] == "leaf":
            canonical = f"AKLT.W.{row['key']}.main"
            proof = next((candidate for candidate in row["proof_candidates"]
                          if candidate["term"] == canonical), None)
            row["proof"] = proof
            row["proof_exists"] = proof is not None
        result.append(row)
    return result


def render_conditional(hypotheses: list[dict]) -> str:
    leaves = [row for row in hypotheses if row["kind"] == "leaf"]
    certificates = [row for row in hypotheses if row["kind"] == "certificate"]
    modules = sorted({row["proof"]["module"] for row in leaves})
    return "\n".join([
        "import AKLT.Final.Skeleton",
        *("import " + module for module in modules), "",
        "/-! Generated by gen_final.py --conditional. Building this application",
        f"checks all {len(leaves)} distinct canonical leaf terms against the skeleton.",
        "Exactly the four certificate contracts remain as hypotheses. -/", "",
        "namespace AKLT.Final", "",
        "/-- The headline from the four remaining certificate contracts. -/",
        "theorem main_of_certificates",
        *(f"    ({row['parameter']} : {row['lean_name']})" for row in certificates),
        "    : AKLT.Challenge.MainStatementV2 :=", "  mainV2_of_open",
        *(f"    ({row['proof']['term']})" if row["kind"] == "leaf"
          else f"    {row['parameter']}" for row in hypotheses), "",
        "#print axioms main_of_certificates", "", "end AKLT.Final", "",
    ])


def write_generated(destination: Path, source: str) -> None:
    descriptor, filename = tempfile.mkstemp(prefix=destination.stem + "Pending",
                                           suffix=".lean", dir=destination.parent)
    try:
        with os.fdopen(descriptor, "w") as stream:
            stream.write(source)
        os.replace(filename, destination)
    finally:
        Path(filename).unlink(missing_ok=True)


def command(root: Path, args: list[str]) -> str:
    environment = os.environ.copy()
    environment["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + environment.get("PATH", "")
    process = subprocess.run(args, cwd=root, env=environment, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if process.returncode:
        raise RuntimeError("Command failed: " + " ".join(args) + "\n" + process.stdout)
    return process.stdout


def check_dependencies(output: str) -> None:
    for axioms in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output):
        found = {name.strip() for name in axioms.split(",") if name.strip()}
        if found - ALLOWED_AXIOMS:
            raise RuntimeError("Disallowed proof dependencies: " + ", ".join(sorted(found - ALLOWED_AXIOMS)))


def validate(root: Path, hypotheses: list[dict], source: str) -> str:
    roots = {row["proof"]["module"] for row in hypotheses} | {"AKLT.Final.Skeleton"}
    visited, visiting = set(), set()

    def build(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise ValueError(f"Cyclic project imports involving {module}")
        path = root / Path(*module.split(".")).with_suffix(".lean")
        target = root / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
        if not path.is_file():
            raise ValueError(f"Missing project module: {path}")
        visiting.add(module)
        rebuild = module in roots or not target.is_file()
        # Existing non-root artifacts are the campaign's prebuilt dependencies.
        # Only AKLT imports are visited; external packages are never built.
        if rebuild:
            for line in strip_comments(path.read_text()).splitlines():
                match = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)", line)
                if match:
                    for dependency in match[1].split():
                        if dependency.startswith("AKLT."):
                            build(dependency)
            target.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {module}", flush=True)
            output = command(root, ["lake", "env", "lean", "-DautoImplicit=false",
                                   "-DrelaxedAutoImplicit=false", "-o", str(target), str(path)])
            check_dependencies(output)
        visiting.remove(module)
        visited.add(module)

    for module in sorted(roots):
        build(module)
    proof_names = sorted({re.search(NAME, row["proof"]["term"])[0] for row in hypotheses})
    audit = source + "\n" + "\n".join("#print axioms " + name for name in proof_names) + "\n"
    descriptor, filename = tempfile.mkstemp(prefix="CheckFinal", suffix=".lean", dir=root / "AKLT/Final")
    try:
        with os.fdopen(descriptor, "w") as stream:
            stream.write(audit)
        output = command(root, ["lake", "env", "lean", "-DautoImplicit=false",
                               "-DrelaxedAutoImplicit=false", filename])
        if "'AKLT.Final.main' depends on axioms:" not in output and "'AKLT.Final.main' does not depend on any axioms" not in output:
            raise RuntimeError("Lean did not print the generated theorem's dependencies")
        check_dependencies(output)
        return output
    finally:
        Path(filename).unlink(missing_ok=True)


def write_inventory(path: Path, hypotheses: list[dict], metadata: dict) -> None:
    counts = Counter({"leaf": 0, "certificate": 0, "bridge": 0})
    counts.update(row["kind"] for row in hypotheses)
    data = dict(metadata, schema_version=1, theorem="AKLT.Final.mainV2_of_open",
                generated_at=datetime.now(timezone.utc).isoformat(),
                counts=dict(counts, total=len(hypotheses),
                            proof_exists=sum(row["proof_exists"] for row in hypotheses),
                            missing=sum(not row["proof_exists"] for row in hypotheses)),
                hypotheses=hypotheses)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    parser.add_argument("--leaves", type=Path, default=DEFAULT_LEAVES)
    parser.add_argument("--proofs", help="Named proof overrides: JSON filename or inline JSON object")
    parser.add_argument("--inventory", type=Path, help="Write or refresh the hypothesis inventory here")
    parser.add_argument("--check-only", action="store_true", help="Inventory and list missing proofs; never write a Lean file")
    parser.add_argument("--conditional", action="store_true", help="Write Conditional.lean with the four certificate hypotheses")
    args = parser.parse_args()
    root = args.root.resolve()
    hypotheses, metadata = read_contract(root, args.leaves.resolve())
    overrides = (json.loads(args.proofs if args.proofs.lstrip().startswith("{")
                            else Path(args.proofs).read_text()) if args.proofs else {})
    if not isinstance(overrides, dict):
        raise ValueError("--proofs must contain a JSON object")
    discover(root, hypotheses, overrides)
    if args.conditional:
        hypotheses = conditional_arguments(hypotheses)
    if args.inventory:
        write_inventory(args.inventory.resolve(), hypotheses, metadata)
    missing = [row for row in hypotheses if not row["proof_exists"]
               and (not args.conditional or row["kind"] != "certificate")]
    if missing:
        print(f"Missing {len(missing)} of {len(hypotheses)} hypotheses:")
        for row in missing:
            key = row["key"] or row["parameter"]
            print(f"  {key} [{row['kind']}, {row['part']}]: {row['lean_name']}")
        destination = "Conditional.lean" if args.conditional else "Main.lean"
        print(f"{destination} was not written. Source-found proofs have not been rechecked by this run.")
        return 1
    if args.conditional:
        leaves = [row for row in hypotheses if row["kind"] == "leaf"]
        if args.check_only:
            print(f"All {len(leaves)} canonical leaf sources found; exactly four certificates remain as hypotheses.")
            return 0
        destination = root / "AKLT/Final/Conditional.lean"
        write_generated(destination, render_conditional(hypotheses))
        print(f"Wrote {destination} using {len(leaves)} distinct canonical leaf theorems and four certificate hypotheses.")
        print("Recheck every leaf term by building: lake build AKLT.Final.Conditional")
        return 0
    if args.check_only:
        print(f"All {len(hypotheses)} proof sources found; run without --check-only for Lean validation and generation.")
        return 0
    source = render(hypotheses)
    output = validate(root, hypotheses, source)
    for row in hypotheses:
        row["proof_status"] = "lean_checked"
    if args.inventory:
        write_inventory(args.inventory.resolve(), hypotheses, metadata)
    destination = root / "AKLT/Final/Main.lean"
    write_generated(destination, source)
    for line in output.splitlines():
        if line.startswith("'AKLT.Final.main'"):
            print(line)
    print(f"Wrote {destination} using {len(hypotheses)} checked proofs.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as error:
        print(f"gen_final.py: {error}", file=sys.stderr)
        sys.exit(2)
