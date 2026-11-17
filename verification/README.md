# Local verification record — 2026-11-17

These are diagnostics of the unported architecture. They are not Palomar
acceptance, a clean source build, a populated package, or a production resource
receipt. The main report is
`/home/ubuntu/aklt/reports/ARCH_PKG/report.md`; raw logs and full exports live
outside the package in that report directory.

| Check | Result and boundary |
| --- | --- |
| `lake build AKLT.Final.Inputs` | PASS, with existing project and pinned dependency objects; 11.56 s. |
| Independent canonical Challenge | PASS, Mathlib-only trusted paths, under a verifier-generated random module alias; 572 lines / 26,735 bytes. One expected placeholder warning. |
| Final module-system Solution | BLOCKED by `cannot import non-module AKLT.Final.Inputs from module`; the tree port is pending. |
| Temporary legacy interface copy of Solution and Audit | PASS; only module/public interface commands were adapted, with every definition and proof body unchanged. |
| Every new exported theorem's axiom audit | PASS; the exact transcript is [axioms-compat.log](axioms-compat.log), checked by `scripts/check_axioms.py`. |
| Header/import inventory | PASS; Lean parsed all 11,380 source headers in the Solution graph. |
| Model package's unchanged Comparator script | Stops at its hard-coded, older verifier revision; it also selects that package's theorem names. |
| Direct export comparison | Stops at `AKLT.Defs.Compass.step`: modern and legacy elaboration select different matchers. Post-port comparison remains open. |
| Lean full-export replay | PASS, exit 0, about 239 s. |
| NanoDa full-export replay | PASS, exit 0, about 290 s; 65,738 declarations checked with no typechecker errors. One nonfatal pretty-printer diagnostic: “Unable to print axioms”. |
| Bundled rc2 con-ron replay | Allocation failure under the local 31 GiB address-space cap, about 237 s. No production classification follows. |
| Skeleton source/config check | Expected failure: 615 sources have not been copied, metadata TODOs remain and a release root license is missing. The three present package Lean files satisfy module/length rules. |

All five newly exported theorems use exactly `propext`, `Classical.choice` and
`Quot.sound`. The allowed axioms are also the complete axiom list in the proof
export. No H1/H3 certificate, CertData, H1C/H3C or H1M/H3M layer is imported or
occurs in that export.

The three standalone kernel diagnostics ran sequentially under a 31 GiB
**virtual-address** cap, without authenticated production cgroup supervision.
They check the full compatibility Solution proof export; they do not repair the
failed Challenge/Solution declaration comparison. The con-ron binary was the
selected rc2 toolchain's bundled binary, not the official verifier's separately
authenticated production checker update. An initial NanoDa harness call used
the wrong input format and failed before replay; the configured run above is
the relevant result. Both attempts are retained in the report directory.

The small `local-receipt.json` records exact selected commands, times, binary
hashes and source identities. No `.olean`, NDJSON export or other prebuilt proof
artifact is included in this skeleton. For a release, follow the materialization
and port instructions in [the package guide](../README.md), then repeat clean
verification against that actual source snapshot.
