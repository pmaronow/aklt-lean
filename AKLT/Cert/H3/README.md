# Stationary H3 production certificates

The executable code is in `CertData/H3/Kernel/Production/{Model,Replay,Batching}.lean`.
Generated literals, checks and data-dependent assemblies are in the optional
`CertData` Lake library. No `AKLT/` Lean module imports generated `CertData` code.
The default Lake target remains `AKLT`.

The canonical report is `/home/ubuntu/aklt/reports/CERT_H3/report.md`; the exact
closed writer statements are in its `leaves.json`. Mathematical soundness leaves
are intentionally unproved under the author's cheaper-model first-attempt rule.
All new written proofs here are assemblies; finite computations use
`decide +kernel`. The original 51 phase-1 proofs are preserved.

The five supported tags are B1=(B,north), B2=(B,west), C1=(C,north),
C2=(C,west), C3=(C,south). Every archive is read in full, with header, length,
endianness, gzip CRC/EOF and exact-prefix reference checks. A case has 14,964
80-bit spatial planes, 234 plane modules, 234 endpoint modules, 234 row checks,
and 256 depth-eight prefix batches. The endpoint rectangle stores both parities.
The prefix checker replays every code slot at the frontier and checks early
closed paths separately. It does not trust a list of surviving frontier states.

From this worktree, generate all finite work:

```sh
python3 AKLT/Cert/H3/production.py generate --cases B1 B2 C1 C2 C3
```

The script enters the pinned Lake environment automatically. It reads prebuilt
Mathlib and project dependencies; it never builds or updates packages. Revised
Defs/Top oleans are frozen under
`/home/ubuntu/aklt/scratch/CERT_H3/dependencies`, with a SHA manifest under the
report's `phase2/dependencies.json`. Pin mismatches abort. Merge the final ARCH_0
statement sources before using ordinary Lake builds of these modules in another
checkout; the timed runner already uses the isolated repaired import root.

Build a full case, using the measured pilot limits:

```sh
python3 AKLT/Cert/H3/production.py build --cases B1 --jobs 24 --ram-gb 270 --process-gib 40
```

For the full production run, use source compaction to stay below the 60 GB disk
budget:

```sh
python3 AKLT/Cert/H3/production.py build --cases B1 B2 C1 C2 C3 --jobs 24 --ram-gb 270 --process-gib 40 --resume --compact-sources
```

The scheduler completes earlier cases first. Once a case assembly is checked,
compaction records hashes and deletes only that case's plane/endpoint literal
`.lean` files. It keeps all checked `.olean` files, check sources, caps, indexes,
and assembly sources. The kernel imports checked oleans without the literal
sources. Regenerate a compacted case with `generate --cases TAG` whenever its
literal sources are needed again. The independent command
`compact --cases TAG` applies the same completed-case checks. Compaction does
not delete the archive, exporter, mathematical statements or proofs.

`--resume` rejects stale source, core or dependency timestamps. Compacted inputs
also require their recorded olean hashes. The process cap defaults to 24; the
runner supports up to 48 for separately authorized production work. The pilot
used 24. RSS reservations and a live process-tree sampler constrain aggregate
memory; each subprocess also has an address-space limit. A root-disk threshold
of 100 GiB and a worktree-plus-scratch budget of 60 decimal GB are enforced.
Resource aborts terminate the subprocess groups. Do not run multiple production
schedulers simultaneously under one memory budget.

Update only generated assemblies after changing their templates:

```sh
python3 AKLT/Cert/H3/production.py assemble --cases B1 B2 C1 C2 C3
```

After checks have completed, emit the writer and audit inventories:

```sh
python3 AKLT/Cert/H3/production_audit.py
python3 AKLT/Cert/H3/run_checks.py CertData.H3.Bridge.Audit --timeout 300
python3 AKLT/Cert/H3/production_plan.py
```

`production_audit.py` prints/checks every closed mathematical statement and
records every generated theorem's statement and axiom output. The generated
check modules themselves contain `#print axioms` for every exported theorem.
`production_plan.py` forecasts remaining work using the actual B1 measurements;
it is not evidence that the other cases were executed.

`production.py legacy --jobs 3 --ram-gb 60 --process-gib 48` rebuilds the
relocated phase-1 prototype and its two original closed-leaf target assemblies.
Their declaration names and proof bodies are preserved; only module imports
were renamed. The old target route is superseded by the V2 route and remains
available for compatibility.

The kernel-checked assembly interfaces are:

- `CertData.H3.Bridge.automatonV2_from_leaves`.
- `CertData.H3.Bridge.caseV2_of_checks` and the actual
  `CertData.H3.Bridge.B1.case_from_leaves`.
- `CertData.H3.Bridge.stationaryV2_from_family_checks` and
  `CertData.H3.Bridge.stationaryV2_of_cases`.
- `CertData.H3.Bridge.legacy_automaton_from_v2` and
  `CertData.H3.Bridge.legacy_stationary_from_v2`.

The full fixed-data composition
`CertData.H3.Bridge.All.stationary_from_leaves` is generated. Its imports become
available after the four nonpilot cases run. Inhabiting `AutomatonBridgeLeaves`
and `ProductionCaseLeaves` is mathematical writer work, rather than a new
certificate-generation implementation task.


## Phase 3 merge handoff

`merge-set.txt` in the report directory is the exact source-only merge set.
Build `lake build CertData.H3.Core` (or the optional `CertData` library target).
`CertData.lean` imports only the handwritten core; the library glob selects this
root rather than enumerating the generated tree. Attach generated modules under
`CertData/H3/` later and build `CertData.H3.Bridge.All` explicitly. There are no
new `.lean` files under `AKLT/`; ordinary `lake build` keeps its existing graph.
The original `AKLT.Cert.H3` declaration namespaces are retained in the relocated
kernel modules for compatibility with the already proved phase-1 helpers.

Phase 3 generalizes the eight graph storage/join leaf statements in
`Bridge.Production` over `PackedGraph` and receipt arguments. This removes their
imports of concrete graph/check modules. `DecodeDataLeaf` is unchanged; the
other seven signatures now bind their packed graph or graph argument explicitly.
No proof is supplied for these leaves. `leaves-open.json` is the current writer
handoff; use its module paths, rather than the accepted phase-2 paths.

`python3 AKLT/Cert/H3/validate_merge.py` reconstructs the merge-set import closure
from a frozen main revision and type-checks it using only prebuilt Mathlib,
without copying repaired statement sources into this worktree. Its clean output
and statement comparison receipts are in the report's `phase3/` directory.
