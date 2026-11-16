# H1 production certificates

The reusable code is in `AKLT/Cert/H1/Production/`. Generated data, finite
checks and their conditional assemblies are here, outside the ordinary AKLT
library. `lake build AKLT` has no import of these certificates. The explicit
`CertDataH1` target selects `Generated/Batch/` and `Generated/Bridge/`.
The hand-written library entry point is `AKLT.Cert.H1.Production.All`; it builds
on current main without attaching any generated modules. The shared generic
`CertData` target on main is preserved.

`Generated/Data/` and `Generated/Check/` are unbundled generator output, retained
as lossless `.lean.gz` sources. The owner maps identify their production
bundles. Bundles preserve the public Data/Check declaration namespaces. Each
`decide +kernel` remains a separate declaration; reductions are never combined
into one large Boolean reduction.

The bridge uses current main's `H1SectorWitnesses`, `H1FiniteDataStatementV2`
and `CertificateStatementV2`, as well as the original Top targets. The phase-3
merge check compiles every hand-written Lean module on a clean main snapshot.
No Defs or package source is edited, and no Mathlib build or Lake update is invoked.

From the CERT_H1 project root, the complete production route is:

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 AKLT/Cert/H1/tools/production_bootstrap.py --jobs 4 --cap-gib 11
python3 AKLT/Cert/H1/tools/production_export.py --all
python3 AKLT/Cert/H1/tools/production_bridge_export.py /home/ubuntu/aklt/reports/CERT_H1/phase2/production-manifest.json
python3 AKLT/Cert/H1/tools/production_coverage.py
python3 AKLT/Cert/H1/tools/production_index.py /home/ubuntu/aklt/reports/CERT_H1/phase2/production-complete.json
python3 AKLT/Cert/H1/tools/production_bundle.py /home/ubuntu/aklt/reports/CERT_H1/phase2/production-manifest.json --label Batch
python3 AKLT/Cert/H1/tools/production_bundle.py /home/ubuntu/aklt/reports/CERT_H1/phase2/production-final.json --base /home/ubuntu/aklt/reports/CERT_H1/phase2/production-batched.json --label Bridge --output /home/ubuntu/aklt/reports/CERT_H1/phase2/production-ready.json
python3 AKLT/Cert/H1/tools/production_build.py /home/ubuntu/aklt/reports/CERT_H1/phase2/production-ready.json --jobs 24 --cap-gib 9 --seconds 7200 --compact-sources
python3 AKLT/Cert/H1/tools/production_leaves.py
python3 AKLT/Cert/H1/tools/production_measure.py
```

The `--all` exporter defaults to `production-manifest.json`; selected exports
default to `pilot-manifest.json`. Use an explicit `--manifest` for diagnostics
to preserve measured pilot plans.

The manifest is a complete dependency DAG. Successful events form a replay
journal; source, dependency and artifact hashes control reuse. Module locks
prevent two frontier runners from writing one artifact. `--force-kinds` reruns
selected stages while reusing their dependencies. `--jobs-file FILE` accepts
a live concurrency setting. Until `/home/ubuntu/aklt/flags/CERT_H3-p3.done`
exists, the runner limits itself to 24 processes and 245 GB of RSS reservations
within the 250 GB allocation. Afterwards it checks `free -g` and permits 44
processes and 410 GB of reservations within 420 GB. It keeps 40 GB available
for other writers. Normal modules use a 9 GiB cap; case modules use 16 GiB in
the phase-3 manifest. Final whole-catalogue witness/target modules have a
64 GiB cap and receive fewer concurrent neighbours. Virtual-address
caps are separate from RSS, because prebuilt library mappings are large.

Builds abort below 100 GiB of free root disk; task accounting stops at 40 GB.
`--compact-sources` gzip-compresses each accepted owner source and retains its
`.olean`. The driver reads compressed sources directly for replay and restores
one source if it needs recompilation. Never delete production check oleans.
`production_receipts.py verify MANIFEST --report-dir DIR` independently checks
the entire receipt DAG, hashes, exits and multiline axiom output. The original
data index and every saved witness chunk are hashed separately.

To restore all generated sources before a conventional `lake build CertDataH1`,
run `python3 AKLT/Cert/H1/tools/production_receipts.py restore-sources`.
`production_bundle.py` also reads compressed templates directly. The compressed
source bytes are identical to those accepted by the kernel; generated files
are excluded from the hand-written merge set.

The production route splits every D exchange parity before packing. Local
tables are reconstructed once per pattern. Sector layouts, all basis indices,
all parities, adaptive widths and whole packed Gaussian rows are checked.
Within a selected parity this includes the other magnetic weights. The
`--unsplit` exporter mode also supports full tensor rows, including other
parities; the production Defs bridge uses the split mode. Cross-parity
decoupling in the analytic certificate is a mathematical obligation.

The root report's `leaves.json` has 33 active closed mathematical leaves. They
have no proof here and require a different cheaper model's first attempt.
The full generated `Targets` module is conditional on those leaves. Closing
them is separate from running the finite production DAG.

`Phase1/` retains the previous sources and proofs unchanged. Its historical
namespaces are deliberately excluded from the production Lake globs.
