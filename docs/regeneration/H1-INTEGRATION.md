# H1 release-stage integration

The H1 numeric route is the data-only interface in the incoming hand-back:

```sh
export H1_INPUT_DIR="$PWD/data/H1"
export H1_REGEN_REPORT="$(dirname "$PWD")/aklt-verification/H1"
python3 AKLT/Cert/H1/tools/production_reexport.py \
  --scratch "$H1_REGEN_REPORT/export-scratch" --install \
  --report-dir "$H1_REGEN_REPORT"
python3 AKLT/Cert/H1/tools/production_build.py \
  "$H1_REGEN_REPORT/data-only-production.json" \
  --jobs 12 --cap-gib 8 --report-dir "$H1_REGEN_REPORT"
python3 AKLT/Cert/H1/tools/production_receipts.py verify \
  "$H1_REGEN_REPORT/data-only-production.json" --report-dir "$H1_REGEN_REPORT"
python3 AKLT/Cert/H1/tools/production_close.py --report-dir "$H1_REGEN_REPORT"
```

These commands describe the final stage's operations. **TBD-H1-PORTABLE-ENTRYPOINT**:
connect the final hand-back through the cold driver's `--h1-stage` adapter.
The reference `AKLT/Cert/H1/tools/production_regen.py` transforms retained sources
using `--legacy-root`, `--legacy-manifest`, `--legacy-receipt`, and `--report-dir`;
it is not the numeric-input-only route above. Its source name and public
arguments are retained. No legacy object is needed by the data-only route.

The inspected H1 hand-back still has literal campaign input paths in
`production_export.py`, `production_bridge_export.py`, `production_coverage.py`,
and the `inputs` command of `production_receipts.py`. Setting `H1_INPUT_DIR` alone
does not make those versions portable. This layout commit preserves runner bytes
so the active certificate builds and receipt contexts remain valid. The adapter
must bind the final portable interface; it must not claim success by setting an
unused variable. The cold driver refuses to start any build without this adapter.
See `docs/PORTABILITY.md` for the complete retained-path inventory.

The adapter is a Python script invoked with:

```text
--project REPOSITORY --input-dir INPUT/H1 --report-dir REPORT/H1
--jobs INTEGER --memory-gb DECIMAL_GB
```

It must hash-check the seventeen inputs against `verification/inputs/H1.json`,
write `data-input-receipt.json` in the format consumed by the H1 verifier, install
a fresh 7,964-owner data-only source export, build the complete DAG with fresh
processes and the requested resource limits, independently verify all source,
dependency, artifact, and axiom receipts, and build/audit both H1 closing modules.
It must exit nonzero for any error. It must not reuse objects from another clone,
update dependencies, change source/interface names, or compact accepted sources.
The final `verified-production.json` must report 7,964 successful modules.

For the inspected plan, larger data/assembly owners have 16 GiB process caps;
two terminal owner kinds have 64 GiB caps. The adapter must honor these plan
reservations as well as the aggregate memory argument. The cold driver adds an
outer sampled RSS guard; a real cgroup can enclose the command as well.

Store the incoming notes as `docs/regeneration/H1.md` and
`docs/regeneration/H1-CHANGES.md`. Keep H3's separate notes intact. Confirm the
archive pins in `docs/ARTIFACTS.md`, then fill the H1 and final-build fields in
`VERIFICATION.md`. None of those documentation changes affects the Lean source
digest or the certificate dependency hashes.
