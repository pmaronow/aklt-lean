# Release layout checks

These records concern the layout/documentation commit based on 2707fd8.
They are not a new Lean build or certificate run. `summary.json` records the
changes, exact source digest, known integration fields, and check results.
`protected-baseline.json.gz` pins all 1,163 constrained files before any edit;
all remain byte-identical. The empty constrained Git diff is checked separately.

`moved-references.tsv` lists every original document/script reference to a moved
root record, including its original line and new location. The source inventory,
generated inventory, and machine-readable certificate interface paths are stable.
`source-checks.json` preserves the official source/header policy result: no
mechanical finding, with only author metadata and root license TODOs. The 12,996
absent generated paths are counted instead of duplicated from the inventory.

`checks.json` records script syntax, argument validation, cold-driver and physical
comparison dry-runs, exact Challenge bytes and its extra-byte negative control,
source-digest positive/negative controls, manuscript hashes, and ignore coverage.
No `.lake/build` directory was created. The compiled-source header parser's
previous acceptance remains bound to the identical Lean bytes; no elaboration
was needed or run for this layout task.

`absolute-paths.tsv.gz` lists retained absolute literals by file and line, with
a reason, including decompressed historical reports. The JSON companion gives
counts. See `docs/PORTABILITY.md` from the repository root for the operational
rules and the named H1 adapter completion field. The inventory excludes itself,
its producer's scanner patterns, repository-anchored Git ignore patterns, and
mathematical division. Historical records remain unchanged.
