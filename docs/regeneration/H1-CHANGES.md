# H1 certificate tooling and module interfaces

The generated library uses ordinary Lean module-system files. No arithmetic
expression, checker definition, statement, proof body, input number, owner name,
dependency edge, or numeric-data key changes in this tooling update.

- `module_source.py` supplies the reversible visibility envelope: `module`, public
  imports, an exposed public section, and `backward.proofsInPublic`. Explicit
  private helpers retain their modifiers. The existing identifier conversion
  preserves numeric and string literals.
- `export.py`, `production_export.py`, `production_bridge_export.py`,
  `production_coverage.py`, `production_index.py`, and `production_bundle.py`
  generate the same source expressions and the same 7,964-owner map. Bundling
  keeps every `decide +kernel` reduction separate.
- `locations.py` defines one numeric-input location, `H1_INPUT_DIR`, defaulting
  to `data/h1/`, and one report location, `H1_REGEN_REPORT`, defaulting to
  `verification/runs/H1/`. Both defaults are relative to the repository. The
  existing `H1_REGEN_ROOT` output override remains independent of numeric inputs.
- `production_reexport.py` runs the complete numeric export and both bundling
  stages in a separate scratch directory. Every owner matched the converted
  module-system source byte for byte; the owner/dependency/component map matched.
- `production_build.py` keeps the existing source, recursive library, build-pin,
  generated-dependency, and compiled-artifact key calculations. The optional
  `--ram-gb` limit defaults to the existing 270 GB and changes only resource
  admission and RSS checks. Existing per-module reservations and all receipt
  field names are retained.
- `production_receipts.py` independently checks source and compiled hashes,
  dependency keys, actual imports, exit status, and every exported theorem's
  axiom transcript. Its verifier and receipt format are unchanged. The input
  command reads the shared input directory and retains its exact record format.
- `production_close.py` builds the two existing closing modules, checks their
  exact hypothesis-free types, and audits every printed theorem. Its source and
  compiled-artifact records are unchanged.
- `production_archive.py` creates the deterministic source-only archive;
  `production_measure.py` summarizes verified receipts. The optional
  `production_cache_test.py` checks transitive invalidation and expected rejection
  in a separate validation directory.

The numeric route is the release build route. Unused source-conversion,
prerequisite, progress-report, and merge helpers are excluded. The commands,
input pins, reference per-kind measurements, resource settings, receipt contents,
and closing contracts are documented in [H1.md](H1.md).

Coverage-frontier checks used 26–28% more CPU than the corresponding
pre-module-system checks. The reference profiled control spent 77.3 seconds in
kernel type checking versus 61.3 seconds. Loading private bodies did not help
(92.17 CPU-seconds), nor did default private-proof elaboration (88.01 seconds),
compared with 85.11 seconds for the profiled control. Inputs, arithmetic, and
check expressions were fixed. This measured cost does not change correctness.
Final combined-tree measurements use `TBD-H1-CPU-HOURS`, `TBD-H1-WALL`,
`TBD-H1-PROCESS-MEMORY`, `TBD-H1-AGGREGATE-MEMORY`, and `TBD-H1-RECEIPT` as
recorded in `VERIFICATION.md`.
