# H1 regeneration changes

No hand-written Lean checker, checker definition, statement, proof body, arithmetic
operation, or input datum has been changed. The pilots use the ported exposed
kernels supplied by the release.

- `AKLT/Cert/H1/tools/module_source.py`: a reversible module envelope adds
  `module`, public imports, an exposed public section, and
  `backward.proofsInPublic`. Explicit private helpers retain their modifiers.
  The three historical catalog identifier spellings are translated to the
  release spellings, with no numeric or string-literal changes.
- `export.py` and `production_export.py`: every source write uses that envelope.
  Report and scratch output roots can be selected through `H1_REGEN_REPORT` and
  `H1_REGEN_ROOT`; the pinned numeric input directory is unchanged.
- `production_bundle.py`: unwraps the visibility envelope before the original
  size-based grouping and body concatenation. This preserves all 7,964 owner
  names, all component namespaces, and each independent kernel reduction.
- `production_regen.py`: checks retained source hashes against the legacy
  verified receipt, transforms only sources, and creates the release manifest
  and paired pilot plan. It never reads or copies a legacy compiled module.
- `production_reexport.py`: runs the complete original numeric export, bridge,
  coverage, representative-index, and two bundling stages in a separate scratch
  directory. All 7,964 owners were independently regenerated from the pinned
  integer inputs and matched the transformed sources byte for byte.
- `production_bootstrap.py`: checks only the local ported prerequisites; removes
  the legacy artifact-symlink attachment workflow.
- `production_build.py`: uses fresh single-threaded Lean processes and this
  release's normal Lake artifact directory. Source, input pins, hand-written
  dependency closure, generated dependency keys, and all module artifact parts
  determine replay. It captures stdout, stderr, GNU-time, per-theorem axiom
  receipts, and an append-only build journal. Module locks and atomic receipts
  permit resume. Limits are 36 Lean processes, 270 GB RAM, 40 GB available RAM,
  and 100 GiB free disk, with conservative per-module reservations.
- `production_receipts.py`: independently checks every source, compiled artifact,
  dependency key, exit status, import edge, and complete theorem axiom transcript;
  writes source and compiled-module SHA-256 manifests.
- `production_measure.py` and `production_cache_test.py`: summarize the new
  receipt format and test unchanged replay, transitive invalidation, expected
  kernel rejection, and restoration in an isolated validation run.
- `production_close.py`: builds both existing closing modules with strict
  warnings, records their exact closed types, and audits every printed theorem.
- `production_handoff.py`: writes final totals and the hand-off only after
  independent production, closing, archive, and all paired-pilot receipts pass.
- `production_archive.py`: creates a deterministic archive containing exactly
  the 7,964 inventory source paths and no compiled artifacts.
- `production_status.py`: records accepted owner counts and same-owner pilot
  comparisons in the live report. It does not change certificate artifacts.

The complete data-only reproduction took 228.63 seconds and emitted 158,230
logical components before bundling. The longest owner has 1,690 physical lines.
Every transformed owner retains exactly its original data and check expressions.

`CertData/H1/Close/Main.lean` has one documentation-only update identifying
the imported numerical proofs as freshly checked module-system certificates.
Its declarations, types, and proof bodies are unchanged.

## Coverage performance finding

The coverage frontier pilots pass but use 26–28% more CPU than their legacy
receipts. A profiled small frontier used 77.3 seconds for kernel type checking,
versus 61.3 seconds in the legacy profile. Loading private bodies did not help
(92.17 CPU-seconds), nor did default private-proof elaboration (88.01 seconds),
compared with 85.11 seconds for the profiled required-header control. All data
and checker expressions were held fixed. No missing exposed body was found.
The production headers and checker definitions remain unchanged. The cost
increase is recorded for the orchestrator; no definition-preserving repair was
identified. Diagnostic receipts are in `coverage-performance.json`. Temporary
validation sources and objects were removed only after recording their hashes.
