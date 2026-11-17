# H3 module-system regeneration changes

The numeric input pins, packing, checker definitions, and certificate statements
are unchanged. Every generated source is regenerated from the numeric archives.
No legacy compiled object is reused.

- `AKLT/Cert/H3/production.py`: emit `module`, public imports, an exposed public
  section, and `backward.proofsInPublic`; print axioms for every exported theorem.
  Use a finite two-billion heartbeat allowance and retain the recursion limit.
  Replace the legacy scratch build/import implementation with the release runner.
- Prefix reducers privately `import all Init.Data.List.Sort.Basic`. The unchanged
  `mergeSortFuel` body calls the standard-library private `splitInTwo` helper.
  Importing its body only in `PrefixView` did not make it available to a later
  `decide +kernel`. The first early-prefix pilot detected this. Importing the
  original standard-library body in the reducing module preserves the checker
  and sort exactly. Standard-library sources and objects are unchanged.
- `AKLT/Cert/H3/regen.py`, `inputs.json`, and `prefix-reference.json`: input pins, exact inventory checks,
  ordinary Lake import environment, dependency/source/object hashes, resource
  guards, per-module fresh processes, resumable receipts, and complete axiom
  audits. The reference assertions replace the generator's dependency on five
  external native log files, retaining their exact bounds and counts. Generated
  objects go under `.lake/build/lib/lean/CertData/H3/`.
- `AKLT/Cert/H3/production_receipts.py`, `production_audit.py`, and `run_checks.py`:
  use the release runner and its receipt format instead of the legacy
  worktree/scratch layout. Selected checks force fresh processes while reusing
  only verified dependencies.
- `AKLT/Cert/H3/export.py` and `generate_prefix.py`: update retained prototype
  output headers, imports, line checks, report destination, and disk guard. These
  prototypes are outside the production inventory and are not produced by this run.

Hand-written Lean checker edits: **none**. No definition, proof body, leaf type,
or closing statement has been changed.
