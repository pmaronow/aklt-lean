# Source and portable-tool checks

The current records bind the unchanged Lean source tree at 42b16c3 to portable
certificate tools and the complete numeric-input cold verification plan.
`summary.json` states the exact scope. No compiler, certificate command, or
independent kernel was run for these checks.

`protected-baseline.json.gz` records current hashes for every tracked Lean file,
build pin, generated/API inventory, numeric pin, and retained certificate tool.
Its source baseline identifies the Lean sources; Python hashes identify the
accompanying tool revision. `verification/source-digest.txt` at the repository
root records the digest of the 1,117 tracked Lean files and three build pins.
`manifest-checks.json` checks the active port manifests, source inventory,
protected hashes, source digest, and exact Challenge generation. Historical
receipts under fidelity-fix/, fidelity-round2/, and rename/ retain their original
hashes and remain bound to their own source commits.

`tool-compatibility.json` records exact AST identity for both receipt verifiers,
key/dependency hash functions, numeric emitters, owner bundling, and the H1
per-module compilation/receipt body. Other changes are restricted to input/report
selection, documentation, and the optional aggregate-memory control. Synthetic
probes reproduce identical keys, input receipt bytes, module envelopes, and H3
context/dependency hashes. They do not verify a mathematical proof.

`checks.json` covers syntax, the 29-stage dry-run, exact H1 command order,
resource limits, paths with spaces, argument rejection, input-directory settings,
small positive/negative numeric fixtures, uppercase layout compatibility, and
byte-exact Challenge generation. A one-byte read perturbation is rejected
without changing a source file. `source-checks.json` preserves the official
source/module-header/line-cap/configuration result: only author metadata and
LICENSE findings, with generated sources counted separately.

Reproduce the pure-Python checks with:

```sh
python3 scripts/refresh_manifests.py --check
python3 scripts/inventory.py --check
python3 scripts/source_digest.py --check verification/source-digest.txt
python3 scripts/make_challenge.py --check
python3 scripts/self_check.py
python3 scripts/check_tool_compatibility.py --baseline 42b16c3
```

The compatibility comparison needs the named Git revision. It never executes an
old or new certificate command. `moved-references.tsv` preserves the earlier
root-record relocation map. `placeholders.json` lists the result
fields that were unfilled when these checks ran; the root VERIFICATION.md now
records them. The baseline commit named here resolves on the `development` branch. `absolute-paths.tsv.gz` inventories retained absolute literals, including
verbatim historical reports; its JSON companion gives counts. Operational
scripts and working instructions contain no fixed user-specific path. See
`docs/PORTABILITY.md` from the repository root for current defaults and overrides.
