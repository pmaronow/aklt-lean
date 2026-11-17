# Verification records

The root [VERIFICATION.md](../VERIFICATION.md) records the final source digest,
closing theorem checks, certificate builds, exact independent-kernel scope,
and author-owned metadata fields. `final/` holds the compact receipts behind that
record, with their own `SHA256SUMS`: driver status files, hand-written build logs,
H1 and H3 summaries and verifier logs, closing audits, source and header checks,
the two statement comparisons, and the independent-kernel replay of the two-input
reduction. The complete report directory is the release asset
`verification-receipts.tar.zst`. The other directories here are records of earlier
source revisions; the development commits they name resolve on the `development`
branch. The generated inventories and exposed API
records remain at `generated-modules.json` and `regen-interface/`; the runners
read those paths and bytes directly. `statement-sources.json` pins the two
library files copied into the root Challenge.

`port/` contains source inventories and identifier spellings.
`port/source-manifest.tsv` preserves the port's source hashes. Its manifests are
port records, not a substitute for the current `scripts/source_digest.py` output
or for the generated-source manifests. `reviews/` preserves three independent
statement reviews with their exact scope; `feasibility/` preserves the measured
independent-checker study.

For an earlier revision, `fidelity-round2/` records the accepted physical statement comparison, negative
control, full protected two-input proof replay, exact elaborated interface
identity, fresh affected build, and strict hand-written Audit. The source commit
is recorded in each summary. `fidelity-fix/` and `rename/` preserve earlier
source-bound evidence. Their absolute diagnostic paths and old source names are
not rewritten to suggest verification of a later tree.

`layout/` records the documentation/layout checks and unchanged protected-file
hashes. Those checks do not rerun Lean or the certificate computations.
`runs/` and `installed/` contain local generated receipts and are ignored by Git.
Release attachments contain the generated-source archives and the complete
receipts. Author identities, ORCIDs, license, and immutable public artifact URLs
are completed by the author in `formalization.yaml`.
