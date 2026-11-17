# Verification boundary

The populated module-system release has passed a fresh default-target source
build, explicit Challenge/Solution/Audit builds, strict axiom checks, independent
protected statement comparison with Lean and NanoDa, and verified con-ron replay.
The package originated at main d77c3ca and was ported only in this separate Git
repository. The legacy tree was not edited.

`local-receipt.json` records the local component study and export digests. Its
source proof files match PORT-MANIFEST.tsv. These measurements used existing
pinned dependency artifacts, 16 CPUs' affinity, and the authorized larger local
memory envelope. They are not an authenticated production cgroup run or a cold
Mathlib-cache receipt. In particular, the measured con-ron peak exceeds 32 GiB;
a default-profile capacity decline needs official supervision.

The root metadata still has author-owned TODOs and no selected release LICENSE.
A completed local proof check is not registry preparation or acceptance. The
standalone cold runner produces new logs and JSON receipts for any chosen package
commit without the study's external package store. Run it inside a real 16 CPU /
32 GiB cgroup as described in the package README. Exit 2 means mandatory kernels
accepted but con-ron hit a locally observed capacity limit; the official verifier
must authenticate that classification.

The previous `axioms-compat.log` is an explicitly historical pre-port architecture
transcript. Current strict axiom output is `axioms.log`; both have only the three
allowed axioms for the five advertised exports. No NDJSON export or project olean
is committed to this source repository.
