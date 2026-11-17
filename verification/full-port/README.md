# Complete release: hand-written port verification

STATUS: FULL PORT COMPLETE

Verified source snapshot: `3c8260184b1df7b90b5cd780777a4a9f2e411985`. All 1,104 original
hand-written files preserve their Lean code after the listed visibility edits.
The release has 1,115 Lean files, including 1,109 source-buildable files and six
closing targets awaiting generated certificates. Original proof-code changes: zero.

The unconditional target is `AKLTPalomar.aklt_gap : AKLTPalomar.Main` in root
Solution. It depends on `CertData.Close.main`; it is not claimed built in this phase.
The independent three-checker result below is the retained two-input regression.

| Stage | Wall, s | CPU, s | Peak tree RSS, GiB | Result |
| --- | ---: | ---: | ---: | --- |
| Official source/configuration checks | 3.426 | 3.342 | 0.065 | 2 author-owned TODO findings |
| Lean header parser, all 1,115 files | 2.242 | 2.272 | 1.712 | PASS |
| Fresh hand-written + Challenge + regression build | 699.726 | 8624.126 | 56.848 | PASS |
| Available-source Audit target build | 13.307 | 13.789 | 4.029 | PASS |
| Paper-reference comment rebuild | 13.954 | 21.059 | 3.831 | PASS |
| Serial-comma comment rebuild | 39.499 | 154.899 | 17.940 | PASS |
| Final American English comment rebuild | 25.681 | 92.067 | 23.582 | PASS |
| Strict available-source Audit | 5.665 | 5.630 | 4.761 | PASS |
| Axiom transcript guard | 0.103 | 0.095 | 0.001 | PASS |
| Protected two-input Challenge build | 8.845 | ≈8.750 | 3.667 | PASS |
| Protected two-input Challenge export | 17.114 | ≈16.940 | 6.366 | PASS |
| Regression.Solution full export | 49.483 | ≈49.300 | 7.084 | PASS |
| Protected Comparator: NanoDa, then Lean | 662.867 | ≈740.070 | 23.226 | PASS |
| Verified con-ron, two workers | 627.995 | ≈740.140 | 47.186 | PASS |
| Final-source export identity check | 46.557 | ≈46.370 | 7.081 | PASS |


The stage-time accounting sum is 2216.464 wall seconds and
10518.850 CPU seconds. Some stages overlapped, so this is not a measured
cold end-to-end elapsed time. Dependency artifacts were already cached. Measurements
use affinity 0–15 and the authorized local memory envelope, not a Palomar 32-GiB
cgroup. RSS sums can double-count shared pages; namespace CPU may be sampled.

The full regression export has 63,516 declarations, 671,987,125 bytes, and SHA-256
`9a6aba195545920cd2b62a256cb9b64d3681de90d91f32193cc6071ec503ae1a`. Final-source re-export is byte-identical
to the export accepted by Lean, NanoDa, and con-ron. Strict audit checks 21,855
declaration entries; module-local realizations can repeat a declaration name.
The only permitted axioms are propext, Classical.choice, and Quot.sound.

Root Challenge is 161 lines and 7,736 bytes. Every first-party Lean file has a
module header, and the maximum file length is 1,636 lines. Only Challenge has its
conventional placeholder. Author metadata and the root LICENSE remain TODO.

Pending generated sources: 7,964 H1 and 5,032 H3 modules. Pending hand-written
builds: CertData.H1.Close.Main, CertData.H1.Close.Audit, CertData.H3.Close.Main,
CertData.Close.All, Solution, and Audit. See ../../REGEN-INTERFACE.md for exact
imports, declaration inventories, exposed bodies, sample modules, and handoff.

The full cold-cache/network path has not been run. The committed-clone smoke test
intentionally used a two-second watchdog and retained an incomplete receipt.
The archive installer smoke tests passed outside the release tree. Raw compiler
and checker transcripts are retained verbatim; authored prose uses American English.
