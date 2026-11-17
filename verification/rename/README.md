# American English identifier verification

STATUS: RENAME COMPLETE

Verified source commit: e0597c0c7910b671f8bc816983e4ba61a26160eb.
All 419 listed source identifier tokens are updated consistently. The compiled
name set is the exact image of the baseline: 18,955 declarations, with 646 changed
names. No declaration, namespace-prefix, file-path, or conservative local collision
was found. Eight Lean files were renamed; 356 Lean files have spelling edits.

The spelling rules and exact old-to-new map are in the external campaign report.
Current spellings are listed in ../../AMERICAN-ENGLISH-IDENTIFIERS.tsv. All 27
generators were reviewed; all 851 literal data-key accesses and all Lean string
literals are unchanged. Paper citation labels and external names remain intact.

| Stage | Wall, s | CPU, s | Peak tree RSS, GiB | Result |
| --- | ---: | ---: | ---: | --- |
| External-name inventory (read only) | 19.743 | 19.714 | 4.742 | PASS |
| Fresh hand-written tree + Challenge + audit + samples | 738.088 | 8985.206 | 55.378 | PASS |
| Strict whole available-tree Audit | 5.164 | 5.160 | 4.761 | PASS |
| Explicit axiom transcript guard | 0.204 | 0.104 | 0.001 | PASS |
| Official Lean header parser, all files | 2.246 | 2.232 | 1.660 | PASS |
| New-name generator ABI probe | 4.656 | 4.593 | 4.426 | PASS |
| Official source/configuration checks | 2.517 | 2.495 | 0.062 | 2 author-owned TODOs |
| Protected pipeline header parse | 0.104 | 0.087 | 0.001 | PASS |
| Regression explicit targets | 10.480 | 11.392 | 0.949 | PASS |
| Strict regression Audit | 3.437 | 3.399 | 4.505 | PASS |
| Explicit axiom transcript guard | 0.103 | 0.028 | 0.001 | PASS |
| Protected independent regression Challenge | 4.446 | ≈4.340 | 3.678 | PASS |
| Protected Challenge export | 9.196 | ≈9.030 | 6.365 | PASS |
| Full renamed regression export | 35.353 | ≈35.190 | 7.082 | PASS |
| Comparator: NanoDa then Lean | 719.238 | ≈792.710 | 23.226 | PASS |
| Verified con-ron replay (two workers) | 579.757 | ≈727.110 | 47.182 | PASS |


All 1,115 source headers and line caps pass. The 1,109 unblocked sources build
from fresh project objects. Strict Audit checks 21,855 declaration entries with
only propext, Classical.choice, and Quot.sound. Both sample/consumer families
and the new-name catalog/center ABI probe pass.

The protected two-input theorem is accepted by Lean, NanoDa, and con-ron. Its
full export has 63,516 declarations and 671,986,654 bytes;
SHA-256: ea82aaec07c458ff23d38403de8cc22fc93b488cebc3a99ebe4ed6701d7fab6d.
The independent root Challenge is byte-identical to the baseline, 161 lines and
7,736 bytes, and contains no affected identifier. All three alias identifications
remain Iff.rfl. The full unconditional closing build still awaits generated data.

Old transcripts were archived without editing, and remain available in Git
history at baseline 169a4007abea6cc73e4630ef99b797491a1708a7. They are not
relabeled as new evidence. Current measurements use 16 CPUs' affinity and the
authorized local memory envelope; some diagnostic stages overlap. CPU may use
sampled namespace child totals, and RSS sums can double-count shared mappings.
Palomar's production resource ceilings are not acceptance constraints here.

Next: regenerate 7,964 H1 and 5,032 H3 sources against these names, then verify
CertData.Close.All, root Solution/Audit, and the unconditional full export.
Author metadata, root LICENSE, and independent fidelity review remain pending.
