VERDICT: FIXES NEEDED

The headline result is closed in Lean: the three inputs and the all-parity main theorem have hypothesis-free proofs. The remaining issues are descriptions of the verification: H1 uses a different positivity route from the archived Bareiss calculation; the redundant 3734-block Bareiss run is external; the H3 module count misclassifies three handwritten modules; H2 took about four minutes; and the independent-kernel claim needs its precise scope. No mathematical change was made by EDIT_4. A fresh copy of the paper compiles successfully without undefined references or citations.

All paper line numbers below refer to the current files in `/home/ubuntu/aklt/manuscript-v2`. The final formalization snapshot is main commit `d77c3ca85754582f91354dd848ac5a830f73727d`, which includes the packaging merge added during this audit; that merge leaves the closing proofs and certificate sources unchanged. The paper and formalization were left unchanged by this audit. Supporting comparisons are reproducible with [audit.py](/home/ubuntu/aklt/reports/EDIT4_DELTA/audit.py); their results are in [audit-results.json](/home/ubuntu/aklt/reports/EDIT4_DELTA/audit-results.json). The large certificate computations were assessed from their retained proofs and receipts, rather than rerun.

1. **Distinguish the archived H1 verification from the Lean certificate.** The archived calculation uses 8439 direct-dominance blocks, two supplied nonzero Gram factors, and 3732 Bareiss fallback blocks. The accepted Lean production instead uses 8439 zero Gram factors and **3734 nonzero Gram factors**, with no numerical Bareiss fallback. It checks the same patterns, representation/inversion choices and reconstructed matrices. Both original nonzero factors are reproduced with identical values. This is a different certificate route for the same local inequalities, not an unproved H1 input.

   Evidence: [Production/Assembly.lean:91](/home/ubuntu/aklt/repo/AKLT/Cert/H1/Production/Assembly.lean:91) constructs every case witness from `g,d,S,L` and `gramResidualRows_of_checked`; [TopAssembly.lean:17](/home/ubuntu/aklt/repo/AKLT/Cert/H1/Production/TopAssembly.lean:17) derives positivity from those residual rows. The original archive's split is recorded in [h1_record_audit.json:5](/home/ubuntu/aklt/reports/REV_C2/checks/h1_record_audit.json:5). The Lean input bundle's `index.json.totals` has `raw_dd=8439, gram=3734`; all 16 bundle hashes match the accepted production input receipt. This audit also counted every block and compared every pattern and choice record: `audit-results.json.H1`.

   The following replacements make the distinction explicit while retaining the archived mathematical argument.

   At **sec8-inputs.tex:9–11**, replace the sentence beginning “The certificates consist” with:

   ```tex
   The finite tests specified below and in Appendix C use integer
   equalities, inequalities, and divisibility tests, with positive
   rational denominators cleared.
   ```

   At **sec8-inputs.tex:32–38**, replace the paragraph with:

   ```tex
   The local verification described below uses the archived
   representation and inversion choices, the two supplied nonzero
   Gram factors, and the Bareiss fallback permitted by
   Lemma~\ref{l:integercheck}. The Lean certificate uses the same
   patterns, choices, and reconstructed matrices, with zero Gram
   factors for the \(8439\) directly dominant blocks and nonzero
   Gram factors for all \(3734\) remaining blocks. It therefore
   proves the same local input without running the numerical
   Bareiss fallback.
   ```

   At **sec8-inputs.tex:139**, replace “These are the only two nonzero factors used.” with:

   ```tex
   These are the only two nonzero factors supplied in the original archive.
   ```

   At **sec8-inputs.tex:181–182**, replace the sentence beginning “The finite assertions specified above” with:

   ```tex
   The finite assertions specified above constitute the archived local
   verification. The accompanying Lean certificate proves the same
   local input by the reconstructed-matrix Gram/residual checks
   described at the beginning of this section.
   ```

   At **sec8-inputs.tex:331–336**, replace the passage beginning “The H1 calculation” and ending “inversion records.” with:

   ```tex
   The archived H1 calculation uses the frozen representation and
   inversion records. Its residual tests require all rows, and its
   fallback requires every division exact and every pivot positive.
   The fallback discharges exactly the blocks without supplied
   nonzero Gram factors, using the fixed representation and inversion
   records. The Lean certificate uses Gram/residual witnesses for all
   blocks and checks their mathematical reconstruction and coverage.
   ```

   At **sec8-inputs.tex:351–353**, replace the sentence beginning “Each certificate is a proof” with:

   ```tex
   Each Lean certificate proves its computational input from the
   finite integer assertions used in that certificate, with the (H1)
   witness format described at the beginning of this section.
   ```

   These qualifications also avoid suggesting that Lean explicitly asserts every archival bookkeeping count. For example, the intermediate counts 106101, 184914 and 123339 have an external enumeration record; Lean's production proves exhaustive coverage by its own finite enumeration and catalogue comparisons.

2. **Remove or label the external redundant Bareiss check.** At **sec8-inputs.tex:163–165**, delete the sentence:

   ```tex
   As an additional finite check,
   all \(3734\) blocks failing the direct dominance test, including
   the two with supplied nonzero factors, pass this fallback too.
   ```

   This is the minimal correction. The preceding sentence ending “replaces any requirement.” remains. A true alternative, if the external corroboration is worth retaining, is supplied in answer A below.

3. **Correct the module classification and describe the timing measurements accurately.** At **sec8-inputs.tex:22–27**, replace the passage from “The certificate for (H1)” through “for (H2) took seconds.” with:

   ```tex
   The certificate for (H1) covers all \(7962\) local patterns and
   their \(12173\) sector blocks; successful Lean builds of its
   numerical certificate library used about \(139\) CPU-hours.
   The production manifest for (H3\(_h\)) contains \(5032\) generated
   modules and three hand-written bridge modules; successful Lean
   builds of these modules used about \(19.5\) CPU-hours. The
   exhaustive kernel computation for (H2) took about four minutes.
   ```

   **5035 is the production-manifest total, not the generated-module count.** Its three handwritten entries are `CertData.H3.Bridge.Production`, `.LegacyTargets` and `.FamilyAssembly`. Evidence: [CLOSE_H3/report.md:50](/home/ubuntu/aklt/reports/CLOSE_H3/report.md:50), and the closing receipt fields `generated_libraries.H3.module_count=5032` and `generated_libraries.H3.modules`. This audit compared that list with all 5035 production module records: `audit-results.json.closing`.

   **139 and 19.5 are correctly rounded process CPU totals for successful module builds, including elaboration, literal loading, imports and proof checking.** They are not measurements of isolated kernel reduction. H1: [campaign-times.json:6](/home/ubuntu/aklt/reports/CERT_H1/phase3/campaign-times.json:6) distinguishes 135.5236028 CPU-hours of phase-3 successful compilation events from 139.0021389 CPU-hours of the full verified portfolio, including earlier reused receipts; interrupted jobs and exporter overhead are excluded. H3: `CERT_H3/phase3/production-receipt.json.cpu_hours=19.455275`; [CERT_H3/report.md:82](/home/ubuntu/aklt/reports/CERT_H3/report.md:82) explicitly explains the measurement.

   **H2's exhaustive computation was not a few-second check.** [check-build.log:1](/home/ubuntu/aklt/reports/CERT_H2/check-build.log:1) reports 237 seconds for `AKLT.Cert.H2.Check`. Its GNU-time record gives 244.78 seconds wall, 233.76 user plus 10.66 system seconds, and exit 0 (lines 5–9, 27). The later `Finite` and `Main` assemblies took only 4.2 and 3.4 seconds; those are not the exhaustive certificate computation. “Took seconds” is literally compatible with 237 seconds but gives a misleading scale here.

4. **Narrow the independent-kernel statement to the recorded recheck.** At **sec8-inputs.tex:27–30**, replace the sentence beginning “Everything in the formalization except” with:

   ```tex
   At commit~\texttt{63d176a}, the part of the formalization independent
   of the (H1) and (H3\(_h\)) certificate proofs, including the
   conditional derivation of Theorem~\ref{t:main} and the (H2) proof,
   was also checked by con-ron and NanoDa, two independent
   implementations of the Lean kernel. These rechecks exclude the
   (H1) and (H3\(_h\)) certificate proofs and the subsequent closing
   and packaging modules.
   ```

   Evidence: the latest [RESULT:1](/home/ubuntu/aklt/val/63d176add85a0eae6c862c54849a495434b7d438/RESULT:1), repeated in [VALCORE.log:3](/home/ubuntu/aklt/logs/VALCORE.log:3), is for base commit `63d176add85a0eae6c862c54849a495434b7d438`, with the explicit exclusion `^AKLT\.W\.(H3C|H1C)[0-9]`. It names 9853 exported project roots. The [names.txt](/home/ubuntu/aklt/val/63d176add85a0eae6c862c54849a495434b7d438/names.txt) includes `AKLT.Cert.H2.complete_checked`, `AKLT.Cert.H2.h2`, and `AKLT.Final.main_of_certificates` (the last at line 4087), and excludes the H1C/H3C certificate leaf proofs. Generated H1/H3 libraries and the later `CertData.*.Close` modules are outside this recorded recheck.

   con-ron accepted 92826 declarations with `--verified`; NanoDa checked 96228 declarations with **no typechecker errors**. NanoDa also reported one pretty-printer error, “Unable to print axioms”; this is not a rejected proof. The counts are each tool's reported totals, not two counts of the 9853 selected roots. The conditional theorem checked here takes four finite certificate contracts; [Conditional.lean:426](/home/ubuntu/aklt/repo/AKLT/Final/Conditional.lean:426) shows their exact types. The final unconditional application was subsequently checked by Lean itself. Thus the intended claim about the analytic derivation is supported; the literal word “Everything” overstates the recorded scope.

   The newly merged `AKLT.Final.Inputs` and `palomar/` package are also later than this two-kernel receipt. Their separate [verification/README.md:19](/home/ubuntu/aklt/repo/palomar/verification/README.md:19)–21 records Lean and NanoDa acceptance for the compatibility export, but a local con-ron allocation failure. This does not extend the two-independent-kernel acceptance record to the new package or to the finite H1/H3 certificates.

5. **Make Appendix C's opening compatible with H2's direct raw-row verification.** At **app-input-contracts.tex:16–18**, replace the sentence beginning “These finite assertions are verified” with:

   ```tex
   In Lean, the archived (H2) integer vector is expanded to all
   \(916\) raw windows and checked directly, and the archived
   (H3\(_h\)) automaton and stationary arrays are checked through
   their literal encodings. The resulting proofs are checked by the
   Lean kernel, as described at the beginning of Section~\ref{s:inputs}.
   ```

   This avoids claiming that the implemented H2 certificate itself checks a JSON file's 115-entry canonical-code indexing contract. It uses exactly the same vector values, but checks all raw rows. [Data.lean:30](/home/ubuntu/aklt/repo/AKLT/Cert/H2/Data.lean:30) defines that expanded witness; lines 44–52 define the exhaustive check; [Check.lean:10](/home/ubuntu/aklt/repo/AKLT/Cert/H2/Check.lean:10) proves it by `decide +kernel`. [CERT_H2/report.md:84](/home/ubuntu/aklt/reports/CERT_H2/report.md:84) expressly says the full 115-orbit reduction theorem is bypassed. No changed H2 integer witness is involved.

   At **sec8-inputs.tex:21–22**, the sentence “The certificates are checked inside the Lean kernel, not by external programs.” is correct about proof acceptance but obscures the external generation/transcription and the redundant external computation in answer A. Replace it with:

   ```tex
   The certificate proofs are checked by the Lean kernel; external
   programs generate and encode witness data.
   ```

6. **Scope the axiom statement to the actual proof.** At **sec8-inputs.tex:18–21**, replace the sentence beginning “The accompanying Lean formalization” with:

   ```tex
   The proof of Theorem~\ref{t:main} and the three input proofs use
   only the standard axioms \texttt{propext}, \texttt{Classical.choice},
   and \texttt{Quot.sound}, and do not use \texttt{native\_decide}.
   ```

   The claimed axiom set is fully supported for these proofs. This precision also accommodates the newly merged package's separate challenge template: [palomar/Challenge.lean:569](/home/ubuntu/aklt/repo/palomar/Challenge.lean:569) has an intentional theorem placeholder. It is outside the closing proof's import closure and [Solution.lean:3](/home/ubuntu/aklt/repo/palomar/Solution.lean:3) does not import it. The actual packaged reduction's separate [axioms-compat.log](/home/ubuntu/aklt/repo/palomar/verification/axioms-compat.log) also lists only the three standard axioms. The placeholder is not an axiom dependency or a missing proof in `CertData.Close.main`.

The following accounts for the requested verification statements, including those requiring no replacement:

| Current paper location | Assessment and supporting record |
| --- | --- |
| `main.tex:51–52`, abstract: theorem including finite checks formalized and kernel checked | **True**, with H1's implementation route clarified by finding 1. [All.lean:16](/home/ubuntu/aklt/repo/CertData/Close/All.lean:16), lines 22, 26 and 62, supplies closed `h1`, `h2`, `h3`, `main`. `receipts/closing/final-receipt.json.theorems[*]` records exact types, `hypothesis_free=true`, and axioms. No pending-proof wording needs restoring. |
| `sec1-result.tex:10–13`: Theorem 1.2 and its finite inputs formalized | **True.** The result type is `AKLT.Challenge.MainStatementV2`; [MainV2.lean:18](/home/ubuntu/aklt/repo/AKLT/Challenge/MainV2.lean:18) has uniqueness for every pair of sizes at least 3 and a uniform eventual gap for both parities, matching `t:main`. |
| `sec8-inputs.tex:15–17`: three inputs and theorem closed, Lean 4.35.0-rc2 with Mathlib | **True.** Closing receipt fields `lean_version`, `lean_commit`, `lean_toolchain`, `mathlib_commit`, `build.exit=0`. Lean commit is `11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib is `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The current `lean-toolchain` agrees. |
| `sec8-inputs.tex:19–21`: only `propext`, `Classical.choice`, `Quot.sound`; no `native_decide` | **True for the final proofs; finding 6 makes that scope explicit.** All four closing theorems print exactly these three axioms: [CLOSE_H3/report.md:149](/home/ubuntu/aklt/reports/CLOSE_H3/report.md:149) and closing receipt `theorems[*].axioms`. Generated H1/H3 proof audits allow no other axioms. H2 explicitly uses `decide +kernel`; H3's production report says the same at [CERT_H3/report.md:39](/home/ubuntu/aklt/reports/CERT_H3/report.md:39). The closing import-closure scan is at `handwritten_import_closure_audit`, with `success=true`. A search of current `AKLT/` and `CertData/` Lean sources also found no `native_decide` use, added axiom declaration, `sorry`, or `admit`; the separate package challenge placeholder is explained above. |
| `sec8-inputs.tex:23–24`: 7962 patterns and 12173 blocks | **True.** `CERT_H1/phase3/verified-production.json.patterns`, `.blocks`, `.modules=7964`; `phase3/measurements.json` repeats them. This audit independently counted all input records and blocks; max dimension 179. |
| `sec8-inputs.tex:24–30`: timings, H3 generated modules, independent recheck | **Correct as amended by findings 3–4.** There is no evidence for full independent replay of the H1/H3 certificates or final unconditional closing module. |
| `sec8-inputs.tex:181–182`, H1 proof; `351–355`, certification scope | **Too broad literally as descriptions of the prescribed Bareiss assertions.** Finding 1 supplies exact replacements. The same pointwise H1 theorem is proved; the particular Bareiss traces are not the numerical certificate used by Lean. The statement that the soundness arguments assume no window estimate, frame finite-energy bound, or spectral-gap conclusion is supported by the closed input types and the direction of their assemblies. |
| `app-input-contracts.tex:13–20`, Appendix C opening | **Same H2/H3 witnesses, with the H2 route qualification in finding 5.** No foreign or unrelated witness was substituted. |
| `app-input-contracts.tex:1174–1178`, Appendix C closing | **True; no replacement needed.** The five actual stationary checks and prefix ceilings are closed by [CertData/H3/Close/Main.lean:23](/home/ubuntu/aklt/repo/CertData/H3/Close/Main.lean:23). The archived exact fractions match the production manifest's `cases.*.exact_bound`; this audit compared all five. |

The records attach the claims to the current formalization, rather than merely to an old lane report: every current closing source in the final receipt's `source_merge_set` matches its recorded SHA-256; the retained final `All.olean` matches `output_olean.sha256`; the handwritten checker/bridge sources checked by this audit match the closing worktree. Relative to the independent-recheck base, current main adds the five closing sources, Lake configuration, closing receipts, `AKLT/Final/Inputs.lean` and the `palomar/` package. The previously validated source files are unchanged. Earlier conditional or “PARTIAL” passages in the lane reports are historical checkpoints or later exploratory searches, not remaining hypotheses of `CertData.Close.main`.

Additional numerical assertions in the relevant passages were checked as follows:

| Numbers in the paper | Finding and file/field evidence |
| --- | --- |
| H1: `4*5^3*8^4=2048000`; consistency/marking totals `106101,184914,123339` | Correct. The option lists are [Production/Coverage.lean:14](/home/ubuntu/aklt/repo/AKLT/Cert/H1/Production/Coverage.lean:14)–25. `CERT_H1/phase2/coverage-smoke.json.raw_cartesian=2048000`; [REV_C2/checks/h1_enumeration.json:2](/home/ubuntu/aklt/reports/REV_C2/checks/h1_enumeration.json:2) records the three intermediate totals and `classes=7962, missing=0`. These intermediate totals are external bookkeeping, rather than separate asserted counters in the accepted Lean coverage theorem. |
| H1: `12173`, maximum dimension `179`; `8439`, `2`, `3732`, redundant `3734` | Correct numbers. `audit-results.json.H1.counts` confirms total/dimension and the Lean split. `REV_C2/checks/h1_record_audit.json` distinguishes the archive's `direct_Gram_blocks=8439`, `archived_nonzero_Gram_blocks=2`, `adopted_fallback_blocks=3732`, `native_Bareiss_blocks=3734`. |
| Patterns 5420 and 7697: dimension 131, `g=1600,d=S=1`, margins `6820166897600,27361669345600` | Correct and the factors match. `audit-results.json.H1.archived_factors` records the comparisons. The original files' unscaled margins are `4262604311,17101043341`; multiplication by 1600 gives the displayed margins. |
| H2: 916 raw windows, 115 orbit entries; denominator 2695605, numerators 935000/961000/539121; extrema and tight row | Correct. `CERT_H2/witness-source.txt:1–4`, [Data.lean:37](/home/ubuntu/aklt/repo/AKLT/Cert/H2/Data.lean:37)–52, [Check.lean:15](/home/ubuntu/aklt/repo/AKLT/Cert/H2/Check.lean:15), and `Finite.lean`'s `witness_low`, `witness_high`, `witness_tight`, `witness_row`, `h2Test`. This audit compared all 916 values to all 115 archived orbit values. Minimum `186377076276`, maximum `1000000000000`, `v(428)=224087522845`; the kernel-certified row numerator is `603787640626036713`. The exact rate is `1119948287353/1120437614225`; `C_V=10` is supplied by [Main.lean:118](/home/ubuntu/aklt/repo/AKLT/Cert/H2/Main.lean:118). |
| H3: `m=10,L=12,R=70`, 3741 classes, 19881 sites, value scale `2^16`, coefficient scale `2^48` | Correct. All five original headers and production manifest headers agree; `audit-results.json.H3.potentials[*].header`. [Stationary.lean:77](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:77)–83 fixes the radius/scales; [ComputationV2.lean:13](/home/ubuntu/aklt/repo/AKLT/Blueprint/Top/ComputationV2.lean:13) fixes the supplied automaton contract. |
| H3: raw memory-ten count 60092, edge counts 2516/5032/1872 | Correct. Same supplied graph, checked by raw enumeration and representative/field checks. This audit compares all map and representative fields and recounts the edge kinds: `audit-results.json.H3.graph`. See also `CertData/H3/Check/EdgeCounts.lean` and `CertData/H3/Check/SuppliedTables.lean`. |
| H3 per file: `4*3741` caps, `4*3741*19881` values, `4*3741*(19881-2)=297469356` nonterminal components | Correct. These are the nonperiodic 141-by-141 arrays. [Model.lean:64](/home/ubuntu/aklt/repo/CertData/H3/Kernel/Production/Model.lean:64)–84 checks each plane, its cap, pins, terminal values, local rows and endpoint rectangle. There are 14964 planes per case; the manifest and input headers agree. |
| Five prefix ceilings `351207554,290599163,527872005,380754375,273048088` | Correct. `CERT_H3/phase3/build_manifest.json.cases.{B1,B2,C1,C2,C3}.ceiling`, each generated `Check/Summary.lean:8`, and the closed stationary contract. The exact fractions agree with the archived prefix records, not just rounded decimals. |
| Prefix nodes `139985,161929,105025,155673,145485`; surviving prefixes `89150,103257,66947,99168,92748`; short hits `937,922,715,1036,861` | Correct. Each generated `CertData/H3/{B1,B2,C1,C2,C3}/Check/Summary.lean:9` asserts these counts. In the sharded manifest, the paper's node count is `expected_total.nodes - expected_total.stems`, because each shard replays a frontier root. The surviving/short counts are `.leaves` and `.closed`. |

**Answer A: the additional 3734-block fallback run is external.** It is performed by [REV_C2/verify_h1_fallback.py:112](/home/ubuntu/aklt/reports/REV_C2/verify_h1_fallback.py:112)–155, with every pivot positive and every division checked using `divmod`. [h1_fallback_summary.json:2](/home/ubuntu/aklt/reports/REV_C2/checks/h1_fallback_summary.json:2) records 7962 patterns, 12173 blocks, 8439 direct blocks, 3734 Bareiss blocks, 57970522 exact divisions, 93614 positive pivots, zero nonexact divisions and zero failures. The two additional patterns are explicitly present in `h1_fallback_2-3.jsonl`: line 1807 is pattern 5420 and line 2566 is pattern 7697, each with 131 positive pivots and 374660 exact divisions.

Lean does contain and prove generic Bareiss mathematics: [TopLeaves.lean:44](/home/ubuntu/aklt/repo/AKLT/Cert/H1/Production/TopLeaves.lean:44)–52 states the universal pivot/minor and divisibility result; `AKLT.W.H1C005.main` proves it, and [Close/Main.lean:48](/home/ubuntu/aklt/repo/CertData/H1/Close/Main.lean:48) checks that exact type. That is not a numerical replay of these 3734 elimination traces. The accepted numerical certificate uses Gram/residual witnesses instead, as shown in finding 1.

Preferred action: delete the redundant sentence, as in finding 2. If retained, use exactly:

```tex
An external exact-integer calculation also verifies the Bareiss
fallback for all \(3734\) blocks failing direct dominance, including
the two with supplied nonzero Gram factors; this redundant
computation is not part of the Lean certificate.
```

**Answer B: the named files specify the same mathematical data, with an H1 witness-format extension.** Lean does not open JSON, text or gzip files during proof checking. External programs transcribe data to Lean literals; Lean checks the resulting values and their mathematical relationships. The closed theorem types are about mathematical arrays and witnesses, not filesystem paths or SHA-256 predicates. The file comparisons below establish provenance; hashes themselves are not proof assumptions.

The H1 source archive is under `compfeas/programs/` and `compfeas/data/`; the paper's two `programs/` files also have byte-identical copies in `manuscript/bundle/programs/`. The H2/H3 archives used by production are under `/home/ubuntu/aklt/compfeas/data/`. Full current hashes and comparison results are recorded in `audit-results.json.H1`, `.H2` and `.H3`.

| Named file | Finding: same values, regenerated equivalent, or different? |
| --- | --- |
| `programs/data/pext/pext7962.json` | **Same pattern values, transcribed through the regenerated H1 bundle.** SHA-256 `fd0866f455505e2cd6317f4a5cc4ec45a1f7d6ed5816786cb6500c3b773caba2`. The original, paper-bundle copy and `data/h1/inputs/` copy are byte-identical. This audit compared all 7962 patterns' IDs, outgoing directions, present bonds and site statuses to the production chunks. |
| `programs/h1-local/out/certificates_covered_operator_only.jsonl` | **Same mathematical choices.** SHA-256 `a3e83622530be8383c9a7989dc78461d76fda512025b458a6d61ead8d49bf309`. Again the three copies are byte-identical. All 7962 thresholds, outgoing directions, reduced/unreduced choices, inversion sets and slot counts agree with the production chunks. Historical search/eigenvalue metadata is not an input to the Lean proof. |
| `data/h1_chol_5420_131.json` | **Regenerated, with identical factor values and the same matrix after the stated scale conversion.** SHA-256 `1609c19ee853b214ca6a7e62a0a9695d2ac8f973d11bba672cf64528ea910358`. Every lower-triangular factor entry agrees; the full archived symmetric matrix multiplied by 1600 agrees with the production matrix. `g=1600,d=S=1` and the displayed residual margin agree. The exporter reconstructs this witness rather than parsing this original factor file. |
| `data/h1_chol_7697_131.json` | **Regenerated, with the same factor and scaled-matrix values.** SHA-256 `ba87ecf182c8f6f1b00178138dfbe21ae510ac6e2d2a060d6c57399ad6a0f313`. The same entrywise checks and parameter comparisons pass. |
| `h2_exact_m6k1_r5.json` | **Same `code`/`h` witness values, expanded from 115 orbits to 916 raw windows.** SHA-256 `ed486e175631deb207ba11a354016aa94854a4932e899b8c0c1fdfc56b3e6771`. This audit independently enumerated the raw windows and eight symmetries and compared every expanded value with `Data.lean`; all agree. The source hash also matches `CERT_H2/witness-source.txt:3`. Lean regenerates every row and verifies the extrema/tight row; it does not trust the JSON's summary fields or perform the optional 115-orbit reduction. |
| `windows_m10_min.txt` | **Same supplied quotient, including its numbering.** SHA-256 `671475d3333b646b3ace22a555f9a63a74f7bb076f0454f5b480c1e444a95785`. All 60092 map entries, 3741 representatives, destinations and edge kinds agree with the packed generated `Graph.lean`. The full dense map's nonwindow sentinel values also agree. No newly minimized or merely isomorphic quotient is substituted. |
| `stationary_B_m10_R70_d1_coarse.bin.gz` | **Same archived B/N array values, encoded as literals.** SHA-256 `3bdc2f5cfe54b15548ccf4b40384ab9585938385bb7860cf94ad1706239293a2`; accepted production case B1. Header, all 14964 cap values and the exact prefix record agree. |
| `stationary_B_m10_R70_d2_coarse.bin.gz` | **Same archived B/W array values.** SHA-256 `6303cba2e5ae59f1ba80ba52b2017a243e362a2ccea44ca776f04e166b8a679b`; case B2. The same comparisons pass. |
| `stationary_C_m10_R70_d1_coarse.bin.gz` | **Same archived C/N array values.** SHA-256 `2aabb88c464f3c3181fa92300548d6ea466321fccab09d32b654b8f0a07a8a6f`; case C1. The same comparisons pass. |
| `stationary_C_m10_R70_d2_coarse.bin.gz` | **Same archived C/W array values.** SHA-256 `0f75d0d12cc3d1c75f18fe68f7f81e78792ef671eda85688c2538ff9c35f352b`; case C2. The same comparisons pass. |
| `stationary_C_m10_R70_d3_coarse.bin.gz` | **Same archived C/S array values.** SHA-256 `6f709cca42dc57a5e52755767eea6af9e6527804661699a4e37f8796ede020e7`; case C3. The same comparisons pass. |

For H1, [data/h1/tools/generate.py:69](/home/ubuntu/aklt/data/h1/tools/generate.py:69)–102 reads the original pattern and choice inputs, reconstructs each matrix and creates its witness. Its `make_witness` at lines 42–65 supplies a nonzero factor for **every** nondominant block. [AKLT/Cert/H1/tools/export.py:49](/home/ubuntu/aklt/repo/AKLT/Cert/H1/tools/export.py:49)–65 consumes the hashed chunks; the production exporter imports this machinery. `CERT_H1/phase3/data-input-receipt.json` pins the index and all 16 chunks, and `verified-production.json` records the accepted module/source/artifact checks. There is no different local operator, threshold, pattern list or inversion search hidden in the route change.

For H3, this audit rehashed **all five complete compressed files** and the graph file. Every hash equals both `CERT_H3/phase3/production-inputs.json[*].sha256/expected_sha256` and the generator manifest's source hash. [production.py:293](/home/ubuntu/aklt/repo/AKLT/Cert/H3/production.py:293)–327 shows the exact header, phase/class/site order, cap parsing and lossless 80-bit-lane encoding of the original uint32 spatial values. It also extracts the prefix endpoint rectangle from those same values. Lines 362–367 compare the resulting exact fraction and counts with the archived prefix record. The generated row checks and proved bridge then verify the mathematical inequalities and endpoint identity.

The full spatial-value provenance assessment uses that input-hash/exporter/accepted-artifact chain. I directly compared every cap value and every graph field, but did not regenerate or re-export all 1.49 billion spatial values: 2340 plane/endpoint literal source files were compacted after their accepted builds, with their retained oleans and hashes preserved. [CLOSE_H3/report.md:50](/home/ubuntu/aklt/reports/CLOSE_H3/report.md:50)–56 and the closing receipt's per-module manifests document that handoff. This is a limit of this audit's fresh value comparisons, not evidence of a different potential. The later structured-potential experiments are not what the closed certificate imports.

The five prefix records mentioned without explicit filenames at `app-input-contracts.tex:1174` are `compfeas/logs/stationary_{B,C}_m10_R70_d{1,2,3}_coarse_exact_prefix.json` for exactly the five cases above. All five `exact_bound` fractions agree with `build_manifest.json.cases.*.exact_bound`; surviving-prefix and short-hit counts agree too.

The minimal substantive wording change for B is the H1 distinction in finding 1. The H2 clarification in finding 5 accurately describes the expanded raw-row check. No change of any named H2/H3 witness, array, bound or constant is warranted. If an additional general transcription sentence is wanted at `app-input-contracts.tex:1093`, the exact replacement for “The five witnesses are the files” is:

```tex
The five witnesses are the arrays \(Z,U\) stored in the files
```

**The EDIT_4 comparison and compilation both pass.** [edit4-only.diff](/home/ubuntu/aklt/reports/EDIT4_DELTA/edit4-only.diff) compares the actual pre-edit files with the current files. Applying the editor script's 28 literal replacements **in memory** reproduces all four current files byte-for-byte. All 22 `\certpending{...}` uses were removed. After excluding the newly added verification-status paragraph and normalizing whitespace/comments/markers, all **660 pre-existing inline/display math segments and 24 numbered theorem/lemma/proposition/definition statements** in the touched files agree. The remaining edits are status prose, the Section 8 label, and equivalent punctuation/conjunctions in the finite contracts. Every untouched `.tex` file has the same diff against HEAD as the saved pre-edit working-tree diff; in particular, the earlier `sec7-recursion.tex` edits were not changed by EDIT_4.

Compilation used only the copied `.tex` files in [paper-copy](/home/ubuntu/aklt/reports/EDIT4_DELTA/paper-copy/main.tex), starting without copied auxiliary files:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

Exit status was 0 after three pdflatex passes. The final [main.log](/home/ubuntu/aklt/reports/EDIT4_DELTA/paper-copy/main.log) has no undefined references/citations, multiply defined labels, LaTeX errors or overfull boxes. The combined [output log](/home/ubuntu/aklt/reports/EDIT4_DELTA/latexmk-output.log) retains the normal first-pass undefined-reference warnings and the subsequent reruns that resolve them. One underfull `\vbox` remains in the final pass. The output is [main.pdf](/home/ubuntu/aklt/reports/EDIT4_DELTA/paper-copy/main.pdf), 82 pages. `main.aux:7` resolves `t:main` to 1.2, and `main.aux:115` resolves `s:inputs` to 8. All paper `.tex` hashes still match the initial snapshot after the audit.
