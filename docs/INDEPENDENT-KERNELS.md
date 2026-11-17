# Independent-kernel scope and feasibility

The full `Regression.Solution` export of the final sources was accepted by Lean's
fresh replay, NanoDa, and verified con-ron. The physical Challenge definitions were also
compared with the library definitions by Lean and NanoDa, including an altered
spinZ negative control. These are distinct checks. Neither is an independent
replay of the unconditional proof with both generated certificate libraries.
The Lean kernel checks all certificate proofs at source-compilation time.

The REL_FEAS study measured original H1 and H3 samples and full owner modules;
it did not run a full unconditional release. Its source pin was
`973919fab9f115631dc07f81f23bb5c91404e777`, with the same Lean v4.35.0-rc2 and
Mathlib pin as this project. The following are estimates from those measurements,
not upper bounds, current release measurements, or claims of checker rejection.

| Stage | Planning estimate and basis |
|---|---|
| Comparator's fresh Lean replay | About 90–140 hours of serial numerical work. A complete H1 owner replay took 132.75 s versus 166.50 s for its source compilation; repeated replay computes the certificates again. More compiler workers do not parallelize this replay. |
| NanoDa | About 100–220 numerical CPU-hours, plus about 4–6 hours of parsing at measured sample throughput. The complete original H1 owner used 0.80 times source CPU in the two-worker check. |
| con-ron | About 220–400 numerical CPU-hours, plus about 4–6 hours of parsing. The same complete H1 owner used 1.93 times source CPU in the two-worker check. |
| Export size | Five H3 spatial catalogs alone encode about 35.8 GB of decimal digits before endpoints, expressions, H1, and proofs. This is not a measured size for the complete export. |

Three original H3 row closures sharing one case catalog produced about 7 GiB
with a formatting-only native serializer. Both independent checkers exceeded
5,400 s before acceptance or reported parse completion. A timeout is neither
acceptance nor rejection. A 64-plane shift-encoding experiment substantially
improved reader behavior, but no full-catalog or full-release result was established.

The study's whole-release memory allowances and 150–200 GiB workspace estimates
are planning values. A complete combined export and replay would require a
separate measured verification run. This release records the complete Lean build and
the exact narrower independent-checker results without extrapolating those
results into unconditional independent acceptance.

The verbatim study report is preserved as
`verification/feasibility/REL_FEAS.md.gz`, with its uncompressed SHA-256 in
`verification/feasibility/manifest.json`. Its paths are historical diagnostics,
not dependencies of the release commands.
