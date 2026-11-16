STATUS: COMPLETE

The requested files are [sec8-inputs.tex](sec8-inputs.tex) and [app-input-contracts.tex](app-input-contracts.tex). They contain all 22 assigned labels in plan order. The original unconditional `t:H1` and all 20 Appendix C statements match the plan exactly after whitespace normalization. Only the certificate-method sentence in `t:inputs` is amended to identify the permitted Bareiss fallback.

All mathematical lemmas are proved. The numerical checks are specified as finite integer assertions over regenerated objects and archived witnesses, for the separately assigned Lean verification. Exact native reruns passed for H1, H2, all five stationary potentials, and all five rational prefixes. H1 carries no extra certificate premise: the allowed fallback covers the blocks whose nonzero Gram factors were not retained.

| Label | Written? | Depends on |
|---|---|---|
| `t:H1` | Yes, original unconditional statement and complete proof account | `d:pattern`, `l:moments`, `l:Iw`, `l:leaf`, `l:integercheck`, `l:gram-residual`, `l:Ostruct`, `l:sector`, `l:inversion`, `c:reduce`; archived local pattern, representation, inversion and factor records |
| `t:inputs` | Yes, unconditional; certificate-method wording amended as documented below | `t:H1`, `h:H1`, `h:H2`, `p:H2-test`, `l:alm`, `l:H2-CV`, `p:automaton10`, `p:stationary-check`, `l:stationary-assembly`, `h:H3` |
| `d:memory-automaton` | Yes, exact definition; successor closure explained | `d:weights` |
| `d:memorygrowth` | Yes, exact definition | `d:memory-automaton`, `d:weights` |
| `l:alm` | Yes, full proof, including uniform initial data | `d:memorygrowth`, `h:H2` |
| `l:H2-dihedral` | Yes, full proof, including the counts 916 and 115 | `d:memorygrowth`; elementary bond counting and the orbit-stabilizer identity |
| `p:H2-test` | Yes, explicit archived-vector integer checks, extrema and an equality row | `d:memorygrowth`, `l:H2-dihedral`; `data/h2_exact_m6k1_r5.json` |
| `l:H2-CV` | Yes, full proof of `C_V=10` | `l:alm`, `p:H2-test`, `d:weights` |
| `l:automaton-quotient` | Yes, full proof of well-definedness, backward intertwining and stopped sums | `d:memory-automaton` |
| `p:automaton10` | Yes, raw reconstruction and finite quotient check specified | `l:automaton-quotient`; `data/windows_m10_min.txt` |
| `d:phaseweights` | Yes, exact definition; free rewards expanded | `d:kernel`, `d:kernel-order`, `d:memory-automaton` |
| `l:phase-expansion` | Yes, full proof for both responding types and every prefix split | `d:phaseweights`, `d:kernel` |
| `d:stationary-walk` | Yes, exact definition; backward rows made explicit | `d:phaseweights`, `p:automaton10`, `l:automaton-quotient` |
| `l:stationary-domination` | Yes, full proof, including permanent bond rules and `L>=m+2` | `d:stationary-walk`, `l:phase-expansion`, `l:automaton-quotient`; `b'_tau<=b_tau` |
| `l:Bellman-soundness` | Yes, finite induction and nonnegative supremum proved | Nonnegative finitely branching transition sums only |
| `d:stationary-certificate` | Yes, exact contract; all coefficient ceilings reconstructed by rational formulas | `d:stationary-walk`, `l:log-mean-bounds`, `d:kernel-order` |
| `l:stationary-local-global` | Yes, full proof at inside, outside and terminal states | `d:stationary-certificate`, `l:Bellman-soundness` |
| `d:prefix-bound` | Yes; exact enumeration, phase updates, short sorting, integer accumulation and endpoint lookup justified | `d:kernel-order`, `d:phaseweights`, `d:stationary-certificate` |
| `l:prefix-domination` | Yes, full proof, uniform in every finite cutoff | `l:stationary-domination`, `l:stationary-local-global`, `d:prefix-bound`, `l:phase-expansion`, `l:Bellman-soundness` |
| `l:kernel-reflection` | Yes, full proof including shifts and tie ordering; only row B reduced | `d:kernel`, `d:kernel-order` |
| `p:stationary-check` | Yes, all five integer-array and cleared rational-prefix assertions specified | `p:automaton10`, `d:stationary-certificate`, `d:prefix-bound`; five archived stationary files |
| `l:stationary-assembly` | Yes, full proof with exact nine-decimal integer ceilings | `p:stationary-check`, `l:prefix-domination`, `l:kernel-reflection`, `h:H3` |

## Deviations

1. **The H1 certificate-method clause of `t:inputs` uses the permitted Bareiss fallback.** The plan says “by the operator-only Gram/residual certificates of Appendix D”; the final text says “by the operator-only certificates of Appendix D, using the supplied Gram/residual checks and its Bareiss fallback.” The mathematical H1 assertion, its unit-vector quantifiers, both thresholds, and every other numerical conclusion are unchanged.

   Justification: `compfeas/report.md` and the amended risk register explicitly say that only representative nonzero Gram factors were retained. The archive supplies the chosen representation/inversion for all 7,962 effective patterns, and two nonzero factors. It does not supply the other 3,732 nonzero factors. Lemma `l:integercheck` and the Lane C acceptance criteria explicitly permit Bareiss as a fallback. The final contract uses Gram/residual checks for the 8,439 directly dominant blocks and the two supplied nonzero factors, and exact Bareiss for the remaining 3,732 blocks. Thus it uses the supplied witnesses without an inversion search, factor search, Cholesky generation, or a new certificate candidate. The sector, inversion and reduction lemmas complete the pointwise proof for either positivity route. Section 8 also proves why removing a verified positive common scalar preserves the exact Bareiss requirements for the reconstructed matrix itself.

2. **No other statement deviation.** `t:H1` and all 20 Appendix C statements retain their exact planned text. `t:inputs` retains all mathematical conclusions and constants. The added local enumeration, data reconstruction, prefix-recursion and coefficient-ceiling descriptions make the finite checks explicit. No periodic remainder, C-row symmetry, parity improvement, physical-window estimate or gap conclusion is used.

## Checks run

All commands ran in `REV_C2`; inputs were read only. No sub-agents were launched. At most four single-threaded checking processes were active together: three H1 matrix workers and one separate sample-factor check. NumPy/BLAS thread counts were set to one. This respects the four-core limit. No certificate candidate was searched for or regenerated.

1. **Statement and interface audit:** `python3 audit_sources.py`. All 22 labels occur once and in plan order. The original `t:H1` and all 20 Appendix C statements match the plan. Only the certificate-method clause of `t:inputs` differs, as documented above. The audit also checks mathematical delimiters and collects external references. Output: [checks/source_audit.json](checks/source_audit.json).

2. **Independent small exact checks:** `python3 verify_contracts.py small`. The script regenerates all raw windows through memory ten and checks the archive without importing a stored transition matrix. Results include:

   - Raw counts through memory ten: `4,12,36,108,316,916,2628,7500,21268,60092`.
   - All 916 raw H2 rows satisfy the **exact** `q_*` inequality; the maximum equals `1119948287353/1120437614225`. All 115 stored orbit codes, their integer vector entries, row sums and orbit sizes agree with regeneration. Vector minimum/maximum: `186377076276` and `1000000000000`. Canonical code 428 attains the maximum row ratio.
   - The exact rational finite-base majorant is below 10. The proof also gives a small-integer comparison through `15/14`.
   - Every one of the 60,092 memory-ten raw rows agrees with the 3,741-state quotient, including representative membership, surjectivity, direction labels, admissibility, kind, successor and the final-direction condition. Quotient edge counts: `2516,5032,1872`.
   - All four diagonal and all 80 response-ceiling entries in `stationary_weights.h` agree with exact rational reconstruction. The exact phase-step common denominator is `12139925673538045870080000`.
   - Both rows of logarithmic-mean rational endpoint inequalities pass. All five logged prefix fractions obey the prescribed nine-decimal ceilings. Their ceiling sums give `993014271/10^9` in B and `1181674468/10^9` in C, with the required exact `rho_0*h` comparisons.

   Output: [checks/small_checks.json](checks/small_checks.json).

3. **All five stationary files, independently of their generator:** compiled the archived checker locally with

   ```sh
   gcc -O2 -I /home/ubuntu/aklt/compfeas/experiments \
     /home/ubuntu/aklt/compfeas/experiments/check_stationary_integer.c \
     -o check_stationary_integer -lz -lm
   python3 verify_contracts.py stationary
   ```

   Every case B/N, B/W, C/N, C/W and C/S passed with `bad=0`, `cap_fail=0`, and `terminal_fail=0`. Each regenerated quotient has 60,092 raw windows and 3,741 states. Each file checks 297,469,356 nonterminal local component inequalities, plus the free rows, caps, positivity and terminal values. The maximum observed `U` is 43,674,194 and maximum `Z` is 45,149,758. Individual evidence logs are the five `checks/*_integer.txt` files. The reconstructed mathematical rows and the proof of soundness, rather than these exit codes, specify the certificate obligations.

4. **Fresh exact prefixes against the full archived potential:** `python3 verify_contracts.py prefix`. [prefix_checker.py](prefix_checker.py) is a local copy of the archived exact evaluator with only storage and output changes: Python `array` replaces NumPy, the source root remains read only, and all output is redirected here. The phase coefficients, short ordering, geometry and rational accumulation are unchanged. Every compact lookup is copied directly from its full phase/window/spatial row while the gzip stream is decoded. All five computed fractions and all enumeration counts equal the archived exact records. Across the cases there are 708,097 nodes, 451,270 surviving prefixes and 4,471 short first hits. Outputs are the five `checks/*_exact_prefix.json` and corresponding `*_prefix.txt` files. No C prefix sum or rounded decimal is used by this evaluator.

5. **LaTeX:** [compile-wrapper.tex](compile-wrapper.tex) copies the exact preamble, macros and theorem declarations from the read-only `manuscript-corrected/main.tex` and includes only the two requested section files, as §8 and Appendix C. Two final passes of `pdflatex -interaction=nonstopmode -halt-on-error -file-line-error compile-wrapper.tex` succeeded, producing [compile-wrapper.pdf](compile-wrapper.pdf), 18 pages. The final log has no undefined commands, LaTeX errors or overfull boxes. Undefined references are exactly the other-file labels listed below; all labels owned by these two files resolve. Logs: [checks/latex-final-pass1.txt](checks/latex-final-pass1.txt), [checks/latex-final-pass2.txt](checks/latex-final-pass2.txt).

6. **Complete local H1 enumeration and exact matrix checks:** `python3 verify_h1_enumeration.py` regenerates the raw status/kept-set assignments, their admissible marked out-neighbours and their effective reflection classes. It reproduces 106,101 consistent assignments, 184,914 marked assignments, 123,339 marked assignments in the N/E reduction, and all 7,962 archived effective classes, with zero missing. Its finite options and filtering are justified mathematically in §8. Output: [checks/h1_enumeration.json](checks/h1_enumeration.json).

   The archived operator constructor was then run with every fixed representation/inversion choice, using [verify_h1_fallback.py](verify_h1_fallback.py). The wrapper replaces the source's floating shadow bounds for nonnegative contractions and weighted additions with integer bounds checked **before** the operations, checks every moment-tensor entry against the exact rational formula, and checks every Bareiss division with `divmod`. It preserves the actual pattern, polynomial, Pauli and sector reconstruction and performs no certificate search. Native NumPy 2.5.5 was installed only under `/tmp/rev_c2_numpy`; input modules were imported with bytecode writes disabled.

   ```sh
   PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
     PYTHONPATH=/tmp/rev_c2_numpy:/home/ubuntu/aklt/compfeas/programs/h1-local/code \
     python3 verify_h1_fallback.py
   ```

   All 7,962 patterns and 12,173 supported central-sector blocks passed. Exactly 8,439 blocks passed direct strict diagonal dominance. All 3,734 remaining blocks passed exact Bareiss as an independent check, including the two blocks for which a stored Gram factor is available. There were 93,614 positive pivots, 57,970,522 exact update divisions, zero nonexact divisions and zero failures. The largest block has dimension 179; the largest pivot after positive common-scalar removal has 7,607 bits. Every guarded nonnegative contraction bound has at most 44 bits. Three workers completed in about 242 seconds wall time; no native timing is asserted for Lean. Summary: [checks/h1_fallback_summary.json](checks/h1_fallback_summary.json). The three worker JSONL files give every checked pattern and sector, and their summaries and output logs are retained in `checks/`.

   Finally, [verify_h1_gram_samples.py](verify_h1_gram_samples.py) regenerated the two supplied nonzero-factor sectors, compared their matrices entry by entry with the stored normalized arrays, and checked every residual row. Both use `g=1600,d=1,S=1`, dimension 131. The minimum margins for the actual reconstructed matrices are `6820166897600` (pattern 5420) and `27361669345600` (pattern 7697). Output: [checks/h1_gram_samples.json](checks/h1_gram_samples.json). The final certificate contract uses these two Gram witnesses and therefore needs the Bareiss fallback for 3,732 blocks; the independent native Bareiss run additionally checked those two blocks. A final metadata audit checks all threshold/type/out-neighbour agreements, reconstructed vector dimensions and positive denominators, verifies that the per-pattern logs cover every index exactly once, and relates each Gram sample to its regenerated sector. Output: [checks/h1_record_audit.json](checks/h1_record_audit.json); reproduction: `python3 audit_h1_records.py`.

## References unresolved in the standalone wrapper

These 17 labels are supplied by other Lane C files:

`c:reduce`, `d:kernel`, `d:kernel-order`, `d:pattern`, `d:weights`, `h:H1`, `h:H2`, `h:H3`, `l:Iw`, `l:Ostruct`, `l:gram-residual`, `l:integercheck`, `l:inversion`, `l:leaf`, `l:log-mean-bounds`, `l:moments`, `l:sector`.

Every label owned by these two files resolves after the reference passes. No A/B result is cited. The numerical statements remain finite verification targets for Lean, as requested; all stated mathematical implications and the native exact verification evidence are present.
