VERDICT: PROVED WITH REPAIRS (actual-departure scope; two additional special mean checks; precise pin, zero-law and correlation bookkeeping)

The complete written proof is [h1tree.tex](h1tree.tex). The minimal wrapper [wrapper.tex](wrapper.tex) produces [wrapper.pdf](wrapper.pdf), a 15-page section. Theorem 1.17 proves `Z_E^τ ≥ c_type Z_{E+}^τ` for every actual non-exceptional U departure, uniformly in original pins and fixed outside spins. The constants remain `c_s = 961/1000` and `c_t = 187/200`. Proposition 1.18 explains its use in the first and second traces, including the existing twelve exceptions and their `12/5` bound, and explicitly recovers `I^τ ≥ c_type J^τ` for the type-dependent response coefficients of paper Lemma 7.6.

Repairs and qualifications:

1. **The replacement proves the actual local conclusion, not the literal larger definition of (H1).** Paper Definition 6.8 puts two artificial fields at every D corner. A physical D corner with `k` present internal bonds has at most `2-k` external factors, because its kept set has size two and D sites cannot carry original pins. The reduction uses this physical restriction. The paper's references to (H1) in Sections 6–7 should instead invoke Theorem 1.17, with Lemmas 7.2 and 7.3 supplying its geometric hypotheses. This proof makes no claim that the larger covered-pattern assertion is false.
2. **There are two further necessary mean checks beyond the advertised 21 cube checks.** The reduction needs the U bounds for radii `(1,1,1/10)` and `(1,1,3/25)`, giving `18/35` and `137/265`. Lemma 1.7 proves the coordinate reduction and specifies their exact Bernstein tests. The additional supplied row `r=1/25` is replayed but unused.
3. **A two-bond upper D corner must lose a zero endpoint exactly.** Its positive decomposition is `(3/5) U + (2/5) δ_0`, with no external fields. When an endpoint disappears, its active U term integrates to exactly `1`. Two zero fields may be inserted and enlarged to `(1,1)` only if its bridge is retained. Replacing the one-bond term by a general two-field U leaf would introduce an unnecessary larger model.
4. **The lower correlation needs a specific exception to arrival integration.** When E and W survive, N does not, the arrival joins both lower corners, and both corners are U, the five-vertex lower path is retained intact. Other cases use the positive auxiliary-U split or sequential leaf integration. Lemma 1.14 specifies every order, mean bound, field count and common weight. The naive independent replacement would allow `m_E = (226/495)e₁`, `m_W = -(226/495)e₁`, N absent and E outgoing, giving ratio `683999/735075 < 187/200`. This is an exact counterexample to the discarded larger intermediate model, not to the actual local inequality.
5. **A disappearing outgoing mark stays absent.** When two non-outgoing marks remain, `Znext` still contains their pair term divided by five. Fixed D neighbours attached only to their covering tips retain the D law and give radius `3/25`. Both facts are included in the models and the exact reconstruction.
6. **Radius enlargement uses separate affinity, not monotonicity of a partition ratio.** Zero fields, shorter fields and shorter mean vectors are explicit convex combinations of boundary directions, with the same coefficients for current and next. Path reversal and component relabeling preserve laws and marks. The formal field `3R` used to encode an isolated mean is only a degree-two tensor identity, even when `3R > 1`.
7. **The older 19 boxes in `closed_boxes.json` are not the present scalar certificate.** The 38-model family has 22 scalar cases, certified directly from its own radii and quadratic tests.

No actual local case is left uncovered, and no false required inequality or counterexample was found. The coverage proof includes an explicitly specified, independently implemented finite combinatorial check. It still enumerates local kept sets; the reduction in primitive inequalities does not purport to eliminate that Boolean enumeration. No Lean-kernel verification is claimed: this is a complete computer-assisted mathematical proof with exact native rational/integer replays and the paper's numbered moment/sector lemmas.

The computer-checked inputs and their sizes are:

| Input | Exact check | Size |
|---|---|---:|
| Coverage from paper Definition 6.8 kept-set rules | Generate masks; test agreement at nonremoved ends; generate branches; compare every reduced list to a dominating model; verify equality of maximal lists | 2,048,000 possible raw choices; 106,101 consistent choices; 184,914 outgoing choices; 123,339 N/E choices; 7,962 effective reflection classes generated from the rules |
| Reduced geometry and radii | Apply the proved case rules, preserve laws/outgoing marks, compare rational radii | 24,741 binary branches, including 981 empty-mark branches; 20 decorated geometries; exactly 38 maximal models |
| Isolated-site mean bounds, Lemma 1.6 | Reconstruct the polynomial and all degree `(2,2,2)` Bernstein coefficients; compare stored coefficients and signs | 21 triples; 567 coefficients; at most 53-bit numerator/denominator |
| Two unit fields and one small field, Lemma 1.7 | Reconstruct degree `(4,4)` Bernstein coefficients after the orthogonal-coordinate estimate | 2 necessary cases; 50 coefficients; at most 27 bits. Replay additionally checks the unused `1/25` case, for 75 comparisons total |
| Independent mean models, Lemma 1.8 | Test `L(±1)`, `Q(±1)`, and an interior quadratic vertex when present | 22 models; 89 exact rational comparisons |
| Pauli-sector reconstruction, Definition 1.9 and Lemma 1.10 | Reconstruct both tensors from degree-four moments; form the chosen inversions and integer-coordinate central forms; compare every matrix entry to its witness | 16 matrices; dimensions at most 66; 14,502 matrix cells. Both tensors over all models have 1,465,600 dense cells and 122,884 nonzeros |
| Gram/residual positivity, Lemma 1.10 | Verify positive scales, lower-triangular factors, and every residual row | 16 nonzero Gram witnesses; 7,443 triangular factor entries; 129,491 triangular Gram products; 384 residual rows; matrix entries at most 37 bits and factors at most 19 bits |

The 16 dimensions, in model-index order, are `14, 7, 25, 14, 14, 25, 7, 14, 66, 36, 14, 25, 14, 7, 66, 36`. All reconstructed matrices match the supplied normalized matrices exactly. All Gram residual margins are strictly positive. Table 3 of the proof gives the inversion, normalization, scale and minimum margin for each; the checker tests every row, not only each minimum.

The self-contained exact replay code is [checks/audit.py](checks/audit.py) and [checks/reconstruct.py](checks/reconstruct.py). It imports no catalogue or original certificate-generation program. In particular, it never reads `pext7962.json`, the old 7,962 operator inequalities, or the old inversion records. The required witness files are copied into [data/](data/); their archival `pid` fields are ignored. The exact model list is also printed in full in Table 1 of the proof.

From this directory, run:

```bash
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  PYTHONPATH=/home/ubuntu/aklt/reports/MATH_FIT/pydeps \
  python3 checks/audit.py all

PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  PYTHONPATH=/home/ubuntu/aklt/reports/MATH_FIT/pydeps \
  python3 checks/numerical.py

pdflatex -interaction=nonstopmode -halt-on-error wrapper.tex
pdflatex -interaction=nonstopmode -halt-on-error wrapper.tex
```

Only NumPy is needed beyond Python's standard library; the `PYTHONPATH` entry uses the dependencies already supplied with MATH_FIT. All generated files stay in this directory. The exact replay takes about 13 seconds here, including about 5 seconds for independent tensor/matrix reconstruction and positivity. Receipts are [data/coverage_receipt.json](data/coverage_receipt.json), [data/mean_receipt.json](data/mean_receipt.json), [data/finite_receipt.json](data/finite_receipt.json), and [logs/final_audit.log](logs/final_audit.log).

The separate floating falsification tests used seed `20261116`: 256 randomly chosen effective configurations generated from the paper rules, plus one source configuration for every maximal row, with six field assignments each. Fields have the actual D-corner capacity; shorter and unit fields are both sampled, with covering tip radius `3/5`. This tests the permitted local field relaxation without assuming simultaneous global realizability of every independent outside direction. There were 1,764 field assignments and 6,336 binary branches, including 522 auxiliary-arrival splits and 24 branches preserving the lower path. The tip-reduced current and next sums were separately compared before and after the law mixture and the arrival/leaf integration chain. Maximum normalized identity error, `max|a-b| / max(1,max|a|)`, was `8.881643014828648e-16`; every sampled mean bound and every sampled H1 ratio passed. The smallest sampled ratio margin over its threshold was `0.019535315917221123`. These tests are diagnostics and are not used as proof inputs. Details are in [checks/numerical.py](checks/numerical.py), [data/numerical_receipt.json](data/numerical_receipt.json), and [logs/numerical.log](logs/numerical.log).

The final LaTeX run has no undefined references, warnings, or overfull boxes. The build transcript is [logs/latex-final.log](logs/latex-final.log). The supplied paper and MATH_FIT directory were only read. This task does not verify the separate H2/H3 replacements or their modified closing constants.
