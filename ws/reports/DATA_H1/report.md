STATUS: COMPLETE

# DATA_H1 — complete saved operator Gram/residual witnesses

All **7,962 patterns and 12,173 central exchange blocks** were regenerated,
saved, and checked from disk. **8,439** blocks use L=0 and **3,734** use a
quantized triangular Gram factor. No block failed. No Lean was run or written;
no sub-agents were used.

The complete dataset is [/home/ubuntu/aklt/data/h1/](/home/ubuntu/aklt/data/h1/).
Its [index](/home/ubuntu/aklt/data/h1/index.json),
[complete format specification](/home/ubuntu/aklt/data/h1/README.md),
[checksum manifest](/home/ubuntu/aklt/data/h1/SHA256SUMS), three executable tools,
two original constructor files, and both original input files are retained.
The input/source snapshots are byte-for-byte copies from `compfeas/programs/`.
The operator choices agree with the feasibility study's two complementary runs.

## Format description

Schema: `h1-gram-residual-v1`. Sixteen gzip JSON-lines files hold consecutive IDs:
500 patterns per file, except the final 462. Every line is one pattern. JSON
integer literals are arbitrary precision; a consumer must not round them through
binary64. Sorted object keys, compact ASCII JSON, LF line endings, gzip level 9,
mtime 0 and empty gzip filenames make the output deterministic in the recorded
runtime. The index records exact ranges, counts, sizes, SHA-256 for each compressed
chunk, and hashes of support files. Timings and machine information occur only
in the separate logs.

Each line contains:

| Field | Exact content |
|---|---|
| `pid` | Contiguous zero-based original ID. |
| `type`, `threshold` | `straight`, [961,1000] for out=(0,1); `turn`, [187,200] for out=(1,0). |
| `pattern.out` | Marked outgoing neighbour; incoming neighbour is (0,-1). |
| `pattern.sites` | Eight [x,y,status] triples in ring order e,c0,N,c1,W,c2,s,c3. `u` uniform, `d` diluted, `x` absent effective site. |
| `pattern.present` | All effective kept bonds, each a sorted pair of coordinate pairs, with the bond list sorted lexicographically. Unlisted bonds are absent. |
| `representation.model`, `refined` | Always `covered`, false. |
| `representation.leafred`, `tip_radius` | Chosen boolean leaf reduction and exact [3,5] tip radius. |
| `representation.nslots`, `slots` | Slot count and ordered [site_x,site_y,role] triples (`tip`, `leaf`, `slot`). |
| `representation.leaf_radii` | Reduced corners as [x,y,a,b], radius a/b, in ring order. |
| `representation.moment_denominator` | Positive integer common denominator D of the selected tensor network. |
| `representation.inversion` | Increasing zero-based inverted slot indices; both slots of a corner flip together. |
| `blocks` | Ordered block records, one per exchange-parity class, defined next. |

Coordinates: V=(0,0), e=(1,0), c0=(1,1), N=(0,1), c1=(-1,1),
W=(-1,0), c2=(-1,-1), s=(0,-1), c3=(1,-1).
The four tip endpoints are (2,0),(0,2),(-2,0),(0,-2).
These are **effective** statuses/kept bonds from the supplied enumeration;
irrelevant statuses of cancelled sites are not claims about original full status
configurations. They suffice to reconstruct the selected operator network.

Visit sites in ring order. A present tip bond gives one qubit. Every live corner
starts with two slots. A pendant corner with leaf reduction enabled becomes one
qubit of radius 1/2 (`u`) or 1/3 (`d`). Other uniform corners use the integer basis
(uu,ud+du,dd); diluted corners use (uu,ud+du,dd,ud-du). These bases are
unnormalized and the operator change is a congruence. Each group has local 2Sz
labels (1,-1), (2,0,-2), or (2,0,-2,0), respectively; only ud-du has exchange bit
1. All other exchange bits are 0.

Tensor-product basis order has the last group varying fastest. Accumulate `par`
by `par = 2*par + bit` for **every group**, and sum the local 2Sz values. For each
par select the least absolute 2Sz, preferring positive in a tie. Each block holds
`n`, `exchange_parity=par`, `two_sz`, `label=1000*par+two_sz`, the increasing full
`basis_indices`, `M_lt`, and `witness`. This is the same central-sector convention
as the original 12,173-block workload. Other magnetization sectors are covered
by the required total-spin lemma; their separate matrices are not exported.

`M_lt` is the lower triangle of the **unreduced** integer matrix
**M=5qA−3pA′**, in the `basis_indices` order. Here A and A′ are the inverted Pauli
operators of the integer tensors 3D·Z_cur and 5D·Z_next, after the selected basis
congruences. No division by a gcd or basis norm is hidden in M.

A packed triangle lists (0,0),(1,0),(1,1),(2,0),...; offset i(i+1)/2+j for i≥j.
The matrix M is symmetric. `witness` contains positive integers `g,d,S`, packed
`L_lt`, and `min_margin`. L is lower triangular with zero upper entries. Empty
`L_lt` denotes the n-by-n zero matrix; otherwise its length is n(n+1)/2.
Check, entirely in integers,

```
E[i,j] = d*S*S*M[i,j] - g*sum(k=0..min(i,j), L[i,k]*L[j,k])
margin[i] = E[i,i] - sum(j != i, abs(E[i,j])) > 0
min_margin = min_i margin[i]
```

All residual diagonals must be positive. Strict symmetric diagonal dominance
proves E positive definite; gLLᵀ is positive semidefinite, hence M is positive
definite. This implication needs only g,d,S>0. The exporter chooses g as a gcd,
but that gcd property is not a checker premise. Zero-factor blocks use d=S=1.
E is recomputed rather than stored. The README gives the exact site moments,
contractions, inversion, bases, sector ordering, all field semantics and commands
in sufficient detail to implement a Lean exporter.

## Totals

All counts below are measured from the saved files by the independent checker,
except storage sizes, supplementary bit statistics, and runtime measurements,
which have their own retained logs.

| Quantity | Value |
|---|---:|
| Patterns | 7,962 |
| Straight / turn patterns | 2,696 / 5,266 |
| Leaf-reduced / unreduced representations | 7,960 / 2 |
| Blocks | 12,173 |
| Zero-factor / Gram blocks | 8,439 / 3,734 |
| Maximum block dimension | 179 |
| Full symmetric matrix entries, Σn² | 4,742,248 |
| Stored matrix triangle entries, Σn(n+1)/2 | 2,443,401 |
| Stored triangular factor entries | 2,184,033 |
| Nonzero factor entries | 1,896,603 |
| Triangular Gram products | 60,154,555 |
| Residual triangle entries checked | 2,443,401 |
| Dominance rows checked, Σn | 144,554 |
| Maximum original M entry bits | 56 |
| Maximum generator-normalized M/g entry bits | 46 |
| Maximum L entry bits | 23 |
| Maximum individual L-product / Gram-sum bits | 46 / 46 |
| Maximum residual E entry bits | 48 |
| Maximum scaled matrix dS²M entry bits | 56 |
| Maximum g / d / S bits | 36 / 1 / 5 |
| Maximum dS² bits | 9 |
| Maximum D bits | 40 |
| Largest g | 43,875,000,000 |
| d values | 1 for every block |
| S values | 1 for 12,166 blocks; 16 for 7 blocks |
| Minimum recomputed row margin | 195 |
| Compressed chunk bytes | 12,333,537 |
| Uncompressed JSONL bytes | 40,473,435 |
| All regular bundle file bytes, including README/tools/inputs/manifest | 16,457,713 |

A bit length means abs(x).bit_length(), with zero having length 0. Gram products
count every term in the lower-triangle dot products, including zero terms:
Σ n(n+1)(n+2)/6 over the 3,734 factored blocks. Zero-factor blocks contribute zero.
The count excludes scalar scaling, row sums, and matrix construction. It agrees
exactly with the feasibility study; so do the factor entry and block totals.

The two unreduced patterns are **3596 and 7725**. The seven S=16 blocks are
(pid,label): (1488,0), (4784,0), (4900,0), (5389,0), (5467,0), (5469,0), (7725,1).

| Block dimension | Blocks |
|---|---:|
| 1 | 307 |
| 2 | 1,186 |
| 3 | 1,499 |
| 4 | 1,052 |
| 5 | 169 |
| 6 | 1,408 |
| 7 | 1,621 |
| 10 | 1,234 |
| 13 | 24 |
| 14 | 1,165 |
| 18 | 745 |
| 20 | 212 |
| 25 | 577 |
| 26 | 72 |
| 35 | 35 |
| 36 | 323 |
| 48 | 200 |
| 50 | 68 |
| 66 | 188 |
| 91 | 12 |
| 96 | 24 |
| 131 | 28 |
| 179 | 24 |

## Verification log

**Independent positivity verification: PASS, 12,173/12,173 blocks.**
The fresh command was:

```sh
python3 -I -u /home/ubuntu/aklt/data/h1/tools/verify.py \
  --summary /home/ubuntu/aklt/reports/DATA_H1/verification-summary.json
```

[Full verification JSONL](/home/ubuntu/aklt/reports/DATA_H1/verification.jsonl)
and [machine-readable totals](/home/ubuntu/aklt/reports/DATA_H1/verification-summary.json).
This verifier uses only the Python standard library and unbounded integers. It
imports neither the exporter, NumPy, nor the original constructor. Its inputs
are saved files only. It verifies support/chunk SHA-256, ranges, IDs, provenance
status/bond/choice agreement, independently derived slots/leaves/basis indices
and exchange-sector coverage, scales, shapes, every Gram/residual row and the
stored minimum margin. The saved M triangle defines symmetry explicitly.
It does not assume a generator success flag or any floating eigenvalue.

**Fresh matrix reconstruction: PASS, 12,173/12,173 blocks.**
[Reconstruction log](/home/ubuntu/aklt/reports/DATA_H1/reconstruction.jsonl).
A separate process rebuilt every A,A′ from the frozen source inputs with the
snapshotted original constructor, compared both triangles of every saved M to
5qA−3pA′, checked D, slots, leaves and sector indices, and rechecked zero imaginary
parts, symmetry, uniform-corner antisymmetric kernels and inter-sector zeros.
This audit is independent of the exporter's memory and factor search, but uses
the **same original constructor**, so it is not a second independent derivation
of the moment/operator construction. The positivity implementation is independent.

| Pattern IDs | Patterns | Blocks | Zero L | Gram | Integer residuals | Reconstructed M |
|---|---:|---:|---:|---:|---|---|
| 0000–0499 | 500 | 790 | 724 | 66 | PASS | PASS |
| 0500–0999 | 500 | 993 | 587 | 406 | PASS | PASS |
| 1000–1499 | 500 | 691 | 372 | 319 | PASS | PASS |
| 1500–1999 | 500 | 681 | 549 | 132 | PASS | PASS |
| 2000–2499 | 500 | 701 | 494 | 207 | PASS | PASS |
| 2500–2999 | 500 | 762 | 628 | 134 | PASS | PASS |
| 3000–3499 | 500 | 848 | 450 | 398 | PASS | PASS |
| 3500–3999 | 500 | 634 | 428 | 206 | PASS | PASS |
| 4000–4499 | 500 | 778 | 706 | 72 | PASS | PASS |
| 4500–4999 | 500 | 1,015 | 583 | 432 | PASS | PASS |
| 5000–5499 | 500 | 686 | 374 | 312 | PASS | PASS |
| 5500–5999 | 500 | 694 | 576 | 118 | PASS | PASS |
| 6000–6499 | 500 | 689 | 510 | 179 | PASS | PASS |
| 6500–6999 | 500 | 750 | 598 | 152 | PASS | PASS |
| 7000–7499 | 500 | 900 | 500 | 400 | PASS | PASS |
| 7500–7961 | 462 | 561 | 360 | 201 | PASS | PASS |

**Deterministic regeneration: PASS.** A second complete run into
`/home/ubuntu/aklt/scratch/DATA_H1/replay/` produced byte-for-byte identical data
for all sixteen compressed chunks and `index.json`, not just equal parsed
matrices. [Comparison log](/home/ubuntu/aklt/reports/DATA_H1/determinism.jsonl).
[Second generation log](/home/ubuntu/aklt/reports/DATA_H1/replay-generation.jsonl).

**Negative controls: PASS.** Two valid sample blocks were accepted. Seven invalid
cases were rejected: negative M diagonal, zero scale, truncated L, oversized L,
false stored margin, truncated M, and a corrupted compressed chunk.
[Control log](/home/ubuntu/aklt/reports/DATA_H1/negative-controls.jsonl).

| Run | Wall seconds | Workers / memory |
|---|---:|---|
| Export all witnesses | 43.936 | 16 one-thread workers; max worker RSS 472,120 KiB |
| Independent integer verification | 12.278 | 1 process; peak RSS 60,428 KiB |
| Fresh matrix reconstruction | 40.998 | 15 one-thread workers, overlapping the 1-process verifier |
| Complete duplicate export | 43.628 | 16 one-thread workers |

The sum of the sixteen first-export worker peak RSS values was 4,609,384 KiB;
this is an upper bound on their simultaneous RSS, not a measured aggregate peak.
The parent and verifier use additional small memory. Runs stayed well within
64 GB RAM and 20 GB disk. All outputs and the scratch NumPy installation are
under the three authorized roots. Numerical BLAS/OpenMP thread counts were
forced to one. Runtime: Python 3.12.3, NumPy 2.2.6 / OpenBLAS 0.3.29,
zlib 1.3, Linux x86_64. No external source tree was modified.
[First export log](/home/ubuntu/aklt/reports/DATA_H1/generation.jsonl).
All four process stderr logs are empty. The negative-control subprocess error
was expected, captured, and checked for the specific hash rejection.

Index SHA-256: `6451c08de041cbf8def4a6c87e6b45b23e17a1152eab4917b7836aaeb19a66f7`.

Full bundle checksum-manifest SHA-256: `f0d5dcffb91c97ee0f24ec6a979ed221c9b01b6651d6f4e1365e5b3958c18ba2`.
Run `sha256sum -c SHA256SUMS` from the data directory to check all 25 listed files.
The manifest does not hash itself; the digest above identifies it.

## Limitations and remaining proof work

This is a complete saved witness export and computational verification, not a
Lean proof. The independent checker proves positivity of the saved integer
matrices computationally. Its separate full reconstruction audit establishes
agreement with the supplied constructor, whose nonnegative int64 contractions
use floating shadows to guard bounds and whose subsequent operator work uses
integer arithmetic with bounds and Python-integer fallback. Floating Cholesky
is candidate generation only; no floating result enters the residual acceptance
criterion. Cross-version/BLAS reproducibility is not asserted beyond the two
complete byte-identical runs in the retained environment.

No new proof of the original geometric enumeration was attempted here. The
retained pattern records are effective representatives after cancellation.
Lean must prove enumeration coverage and the relation from those records to
the original integrals, including moments/denominators, tip/leaf reductions,
inversion/coherent-state transfer, exchange bases/discarded kernels, decoupling,
and the central-sector/total-spin reduction. It must reconstruct each M from
the definitions, relate that result to any imported literal matrix, prove the
Gram/residual implication, and kernel-check all integer obligations. Hashes,
Python checks and stored matrices cannot replace those proofs.

## ORCH-SUMMARY
- Complete dataset: `/home/ubuntu/aklt/data/h1/`; no Lean, no sub-agents.
- 7,962 patterns; all 12,173 central exchange blocks saved.
- 16 deterministic gzip JSONL chunks; index and complete SHA-256 manifest retained.
- Each pattern includes effective statuses/kept bonds, type, p/q, representation and inversion.
- Each block includes ordered sector indices, unreduced M, positive g,d,S, triangular L and margin.
- 8,439 zero factors; 3,734 Gram factors; largest block 179.
- 2,184,033 factor entries; 60,154,555 triangular Gram products.
- Independent stdlib integer checker passed every block from saved files.
- Separate fresh reconstruction matched every M using the supplied exact constructor.
- Complete duplicate export was byte-identical; seven corruption controls were rejected.
- Chunks: 12,333,537 compressed bytes; 40,473,435 uncompressed bytes.
- Format/reproduction: data `README.md`; source, tools and original inputs are included.
- Logs/totals: `/home/ubuntu/aklt/reports/DATA_H1/`.
- Limitation: central sectors and effective patterns rely on mathematical reduction/coverage lemmas.
- Lean still must prove construction/coverage/reduction correctness and check all residual inequalities.
