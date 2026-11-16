STATUS: COMPLETE

# VENDOR-PLAN

**Keep Lean `4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.**
The selected Hex, finite-chain, Physlib sl₂, TNLean AKLT, Balaban, Potts, finite-conditioning,
and LeanCert closures compile on that pin without mathematical source changes. The full selected
QICLean closure needs one small matrix-rank proof replacement; that replacement is retained and
the repaired closure builds. Moving to `4.36.0-rc1` is feasible, including Comparator, but saves
little work for these immediate imports. TauCeti still requires a substantial port at either pin.

This is a completed donor/pin audit and vendoring recommendation. Failed trial ports are reported
as measurements. Campaign sources were not changed, and namespace relocation has not yet been
implemented. The trial projects retain upstream declaration names to isolate version/API errors.

## Evidence and measurement conventions

The requested 13 repositories were fetched at the exact commits below under
`/home/ubuntu/aklt/donors/`, using depth-one, blob-filtered Git fetches. Seven additional Mathlib
snapshots and their dependency sources make the import analysis reproducible at the donors' own
pins. [Clone records](clones.json), [all clone metadata](clone-inventory.json),
[dependency fetches](dependency-clones.json), and [Mathlib dependency fetches](mathlib-dependency-clones.json)
record the materialization. Every retained donor checkout has a clean tracked worktree.

**Copy closure** means the complete explicit transitive source imports outside Mathlib and its
packages, with selected donor roots included. **Full source closure** also expands Mathlib and
its manifest-pinned packages. Every explicit import resolves, except the deliberately recorded
`Init`/`Lean`/`Std`/`Lake` toolchain boundary. Implicit `Init` is noted separately. Module lists,
per-file paths, lines, hashes for copied files, and import edges are linked for every donor.
Counts are physical Lean source lines including comments and blank lines, counting a final
unterminated line. Counts across donors overlap and should not be added as independent code.

First-pass trials are source compilation in standalone Lake projects, using a topological
`lake env lean -o ... --json` driver. Failed modules block their descendants. Error counts count
Lean error diagnostics, not failed modules, and are **lower bounds until blocked descendants
are elaborated**. The driver builds no shared dependency. Each current-pin project's
`.lake/packages` is a symlink to `/home/ubuntu/aklt/repo/.lake/packages`; the campaign is read-only.
The 4.36 trials use a separate writable Mathlib/cache copy under scratch. The projects, build
inputs, JSON summaries, and module logs are retained; generated build outputs are removed at the end.
Timings are wall-clock observations on this shared host, not controlled performance comparisons.

The [trial driver](../../scratch/VENDOR-PLAN/port.py), [source scanner](../../scratch/VENDOR-PLAN/audit.py),
and [full closure expansion](../../scratch/VENDOR-PLAN/full_audit.py) are retained in scratch.
Raw ripgrep evidence is `logs/grep-<closure>-full.log`; structured scans are in each full-closure JSON.

## Trust assessment

For every selected **donor-owned** copy closure, the comment/string-aware scan found zero proof
`sorry`/`admit`, zero axiom declarations, and zero `native_decide`/`ofReduceBool`/`ofReduceNat`/
`trustCompiler` invocations. The full `AKLT*` TNLean option adds local metaprogramming but no such
proof holes. Hex has native implementation attachments and metaprogramming, described below.

The **full imported source closure is not textually free of placeholder vocabulary**. Mathlib
and its tactic dependencies contain quotations of `sorry`/`admit`, UI suggestion code, axiom-name
inspection, and unsafe metaprogramming. Examples include `Aesop.Script.Step`, `Mathlib.Tactic.TFAE`,
`Mathlib.Tactic.Widget.Calc`, and `LeanSearchClient.Syntax`. The sampled latest Mathlib conditional
expectation file also contains `#check μ[f | m] (sorry : α)`. Econlib's old Batteries closure
contains an `axiom helper` **inside the quotation used by `proof_wanted`**, in
`Batteries.Util.ProofWanted`; its elaborator uses `withoutModifyingEnv`, so this is not an exported
mathematical axiom. Raw hits and exact lines remain in the scan evidence. `evalExpr` hits also
include ordinary symbolic tactic functions with that name; their occurrence is not a native proof.

For the built key theorems, actual `#print axioms` checks give only
`propext`, `Classical.choice`, and `Quot.sound`. This covers Mathlib's FKG/four-functions,
spectral/Rayleigh, conditional expectation and trail parity; Hex checker/scaling/congruence;
QICLean Knabe/detectability/gap/coherent integrals; finite-chain stochasticity, reversibility,
Dirichlet/Cheeger/mixing/TV; sl₂ intertwining and normalized coefficients; Balaban/Potts cuts;
finite conditioning; dyadic rounding/arithmetic/finite sums; and the selected TNLean AKLT
Hamiltonian theorems. RealRooted's key PF theorems pass on the 4.36 trial. Their logs are linked
per donor. The final campaign theorems must undergo the same audit after namespace relocation
and the manuscript-specific bridges are added; these samples are not an audit of every declaration.

## First-pass compatibility matrix

Both columns use the same selected donor sources, with their original namespaces. The current
column is before repairs; QICLean's repaired result is shown separately. Mathlib's own row is
an import-availability check rather than an attempted downgrade of the whole library.

| Donor / selected closure | Copy modules / lines | Current pin: errors (passed / failed / blocked) | 4.36.0-rc1 + Mathlib 625d8914199b |
|---|---:|---|---|
| Mathlib requested modules | 20 roots | 19 available; Echelon.Cert absent | all 20 available |
| Hex | 60 / 15,933 | 0 (60 / 0 / 0) | 0 (60 / 0 / 0) |
| QICLean | 62 / 16,695 | 1 (53 / 1 / 8) | 0 (62 / 0 / 0) |
| Physlib sl₂ | 12 / 3,521 | 0 (12 / 0 / 0) | 0 (12 / 0 / 0) |
| Finite chain | 8 / 2,440 | 0 (8 / 0 / 0) | 0 (8 / 0 / 0) |
| TNLean selected AKLT | 91 / 22,134 | 0 (91 / 0 / 0) | 0 (91 / 0 / 0) |
| Balaban | 5 / 942 | 0 (5 / 0 / 0) | 0 (5 / 0 / 0) |
| Potts cuts | 33 / 5,841 | 0 (33 / 0 / 0) | 0 (33 / 0 / 0) |
| Econlib | 6 / 1,158 | 4 (1 / 1 / 4) | 4 (1 / 1 / 4) |
| Finite conditioning | 1 / 118 | 0 (1 / 0 / 0) | 0 (1 / 0 / 0) |
| LeanCert | 23 / 12,796 | 0 (23 / 0 / 0) | 0 (23 / 0 / 0) |
| RealRooted | 12 / 3,441 | 1 (4 / 1 / 7) | 0 (12 / 0 / 0) |
| TauCeti sphere | 180 / 52,097 | 98 (78 / 28 / 74) | 64 (98 / 19 / 63) |

QICLean after the retained repair: **62/62 modules, zero errors**. The small TNLean
`AKLT`/singlet-only alternative is 35 modules / 8,389 lines, also zero errors on the current pin.
The finite heat-bath examples add up to an 11-module / 3,117-line closure, zero errors.
Normalized Physlib coefficients use a 15-module / 4,542-line closure, zero errors.
TauCeti min-max alone is 5 modules / 1,425 lines; its current-pin trial has four errors in two
modules, one blocked module. Physlib's older min-max copy remains an alternative to inspect if needed.

## Mathlib

Commit: `d3b6d8f438cd76e927d69583d94eedf857946523` ([source](https://github.com/leanprover-community/mathlib4/tree/d3b6d8f438cd76e927d69583d94eedf857946523)).
Lean: `leanprover/lean4:v4.36.0-rc2`; Mathlib is this repository itself.

The 20 requested roots are listed below. Their exact source closure at the inspected commit is
**2,869 Mathlib modules / 953,631 lines**, or
**3,158 modules / 998,312 lines** including Mathlib's source dependencies:
[module list](closures/mathlib.txt), [import edges / source evidence](closures/mathlib.json); [module list](closures/mathlib-full.txt), [import edges / source evidence](closures/mathlib-full.json).

```text
Mathlib.Combinatorics.SetFamily.FourFunctions
Mathlib.Combinatorics.SetFamily.HarrisKleitman
Mathlib.Analysis.InnerProductSpace.Spectrum
Mathlib.Analysis.InnerProductSpace.Rayleigh
Mathlib.Analysis.Matrix.Hermitian
Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
Mathlib.Combinatorics.SimpleGraph.Paths
Mathlib.Combinatorics.SimpleGraph.Walk.Basic
Mathlib.Combinatorics.SimpleGraph.Trails
Mathlib.Combinatorics.SimpleGraph.Walk.Counting
Mathlib.Combinatorics.SimpleGraph.AdjMatrix
Mathlib.LinearAlgebra.Matrix.PosDef
Mathlib.Tactic.Echelon.Bareiss
Mathlib.Tactic.Determinant.Echelon.Cert
Mathlib.MeasureTheory.Constructions.HaarToSphere
Mathlib.RingTheory.MvPolynomial.Homogeneous
Mathlib.NumberTheory.Real.GoldenRatio
Mathlib.Analysis.Normed.Algebra.Spectrum
Mathlib.Analysis.Matrix.LDL
```

At the recommended pin, 19 roots already have sources and cached oleans. The missing root is
`Mathlib.Tactic.Determinant.Echelon.Cert`; retain the existing `Mathlib.Tactic.Echelon.Bareiss`
and use Hex's checker/congruence API for H1. The current determinant implementation also has
`Mathlib.Tactic.Determinant.Bird.Cert`. No whole-library source port is recommended.
The 19-root current source closure is 3,082 modules / 978,752 lines:
[module list](closures/mathlib-current-full.txt), [import edges / source evidence](closures/mathlib-current-full.json).

Licence: Apache-2.0. Import this dependency; copy no Mathlib tree into `AKLT.Vendor`.
Preserve author headers and the licence when adapting individual proofs. The full-source scan
has the tactic/placeholder hits discussed above. [Availability](mathlib-current-availability.json),
[4.36 availability](mathlib-436-availability.json), [key axiom checks](logs/axioms-Mathlib-current.log).

## HexPosDefTheory / Hex

Commit: `3a1b9813b1d1876ae0c89f5cfc20da05547bd854` ([source](https://github.com/kim-em/hex-dev/tree/3a1b9813b1d1876ae0c89f5cfc20da05547bd854)).
Lean: `leanprover/lean4:v4.35.0-rc3`. Mathlib: `6b7abb3c7686292736be2955bd3eb9ebf63b456a`.

Exact copy closure: [module list](closures/hex-dev.txt), [import edges / source evidence](closures/hex-dev.json).
Full source closure: **2,527 modules / 773,237 lines**; [module list](closures/hex-dev-full.txt), [import edges / source evidence](closures/hex-dev-full.json).

Use `HexPosDefTheory.{Soundness,Scaling,Congruence,Quotation,Tactic}`. The complete
60-module copy set has **15,933 lines**. The proof-oriented `Soundness`/`Scaling`/`Congruence`
alternative is 55 modules / 15,241 lines; the larger dependency set already enters through
matrix/producer infrastructure. Neither selected closure imports `HexBareissTheory` at this
commit. Thus the donor report's proposed Bareiss dependency is not actually part of this copy set.

The first current-pin source pass builds all 60 modules unchanged in 49.6 s. The 4.36 pass also
has zero errors. The scan finds one `extern` exact-division attachment, two `implemented_by`
attachments and fourteen `csimp` occurrences (17 implementation-attachment hits total), plus
14 metaprogramming hits. These leave kernel definitions/proofs available. Key soundness,
scaling and congruence axiom checks pass.

A 2×2 rational `pos_def` smoke proof initially aborted because the olean-only harness had not
loaded `HexArith.Int.exactDiv`'s native wrapper. Building
`lake --no-cache build +HexArith.ExactDiv:dynlib` and loading that dynlib fixes it without a source
change. Preserve upstream `precompileModules := true` for the library owning that module, or
load the dynlib explicitly in this harness. The candidate computation can be native; the final
`hexKernelSmoke` axiom list contains only the allowed three. This is a functional smoke test,
not a 245×245 timing result.

Licence/attribution: Apache-2.0; retain Lean FRO, LLC / Kim Morrison headers and root LICENSE.
Nauty and other monorepo native components are outside this closure. Expected integration:
roughly 1–2 engineering days for namespace/meta-quotation relocation, build configuration,
and review; no mathematical API repair was needed.

Evidence: [axioms](logs/axioms-hex-dev.log), [native wrapper build](logs/Hex-native-build.log),
[initial smoke failure](logs/Hex-kernel-smoke-before-native-build.log),
[successful kernel smoke](logs/Hex-kernel-smoke.log), [55-module alternative](closures/hex-kernel.txt).

Current build summary: 0 errors; 60 passed, 0 failed, 0 blocked; 49.6 s.
Newer-pin build summary: 0 errors; 60 passed, 0 failed, 0 blocked; 65.8 s.

## QICLean

Commit: `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac` ([source](https://github.com/LionSR/QICLean/tree/603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac)).
Lean: `leanprover/lean4:v4.36.0-rc1`. Mathlib: `625d8914199bc567cca9b91f90e8e5afafa5ae51`.

Exact copy closure: [module list](closures/QICLean.txt), [import edges / source evidence](closures/QICLean.json).
Full source closure: **3,278 modules / 1,029,996 lines**; [module list](closures/QICLean-full.txt), [import edges / source evidence](closures/QICLean-full.json).

Use the six requested analysis/coherent-measure roots. Their complete closure is
**62 modules / 16,695 lines**; the projection/Knabe/detectability/gap-only alternative is
9 modules / 2,854 lines. No Gametheory or checkdecls source is imported by these selected modules,
although the upstream package manifest declares those package dependencies.

First current-pin pass: one error, 53 modules passed, one failed, eight blocked, 49.0 s.
`QICLean.Algebra.MatrixUnitaryBetween` references the newer
`Matrix.mulVec_surjective_iff_rank_eq_card`. Expanding the proof through
`LinearMap.range_eq_top`, `Submodule.eq_top_of_finrank_eq`, and `Module.finrank_pi` gives
**62/62 modules and zero errors** (74.3 s on the repaired pass).
[The exact patch](QICLean-current.patch) preserves the statement and assumptions.
At the original 4.36/625d8914199b pin, all 62 modules build unchanged.

The selected copy scan has no forbidden-feature or unsafe/meta/implementation-attachment hits.
The key theorem axiom checks, including both coherent-resolution/integral theorems after repair,
pass. This supplies cyclic Knabe algebra and Haar coherent frames; 2D box counting and the
manuscript's SU(2)/sphere normalization bridges remain separate mathematics.

Licence/attribution: Apache-2.0; retain Sirui Lu, QICLean contributors, and TNLean contributor
headers. The Wolf-note PDFs/TeX and their Notes/NOTICE.md are outside the Lean closure.
API repair is very small and already demonstrated; allow 1–2 days for namespace integration.
Evidence: [first pass](port-QICLean-first.json), [repaired pass](port-QICLean.json),
[axioms](logs/axioms-QICLean.log), [9-module alternative](closures/QICLean-projections.txt).

Current build summary: 0 errors; 62 passed, 0 failed, 0 blocked; 74.3 s.
Newer-pin build summary: 0 errors; 62 passed, 0 failed, 0 blocked; 87.1 s.

## Physlib sl₂

Commit: `892e8fcba8af5ec691ca7a8ad82ee5dbe3180b17` ([source](https://github.com/leanprover-community/physlib/tree/892e8fcba8af5ec691ca7a8ad82ee5dbe3180b17)).
Lean: `leanprover/lean4:v4.35.0`. Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Exact copy closure: [module list](closures/physlib.txt), [import edges / source evidence](closures/physlib.json).
Full source closure: **2,516 modules / 747,365 lines**; [module list](closures/physlib-full.txt), [import edges / source evidence](closures/physlib-full.json).

Use `PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.{Construction,
TensorHighestWeight,TensorDecomposition,TensorIntertwiner}`. The exact closure is
**12 modules / 3,521 lines**. Adding normalized
`PhyslibAlpha.QuantumMechanics.AngularMomentum.ClebschGordanCoefficients` gives
15 modules / 4,542 lines. Both versions compile unchanged on the current pin (21.7 s and
30.3 s respectively); the 12-module selection also builds unchanged on 4.36.
The decomposition closure itself includes the dimension-based `ClebschGordan` prerequisite;
its presence does not replace the stronger intertwining conclusions in TensorDecomposition.

The selected copy scans have no forbidden or unsafe/meta/implementation-attachment hits.
Intertwining and normalized coefficient theorem axiom checks pass. Compact SU(2), Hermitian
orthogonality and the degree-four polynomial correspondence still need manuscript bridges.

Licence/attribution: Apache-2.0; preserve Tom Ole Diem / Tom Diem, Daniel Leonforte and Gregory
J. Loges notices in the retained files. Expected source integration is small, around half a day
plus review; mathematical bridges are excluded from that estimate.
Evidence: [axioms](logs/axioms-physlib.log), [normalized closure](closures/physlib-coefficients.txt),
[normalized axioms](logs/axioms-physlib-coefficients.log).

Current build summary: 0 errors; 12 passed, 0 failed, 0 blocked; 21.7 s.
Newer-pin build summary: 0 errors; 12 passed, 0 failed, 0 blocked; 20.5 s.

## Finite-chain modules from fluctuations-palomar

Commit: `52e8a21a2497f28811a3154dea6d37e819ccc088` ([source](https://github.com/pmaronow/fluctuations-palomar/tree/52e8a21a2497f28811a3154dea6d37e819ccc088)).
Lean: `leanprover/lean4:v4.35.0-rc2`. Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

Exact copy closure: [module list](closures/fluctuations-palomar.txt), [import edges / source evidence](closures/fluctuations-palomar.json).
Full source closure: **3,454 modules / 1,092,296 lines**; [module list](closures/fluctuations-palomar-full.txt), [import edges / source evidence](closures/fluctuations-palomar-full.json).

The generic chain copy set is exactly:

```text
SKConstants.EntropyCoverage
SKConstants.EntropyDissipation
SKConstants.FiniteChainCheeger
SKConstants.FiniteChainDirichlet
SKConstants.FiniteChainMixing
SKConstants.FiniteChainPruning
SKConstants.FiniteChainSemigroup
SKConstants.FiniteGibbs
```

This is **8 modules / 2,440 lines**, rather than the paper's full proof closure. It builds
unchanged on the campaign's exact pin in 8.9 s; the newer-pin pass also succeeds.
The adaptation examples add `ContinuousHeatBath`, `HeatBath`, `JointGibbs`: the resulting
11-module / 3,117-line closure also compiles unchanged (13.2 s). No `SKConstants.Upstream`,
`vendor/all-lean`, OpenAI-math, or legacy paper modules enter either selected closure.

The copy scans have no forbidden or unsafe/meta/implementation-attachment hits. Stochasticity,
detailed balance, Dirichlet/Cheeger/mixing/TV and heat-bath axiom checks pass. Keep the generator
normalization explicit; adapting Boolean heat-bath states to 12/20-letter sites is additional work.

Licence/attribution: root Apache-2.0; retain root NOTICE and source notices. The root NOTICE is
preserved in the licence evidence. MIT all-lean and other nested licences become relevant only
if the copy set is later expanded into their modules. Do not copy the original broad Lake
configuration/default Challenge and Solution targets merely to obtain these eight modules.
Expected namespace integration: a few hours to half a day, excluding model adaptation.
Evidence: [axioms](logs/axioms-fluctuations-palomar.log),
[examples closure](closures/fluctuations-examples.txt), [example axioms](logs/axioms-fluctuations-examples.log).

Current build summary: 0 errors; 8 passed, 0 failed, 0 blocked; 8.9 s.
Newer-pin build summary: 0 errors; 8 passed, 0 failed, 0 blocked; 12.4 s.

## TauCeti sphere measures and moments

Commit: `1ff53249699b7c424afd3a2df742800406435ec5` ([source](https://github.com/TauCetiProject/TauCeti/tree/1ff53249699b7c424afd3a2df742800406435ec5)).
Lean: `leanprover/lean4:v4.36.0-rc2`. Mathlib: `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81`.

Exact copy closure: [module list](closures/TauCeti.txt), [import edges / source evidence](closures/TauCeti.json).
Full source closure: **3,726 modules / 1,189,244 lines**; [module list](closures/TauCeti-full.txt), [import edges / source evidence](closures/TauCeti-full.json).

Use roots
`TauCeti.Probability.Distributions.Uniform.Sphere.{Basic,Moments,Dirichlet,Norm}`.
Their complete closure is **180 modules / 52,097 lines**.

Current-pin trial: **98 errors in 28 modules**, 78 passed and 74 blocked (79.7 s).
Newer-pin trial: **64 errors in 19 modules**, 98 passed and 63 blocked (112.1 s).
Breakage includes eNorm/nnNorm lemmas and instances, `PiLp` extension APIs, multilinear-map
parameters, finite-dimensional completeness, quasi-measure-preserving constructor arguments,
and measure/integrability interfaces. These counts cannot price the unelaborated descendants.
The separate Courant–Fischer closure is 5 modules / 1,425 lines and has four current-pin errors
about finite-span dimension APIs, with one blocked module.

The donor copy scan has no forbidden or unsafe/meta/implementation-attachment hits. The sphere
root theorems could not be built at either trial pin, so no successful key sphere axiom report
is claimed. Its own pin is 4.36.0-rc2 with a different master Mathlib commit from the Mathlib
donor; changing only the Lean version is insufficient.

Licence/attribution: Apache-2.0; preserve all file authors, including Tau Ceti contributors,
Kitware, Inc., and named individual contributors where present. Defer bulk vendoring. Budget
several days to more than a week for a full backward source port, with substantial uncertainty;
first consider a smaller sphere-moment development over existing `HaarToSphere` and Gaussian
integration. New finite 4-design identities remain necessary either way.
Evidence: [current diagnostics](port-TauCeti.json), [newer diagnostics](port-TauCeti-436.json),
[min-max closure](closures/TauCeti-minmax.txt), [min-max trial](port-TauCeti-minmax.json).

Current build summary: 98 errors; 78 passed, 28 failed, 74 blocked; 79.7 s.
Newer-pin build summary: 64 errors; 98 passed, 19 failed, 63 blocked; 112.1 s.

## TNLean selected AKLT pieces

Commit: `3d3507f93fdf6fa52db553cacf30b5df4e60eaa7` ([source](https://github.com/LionSR/TNLean/tree/3d3507f93fdf6fa52db553cacf30b5df4e60eaa7)).
Lean: `leanprover/lean4:v4.36.0-rc1`. Mathlib: `625d8914199bc567cca9b91f90e8e5afafa5ae51`.

Exact copy closure: [module list](closures/TNLean-selected.txt), [import edges / source evidence](closures/TNLean-selected.json).
Full source closure: **3,634 modules / 1,147,178 lines**; [module list](closures/TNLean-selected-full.txt), [import edges / source evidence](closures/TNLean-selected-full.json).

The selection consists of
`TNLean.MPS.Examples.{AKLT,AKLTParentHamiltonian,AKLTPolynomialHamiltonian,AKLTSpinSectors,
SpinOne,SpinOperator}` and `TNLean.Algebra.SingletMatrix`, with their complete closure:
**91 modules / 22,134 lines** (64 TNLean, 27 QICLean). Both pins build this selection unchanged:
zero errors in 129.4 s at the current pin and 115.5 s at 4.36.

Only five of these imported QICLean modules overlap the separate 62-module QICLean selection;
enabling this full TN selection adds 86 files to that union, including 22 more QICLean modules.
Keep those 22 under the QICLean vendor namespace at the same QICLean commit.
The `AKLT`/singlet-only option is 35 modules / 8,389 lines and builds unchanged on the current pin.
By comparison, expanding the literal `AKLT*` glob gives **473 modules / 121,098 lines**,
including three Gametheory/Brouwer modules and a near-whole-Mathlib import. That larger option
was source-audited, not trial-compiled as a whole; its exact list is linked below.

The selected 91-module copy scan has no forbidden or unsafe/implementation-attachment hits.
Its QICLean `Kraus.Tactic.Attr` prerequisite registers the `kraus_transfer` simp attribute;
this registration is ordinary proof automation, with no extra logical assumption.
AKLT normality, the parent-Hamiltonian ground-state result, the spin-two projection identity
and the physical Hamiltonian ground-state result pass axiom checks. These are spin-1 chain
examples; the square-lattice spin-2 construction remains a new development.

Licence/attribution: Apache-2.0 for the selected TN/QIC source, preserving all contributor
headers. Papers/NOTICE.md concerns papers outside this code selection. The 473-module option
also imports MIT-licensed `LionSR/Brouwer` at `439aaeb9caa7a7f943f9e72afc77751cbc5b0098`;
retain its Math_XMUM copyright and MIT licence if that option is ever taken.
Use TNLean as a reference first and copy selected lemmas when a manuscript bridge needs them.
Allow 1–2 days for a whole 91-module namespace integration, excluding new physics.
Evidence: [axioms](logs/axioms-TNLean-selected.log), [small closure](closures/TNLean-small.txt),
[all AKLT modules](closures/TNLean.txt), [all AKLT full import closure](closures/TNLean-full.txt).

Current build summary: 0 errors; 91 passed, 0 failed, 0 blocked; 129.4 s.
Newer-pin build summary: 0 errors; 91 passed, 0 failed, 0 blocked; 115.5 s.

## Balaban Timár / boundary connectivity

Commit: `493e9eb97292ebf6070c1c217a09bcf1adc23857` ([source](https://github.com/scottnarmstrong/balaban-lean/tree/493e9eb97292ebf6070c1c217a09bcf1adc23857)).
Lean: `leanprover/lean4:v4.35.0-rc2`. Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

Exact copy closure: [module list](closures/balaban-lean.txt), [import edges / source evidence](closures/balaban-lean.json).
Full source closure: **1,222 modules / 313,744 lines**; [module list](closures/balaban-lean-full.txt), [import edges / source evidence](closures/balaban-lean-full.json).

The complete copy set is exactly:

```text
Balaban.LargeField.Geometry.BoundaryConnectivity
Balaban.LargeField.Geometry.Escape
Balaban.LargeField.Geometry.Lattice
Balaban.LargeField.Geometry.Plaquette
Balaban.LargeField.Geometry.Timar
```

**5 modules / 942 lines**, exact campaign pin; unchanged builds at both tested pins, current
5.5 s. No forbidden or unsafe/meta/implementation-attachment hits in the copy set. The key
outer/exterior boundary star-connectivity results pass axiom checks.
The manuscript's stronger NN-connectivity conclusion under its different *-connectivity and
no-diagonal-block hypotheses still needs a new bridge. Frozen roots/providers containing holes
elsewhere in Balaban are outside this closure.

Licence/attribution: Apache-2.0; retain root licence, existing source comments/notices and
upstream Scott Armstrong / balaban-lean provenance. Source integration should take a few hours;
the mathematical bridge has no estimate here. [Axioms](logs/axioms-balaban-lean.log).

Current build summary: 0 errors; 5 passed, 0 failed, 0 blocked; 5.5 s.
Newer-pin build summary: 0 errors; 5 passed, 0 failed, 0 blocked; 5.6 s.

## Potts finite cut and parity lemmas

Commit: `435fb57856860eda7a65c8fec9e5fb29eff2b46b` ([source](https://github.com/zijie123123/PottsDiscontinuity-lean/tree/435fb57856860eda7a65c8fec9e5fb29eff2b46b)).
Lean: `leanprover/lean4:v4.35.0-rc3`. Mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e`.

Exact copy closure: [module list](closures/PottsDiscontinuity-lean.txt), [import edges / source evidence](closures/PottsDiscontinuity-lean.json).
Full source closure: **8,976 modules / 2,402,946 lines**; [module list](closures/PottsDiscontinuity-lean-full.txt), [import edges / source evidence](closures/PottsDiscontinuity-lean-full.json).

Select `PottsDiscontinuity.Duality.{RectangleLabelCut,RectangleDualCrossing,
LatticeCellBoundaryParity}`. Their exact **33-module / 5,841-line** closure includes finite
FK model/probability/rectangle prerequisites. Some prerequisites import the Mathlib umbrella,
so the full source import closure is much larger than the copy footprint.

Both pins compile the selection unchanged; current pass 60.8 s. The copy scan has no forbidden
or unsafe/meta/implementation-attachment hits. Boolean cut parity, lattice-cell even degree
and dual crossing key theorems pass axiom checks. Translation of the manuscript's domain and
adjacency conventions remains necessary.

Licence/attribution: Apache-2.0; retain root licence and the source's adaptation notice about
the author's earlier unpublished planar FK formalization. The MIT
`vendor/fixed-point-theorems` library is **outside** this 33-module closure. No Jordan/fixed-point
library is needed by this selection. Expected integration: half a day to a day, excluding the
Appendix B bridge. [Axioms](logs/axioms-PottsDiscontinuity-lean.log).

Current build summary: 0 errors; 33 passed, 0 failed, 0 blocked; 60.8 s.
Newer-pin build summary: 0 errors; 33 passed, 0 failed, 0 blocked; 60.7 s.

## Econlib finite variance / conditioning

Commit: `d7bd9477476cade1c6695c8891746048ceddc52f` ([source](https://github.com/danlyng/Econlib/tree/d7bd9477476cade1c6695c8891746048ceddc52f)).
Lean: `leanprover/lean4:v4.29.0`. Mathlib: `8a178386ffc0f5fef0b77738bb5449d50efeea95`.

Exact copy closure: [module list](closures/Econlib.txt), [import edges / source evidence](closures/Econlib.json).
Full source closure: **1,763 modules / 502,222 lines**; [module list](closures/Econlib-full.txt), [import edges / source evidence](closures/Econlib-full.json).

The complete copy set is exactly:

```text
Econlib.Attributes
Econlib.Probability.FinDist.Basic
Econlib.Probability.FinDist.ConditionalOn
Econlib.Probability.FinDist.Expect
Econlib.Probability.FinDist.Map
Econlib.Probability.FinDist.Variance
```

**6 modules / 1,158 lines**. Both trial pins report four diagnostics in `FinDist.Basic`:
`split_ifs`/`simp` normalization and two positivity/type mismatches. Only Attributes builds;
four descendants are blocked. Its declared optlib dependency does not enter this copy closure.
The copy scan itself has no forbidden or unsafe/implementation-attachment hits; `Econlib.Attributes`
registers two named simp sets. The full
old Mathlib/Batteries closure's quoted `axiom helper` is explained in the trust assessment.
No successful key variance/conditioning axiom audit is claimed because those modules did not build.

Licence/attribution: Apache-2.0; preserve Daniel Lyng headers. Defer until a specific finite
variance identity is required; allow roughly 1–3 days for compatibility and integration because
the blocked descendants remain unchecked. The 118-line llm-audit fibre formula is ready sooner.
Evidence: [current trial](port-Econlib.json), [newer trial](port-Econlib-436.json).

Current build summary: 4 errors; 1 passed, 1 failed, 4 blocked; 2.8 s.
Newer-pin build summary: 4 errors; 1 passed, 1 failed, 4 blocked; 3.0 s.

## llm-audit finite conditioning

Commit: `46b3e3fc61c6b1175a695582631396845b40557c` ([source](https://github.com/pmaronow/llm-audit-lean/tree/46b3e3fc61c6b1175a695582631396845b40557c)).
Lean: `leanprover/lean4:v4.34.1`. Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Exact copy closure: [module list](closures/llm-audit-lean.txt), [import edges / source evidence](closures/llm-audit-lean.json).
Full source closure: **3,592 modules / 1,138,297 lines**; [module list](closures/llm-audit-lean-full.txt), [import edges / source evidence](closures/llm-audit-lean-full.json).

The copy set is the single
`AronowAudit.P015.P015_FiniteConditioning` module, **118 lines**. It imports Mathlib only,
compiles unchanged on both trial pins (current 2.3 s), and its three key finite-fibre/conditional
independence results pass axiom checks. The copy scan has no forbidden or unsafe/meta/
implementation-attachment hits. SAP Challenge modules are outside this closure.

Licence/attribution: Apache-2.0. Retain the header crediting Rémy Degenne and the exact Mathlib
source revision `d13f23b723b8a846827a245b89c10fc7d3f11612`; preserve root NOTICE in the licence
bundle. Other StatLean/Causalean files mentioned in that NOTICE are outside this copy set.
Expected integration: a few hours. [Axioms](logs/axioms-llm-audit-lean.log).

Current build summary: 0 errors; 1 passed, 0 failed, 0 blocked; 2.3 s.
Newer-pin build summary: 0 errors; 1 passed, 0 failed, 0 blocked; 2.0 s.

## LeanCert dyadic core, evaluation and finite sums

Commit: `44b323a0d6af00211d5013f6e021432db032087c` ([source](https://github.com/alerad/leancert/tree/44b323a0d6af00211d5013f6e021432db032087c)).
Lean: `leanprover/lean4:v4.35.0`. Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Exact copy closure: [module list](closures/leancert.txt), [import edges / source evidence](closures/leancert.json).
Full source closure: **2,899 modules / 922,801 lines**; [module list](closures/leancert-full.txt), [import edges / source evidence](closures/leancert-full.json).

Select `LeanCert.Core.{Dyadic,IntervalDyadic}`, `LeanCert.Engine.IntervalEvalDyadic`,
`LeanCert.Validity.DyadicBounds`, and `LeanCert.Engine.FinSumDyadic`. The exact closure is
**23 modules / 12,796 lines**. Restricting roots to the two core files still imports
11 modules / 7,719 lines, including rational transcendental prerequisites.

Both tested pins build the 23-module selection unchanged; current 31.1 s. The copy scan has
no forbidden or unsafe/meta/implementation-attachment hits. Documentation mentions
`native_decide`, including finite-sum examples, but the selected implementation theorems use
checker hypotheses and kernel proofs. Rounding, add/mul, upper-bound and checked finite-sum
soundness theorem axiom checks pass.

No LeanCert tactic/trust-mode implementation is in this closure. If a tactic frontend is added
later, configure strict `trust := kernel` / `leancert.trust = "kernel"` and retain its soundness
closure; the upstream native default and auto fallback are unsuitable for these final proofs.
The exact scalar/vector certificate representation and its large H3 replay time remain to be measured.

Licence/attribution: Apache-2.0; preserve LeanCert Contributors headers. The separately licensed
HadamardSupport subtree is outside this selection. Allow about a day for namespacing and
integration, excluding certificate construction and performance work.
Evidence: [axioms](logs/axioms-leancert.log), [core-only closure](closures/leancert-core.txt).

Current build summary: 0 errors; 23 passed, 0 failed, 0 blocked; 31.1 s.
Newer-pin build summary: 0 errors; 23 passed, 0 failed, 0 blocked; 35.3 s.

## RealRooted Perron–Frobenius

Commit: `d667074269bb822fa18ca9142a14fdd90734dd57` ([source](https://github.com/PerAlexandersson/RealRooted/tree/d667074269bb822fa18ca9142a14fdd90734dd57)).
Lean: `leanprover/lean4:v4.35.0`. Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Exact copy closure: [module list](closures/RealRooted.txt), [import edges / source evidence](closures/RealRooted.json).
Full source closure: **3,217 modules / 984,140 lines**; [module list](closures/RealRooted-full.txt), [import edges / source evidence](closures/RealRooted-full.json).

Select `RealRooted.Mathlib.LinearAlgebra.Matrix.PerronFrobenius.{CollatzWielandt,
Nonneg,Irreducible}`. The complete closure is **12 modules / 3,441 lines**; no LeanLGV code enters it.

First current-pin pass: one missing-import error for `Mathlib.Algebra.Order.Star.Int`, four
modules passed and seven blocked. Removing that unused public import in a scratch-only follow-up
exposes two diagnostics in `CStarClasses`: missing `mul_star_self_ne_zero.mpr` and its downstream
complex-field algebra goal; nine modules then pass and two remain blocked.
The [follow-up patch](RealRooted-current-attempt.patch) is an unfinished port, not a recommended
proof replacement. At 4.36/625d8914199b, all 12 modules compile unchanged (16.7 s), and the key
nonnegative PF/dominance/monotonicity/Collatz–Wielandt theorem axiom checks pass.

The copy scan has no forbidden or unsafe/meta/implementation-attachment hits. Its original
package pin is 4.35.0/56a005855ea1; 4.36 is source compatible for the selected files, rather than
an exact match of the unchanged upstream package manifest.

Licence/attribution: Apache-2.0; preserve Per Alexandersson and Matteo Cipollina headers and
source provenance. Defer unless spectral-radius/PF theory is actually needed. H2 and the tail
can use positive-vector power domination directly. The min-ratio Collatz–Wielandt lower bound
requires an additional argument to yield the manuscript's desired max-ratio upper bound.
Estimated compatibility/integration: half a day to two days, with the blocked current-pin
descendants still uncertain. Evidence: [first pass](port-RealRooted-first.json),
[follow-up](port-RealRooted.json), [4.36 axioms](logs/axioms-RealRooted-436.log).

Current build summary: 2 errors; 9 passed, 1 failed, 2 blocked; 13.4 s.
Newer-pin build summary: 0 errors; 12 passed, 0 failed, 0 blocked; 16.7 s.

## Pin choice and measured costs

**Recommendation: retain `leanprover/lean4:v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.** The existing Mathlib cache is already present
(about 6.6 GiB), and the high-value source closures above need only the retained QICLean rank
proof repair. Existing Challenge work therefore stays on its current definitions and theorem
surface. Namespace isolation and manuscript bridges are required independently of the pin.

The concrete alternative tested was **Lean `4.36.0-rc1` + Mathlib
`625d8914199bc567cca9b91f90e8e5afafa5ae51`**, exactly QICLean/TNLean's common pin:

- QICLean and TNLean become exact-pin package candidates. Their selected closures both build
  unchanged. A full package installation still resolves their declared Gametheory/checkdecls/
  cslib dependencies, even where those modules are absent from the selected proof closure.
- Hex, Physlib, finite chains, Balaban, Potts, finite conditioning and LeanCert are source
  compatible for the selections tested, but their original package manifests use different
  pins. They need common-pin reconciliation or the source vendoring described here.
- RealRooted's selected source closure becomes zero-change source compatible. TauCeti still
  has 64 diagnostics with 63 modules blocked; Econlib still has four. Thus a bump does not make
  the sphere or variance donor an immediate import.
- All 20 requested Mathlib roots are available, including the newer Echelon certificate module.
  The existing Hex route limits the practical benefit of that addition for H1.
- The toolchain was already installed, so its download cost was zero. A fresh Mathlib cache-tool
  build plus full **9,047-module** cache download/decompression took **28.0 s**.
  The resulting Mathlib `.lake/build` occupied about **6.7 GiB**, with about **453 MiB** of
  compressed cache files and roughly 170 MiB of source/dependency copies. This was a successful
  full cache hit; a source rebuild of all Mathlib was neither needed nor timed. With no cache,
  that build cost remains unmeasured. See [command, timing and disk samples](cache-436.json)
  and [complete cache log](logs/cache-436.log).
- `leanexport`, `con-ron` and `nanoda_bin` are executable in **both** installed toolchain bin
  directories. The 4.36 exporter identifies format/exporter 3.1.0 and the matching Lean githash.
  A sandboxed `lake comparator` smoke test with the three-axiom allow-list and explicit Nanoda
  plus `con-ron --verified --jobs=1` **passed all three checkers**, including Lean's kernel,
  in 10.7 s. [Comparator log](logs/comparator-436.log),
  [smoke configuration](../../scratch/VENDOR-PLAN/comparator-436/comparator.json),
  [installed-tool evidence](logs/environment.log).

The extra cache footprint and time are modest on this host. The reason to retain the current
pin is the very small demonstrated compatibility gap for the immediate imports. If the project
later commits to importing TauCeti's full sphere stack, reconsider a coordinated newer Mathlib
pin then. Lean 4.36.0-rc2 was not installed here; neither the latest Mathlib donor nor TauCeti's
distinct rc2 snapshot was built at its own original toolchain during this audit.

## Vendoring list and namespace plan

Use the source commit in each donor section, not an upstream branch. The exact source module
sets and proposed namespaces are also recorded in [vendoring-plan.json](vendoring-plan.json).

| Decision | Exact closure | Namespace / use |
|---|---|---|
| Import dependency | 19 available Mathlib roots above | Keep `Mathlib.*`; no vendor copy |
| Vendor | Hex 60-module set, preserving native-wrapper build configuration | `AKLT.Vendor.Hex` |
| Vendor | QICLean 62-module set + retained rank proof patch; start with its 9-module projection subset when useful | `AKLT.Vendor.QICLean` |
| Vendor | Physlib 12-module sl₂ set; 15-module normalized-coefficient option as needed | `AKLT.Vendor.Physlib` |
| Vendor | Finite-chain 8-module set; heat-bath additions only as examples when needed | `AKLT.Vendor.FiniteChain` |
| Vendor | Single 118-line finite-conditioning module | `AKLT.Vendor.FiniteConditioning` |
| Vendor | LeanCert 23-module set; core-only 11-module option if no evaluator/finite-sum interface is used | `AKLT.Vendor.LeanCert` |
| Copy when a bridge uses it | Balaban 5-module boundary set | `AKLT.Vendor.Balaban` |
| Copy when a bridge uses it | Potts 33-module cut set | `AKLT.Vendor.Potts` |
| Reference first | TNLean 91-module selected AKLT closure; prefer 35-module small option for examples | `AKLT.Vendor.TNLean`; its QIC imports share the QIC vendor namespace |
| Defer | TauCeti 180-module sphere closure | `AKLT.Vendor.TauCeti` if its port is chosen |
| Defer | Econlib 6-module set | `AKLT.Vendor.Econlib` if variance identities need it |
| Defer | RealRooted 12-module set | `AKLT.Vendor.RealRooted` if PF theory is needed |

The six immediate non-Mathlib vendor selections total **166 distinct modules / 51,503 source
lines** before namespace changes. TNLean's selected closure would add another 86 files to the
QICLean union. This recommendation excludes the 473-module AKLT glob and every donor's
Challenge/SAP or unrelated admitted root.

Use a source-aware relocation: rewrite local import paths, owned namespaces, qualified theorem
references and quoted names together. Keep references to Mathlib/Lean types rooted correctly;
several donors extend `Matrix`, `ContinuousLinearMap` or `TensorPower` rather than using a
single upstream namespace. For TNLean, map all QIC-owned modules to `AKLT.Vendor.QICLean`
and deduplicate them at the same QIC commit. A blanket text prefix without updating quotations
and cross-donor names is insufficient. After relocation, rebuild each selected closure and
audit its exported theorem axioms and final Comparator targets again.

The engineering estimates above concern compatibility, relocation and notices. They do not
estimate the remaining SU(2)/polynomial edge lemma, 2D Knabe counts, MO/MOS bridge, stronger
Appendix B connectivity, spherical 4-design specialization, trail recursion, or H1–H3 certificate
construction and scale. No largest H1 matrix or H3 recurrence benchmark was run in this task.

## Licence and NOTICE packaging

All thirteen selected donor repositories have root Apache-2.0 licences. Copies of their root
licences and existing root NOTICE files are preserved under [licenses/](licenses/). The selected
TNLean 91-module and Potts 33-module sets avoid the MIT dependency subtrees discussed above;
the larger TNLean option needs Brouwer's MIT notice as well. The materialized Mathlib package
sources are Apache-2.0 except the manifest dependency `Cli` (MIT, copyright 2021 mhuisi);
no `Cli` module enters any inspected Lean source import closure. See the
[dependency licence inventory](dependency-license-classification.json). Installed/distributed
dependencies should retain their own licence files.

For distributed copies, include the licence, retain applicable copyright/author/attribution
notices, mark modified files, and retain applicable upstream NOTICE attributions. These are the
redistribution requirements in [Apache-2.0 §4](https://www.apache.org/licenses/LICENSE-2.0).
Keep each source header. Add a short modification notice with original repository, full commit,
original path, namespace/import changes and proof repair where applicable. Record original
and modified hashes in a vendor manifest. Namespace changes also count as modifications.

Suggested packaging: `LICENSES/<Donor>/LICENSE`, `LICENSES/<Donor>/NOTICE` where supplied,
and a concise aggregate `NOTICE` or `THIRD_PARTY_NOTICES.md` pointing to them. Retain the
fluctuations-palomar root NOTICE and llm-audit root NOTICE verbatim for the initial copy; the
latter's source header separately preserves Rémy Degenne's Mathlib adaptation credit.
Do not import paper PDFs/notes merely to obtain Lean code. Preserve additional nested licences
if a future expansion crosses the boundaries documented for F, TNLean or Potts.

## Resource use, deviations and retained artifacts

No sub-agents were launched. Compilation was scheduled with at most eight simultaneous Lean
compiler children (current trials at up to three per closure, newer-pin trials at two; the
Mathlib cache bootstrap wrapper caps its Lean compiler children at three). No toolchain or
user cache was installed outside the permitted roots. Mathlib cache files were redirected to
scratch. No campaign or other campaign file was written.

The disk guard uses a conservative **150 GiB** free-space floor (stricter than 150 decimal GB)
and a **40 decimal GB** total-task ceiling. Observed resource records and cleanup measurements
are in [resources.json](resources.json). All checks stayed within those limits. The particularly
large Hex checkout includes about 4.1 GiB of committed report data plus a 3.6 GiB Git store;
it is retained unchanged as part of the read-only donor snapshot.

An initial Mathlib cache attempt, and one partial TauCeti current-pin trial, were stopped when
the monitor's `du` raced temporary download-file renames. This was a monitoring error rather
than a disk-limit abort. The monitor was corrected to use valid `du` totals despite disappearing
temporary files. The cache/build outputs from that incomplete cache attempt were removed for
the complete cold rerun; TauCeti was also rerun to a complete pass over all 180 scheduled
modules. The reported timings/error counts use those completed runs. Earlier logs are retained.

Trial build outputs, native libraries, compiled cache artifacts and compressed Mathlib cache
downloads have been deleted after validation. Original donor sources, scratch Lake project
sources/configuration/package symlinks, scripts, patches, module lists, licence evidence and
all logs remain. [Clone inventory](clone-inventory.json) confirms clean donor source worktrees;
[campaign metadata hashes](logs/environment.log) and [final hashes](logs/final-campaign-hashes.log)
record the unchanged campaign toolchain/Lake pin files.

Final measured footprint: **11.20 GB** retained,
    versus a maximum observed **19.70 GB** during the task.
    Minimum observed free disk was **189.87 GB**
    (176.8 GiB). Cleanup removed approximately
    8.49 GB of generated artifacts.
