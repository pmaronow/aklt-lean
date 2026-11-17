# Certificate regeneration interface

This handoff is the complete-formalization hand-written port from main
`8f59d336acf2fc13428893faf26097890f4f288b`, extending the earlier two-input release.
Regenerate the certificates **against this release's module-system sources and
fresh objects**. Do not copy or import any legacy olean. Lean is 4.35.0-rc2;
Mathlib is pinned to `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
First-party identifiers now use American English. Eight analytic source files
were renamed consistently with their imports; no direct H1/H3 kernel import
module name changed. Declaration inventories below contain the current names. In
particular, several H3 files live under `CertData/H3/Kernel/` while their original
namespace remains `AKLT.Cert.H3`; use the existing names, not a namespace inferred
from the relocated directory.

The source-only target is `Handwritten`. The optional certificate libraries are
`CertDataH1` and `CertDataH3`, and the complete default targets are `Solution` and
`Audit`. A certificate library name is not a module name. The release target is
unconditional `AKLTPalomar.aklt_gap`, proved through `main_iff` from
`CertData.Close.main`; the ordinary library retains `AKLT.Final.main_of_inputs`.

## H1

The 7,964 generated owner modules retain their paths under
`CertData/H1/Generated/Batch/` and `Bridge/`. The exact inventory is the H1 list in
`verification/generated-modules.json`. Generated modules directly import:

| Legacy module | New module |
| --- | --- |
| `AKLT.Cert.H1.Literals` | unchanged |
| `AKLT.Cert.H1.Production.Assembly` | unchanged |
| `AKLT.Cert.H1.Production.Basic` | unchanged |
| `AKLT.Cert.H1.Production.Coverage` | unchanged |
| `AKLT.Cert.H1.Production.Input` | unchanged |
| `AKLT.Cert.H1.Production.Semantics` | unchanged |
| `AKLT.Defs.OperatorContracts` | unchanged |
| `AKLT.Gen.Gram.Basic` | unchanged |

`verification/regen-interface/H1-imports.tsv` records the same map with paths.
`H1-declarations.tsv` lists the hand-written declarations explicitly referenced
by generated sources, with their owning module, kind, exposure, and a source
example. The accompanying resolution record describes conservative unqualified
name matches and includes inherited constructors and projections. It is an API
inventory, not a substitute for elaborating every regenerated module. Lean
supplies standard-library and Mathlib implicit instances; those dependencies
remain pinned. `H1-exposed.tsv` lists the full exposed hand-written kernel surface,
including dependencies, so literal consumers and arithmetic can reduce in later
modules. `H1-complete-surface.tsv` also includes implicit constructors, projections,
and instances. The syntax `h1_row%` is registered by `AKLT.Cert.H1.intRow` and
`AKLT.Cert.H1.elabIntRow`; the private helper `rowExpr` stays private. Retain the production logical Data/Check namespaces and owner map.

Every generated H1 file begins with this pattern, using its actual imports:

```lean
module

public import AKLT.Cert.H1.Production.Basic
public import AKLT.Cert.H1.Literals
-- Publicly import each generated dependency as well.

@[expose] public section
set_option backward.proofsInPublic true
```

Data definitions, lists, packed integers, structures, and selector functions must
be public and exposed; otherwise a later `decide +kernel` cannot necessarily
reduce them. Certificate theorems must be public for the next assembly layer.
Keep existing explicit private helpers private, but expose any computational
helper needed through a public definition. The compatibility option
`backward.privateInPublic` may be retained when a legacy template needs it; it
is a visibility migration option, not a kernel bypass. Existing finite-check
heartbeat and recursion settings may be retained in generated certificate files.
Every generated source still needs at most 10,000 physical lines.

The compiling sample is `RegenSamples.H1`; `RegenSamples.H1Consumer` imports it
normally, consumes its accepted Boolean check with the actual hand-written
`AKLT.Cert.H1.lowerTriangularCheck_sound`, and performs another kernel reduction
through the exposed literal and signed packing. These are tiny interface tests,
not production matrix or coverage certificates.

The next hand-written closing module is `CertData.H1.Close.Main`. Its one direct
generated import is
`CertData.H1.Generated.Bridge.Targetassembly0000`, whose `targets` theorem must
retain its original type and namespace
`CertData.H1.Generated.Check.Targets.targets`. The complete H1 list records that
module's transitive generated dependencies. `CertData.H1.Close.Audit` depends
transitively on the same family.

## H3

The 5,032 generated modules retain the existing graph/check, B1, B2, C1, C2, C3,
and generated bridge paths under `CertData/H3/`. The H3 list in
`verification/generated-modules.json` is exact. Generated modules directly import:

| Legacy module | New module |
| --- | --- |
| `AKLT.Defs.Automaton10Data` | unchanged |
| `CertData.H3.Bridge.GraphLayout` | unchanged |
| `CertData.H3.Bridge.Interface` | unchanged |
| `CertData.H3.Bridge.Production` | unchanged |
| `CertData.H3.Kernel.Common` | unchanged |
| `CertData.H3.Kernel.Literal` | unchanged |
| `CertData.H3.Kernel.Production.Batching` | unchanged |
| `CertData.H3.Kernel.Production.Model` | unchanged |
| `CertData.H3.Kernel.Production.Replay` | unchanged |

`H3-imports.tsv`, `H3-declarations.tsv`, and `H3-exposed.tsv` under
`verification/regen-interface/` give paths and the full declaration inventories.
The syntax `h3_hex%` is registered by `AKLT.Cert.H3.h3Hex` and
`AKLT.Cert.H3.elabH3Hex`, using `AKLT.Cert.H3.decodeHexBalanced` during elaboration.
`H3-complete-surface.tsv` also includes implicit constructors, projections, and
instances. The 2,340 compacted legacy plane/endpoint literal sources were absent from the
retained worktree; their names come from actual imports, and their simple header
and literal consumer come from the retained `production.py` template. These must
be regenerated from the pinned numeric archive. This is not permission to reuse
the old literal objects or omit these modules from the final source checks.

The generated H3 header pattern is:

```lean
module

public import CertData.H3.Kernel.Production.Model
public import CertData.H3.Kernel.Literal
-- Publicly import the other hand-written/generated dependencies actually used.

@[expose] public section
set_option backward.proofsInPublic true
```

Keep `h3_hex%` elaboration and exact Nat literals. Its implementation is now
explicitly meta; it returns an ordinary numeral term and does not prove a
certificate. The hand-written packed arithmetic, graph/plane lookup, row
checkers, raw replay, prefix replay, and batch consumers have exposed bodies.
Generated graph blocks, `PlaneTree` catalogs, tables, caps, endpoint selectors,
and intermediate result definitions also need public/exposed bodies. Public
certificate theorems feed the unchanged graph and case soundness assemblies.
No arithmetic, check predicate, numeric value, or mathematical assertion changes;
identifier spelling is updated consistently in definitions and statements.

`RegenSamples.H3` elaborates a tiny hexadecimal literal, proves a packed-row
Boolean check by `decide +kernel`, and reduces `Walk.step` through the production
model. `RegenSamples.H3Consumer` imports it normally, applies the actual
`AKLT.Cert.H3.packedRowCheck_sound`, and reduces the imported literal again.
These modules compile against the ported kernels and prove a component bound.

The next hand-written closing module is `CertData.H3.Close.Main`. Its one direct
generated import is `CertData.H3.Bridge.All`. It references these generated objects:
`CertData.H3.Graph.packed`, `CertData.H3.Check.SuppliedTables.checked`,
`CertData.H3.Check.BlockLookup.checked`, `CertData.H3.GraphAssembly.raw_receipt`,
`CertData.H3.GraphAssembly.representative_receipt`,
`CertData.H3.GraphAssembly.field_receipt`, `CertData.H3.Check.EdgeCounts.checked`,
and `CertData.H3.Bridge.All.stationary_from_leaves`. Use the current names and types shown here.
The H3 manifest lists their transitive generated dependencies.

## Exposed computational bodies

The body inventory was read from the actual compiled Lean environment, not
inferred only from source attributes. H1 has 1,153 available bodies in its
hand-written dependency surface; H3 has 1,083. The smaller
`H1-reduction-bodies.tsv` and `H3-reduction-bodies.tsv` lists identify 410 and 392
kernel arithmetic/checker entries, respectively, including generated matchers
and projections. The reference candidate lists have 100 H1 and 69 H3 names;
conservative suffix matches can include a short-name ambiguity. The complete
named surfaces, with 1,589 H1 and 1,511 H3 names, cover that ambiguity and implicit
elaborated names. Standard-library and Mathlib dependencies remain pinned.

Representative H1 entries are `AKLT.Cert.H1.Gaussian.mul`, `Table.get`,
`packedThresholdRow`, and the production `sparsePack`, `packedRowCheck`,
`RowsAccepted`, `constructedSectorRows`, `Block.Accepted`, and `Case.Accepted`.
Representative H3 entries are `AKLT.Cert.H3.PlaneTree.get`, `packedRowCheck`,
and production `Graph.quotient`, `Tables.data`, `planeBatch`, `rawBatch`,
`prefixBatch`, and `sumResults`. The TSV files use their full declaration names.
Exposure makes their unchanged bodies available to downstream kernel reductions;
it does not replace the soundness theorems or certify numeric data.

## Closing and verification

Only the two Close.Main files directly import generated modules. The further
blocked hand-written modules are `CertData.H1.Close.Audit`, `CertData.Close.All`,
`Solution`, and `Audit`. Their exact direct and transitive requirements are in
`verification/generated-modules.json`. No unproved fact is introduced to make
these modules compile early; they remain genuine pending builds.

Build the samples with:

```sh
LEAN_NUM_THREADS=4 lake build RegenSamples.H1Consumer RegenSamples.H3Consumer
lake env lean -DwarningAsError=true AuditHandwritten.lean
```

The original generator scripts are retained under `AKLT/Cert/H1/tools/` and
`AKLT/Cert/H3/`. Their legacy output templates must be adapted to these headers
before use. The regeneration agents own the data-input pins, output archives,
updated manifests, full rebuild, and per-theorem axiom receipts. If splitting a
source to meet the line cap adds modules, update the generated inventory, Lake
globs, and ignore rules together, while preserving downstream declaration names.
The archive installer accepts only inventory paths and refuses overwrites.

Every `.lean` source, including generated sources, must have a module header and
at most 10,000 lines. Only the root Challenge has its single conventional
placeholder. The only permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`; no `native_decide`, `unsafe`, `implemented_by`, `extern`, or new
`opaque` declaration is allowed. Run the official source/header checks, the full
fresh build, strict Audit, unconditional Comparator with Lean and NanoDa, and
con-ron on the final full export after regeneration. Earlier conditional receipts
do not certify that final export. Resources are recorded, not constrained by
Palomar's production acceptance budget.

All prose and first-party identifiers use American English.
`AMERICAN-ENGLISH-IDENTIFIERS.tsv` lists the current identifier spellings. External
Mathlib identifiers and manuscript labels such as `l:colour` stay exact.
The generator input-key audit found no affected external data key: only emitted
Lean names and Lean leaf-name metadata values change.
