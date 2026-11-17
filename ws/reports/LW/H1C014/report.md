STATUS: PROVED FROM DEPS

## Files

- `AKLT/W/H1C014/Main.lean` — the requested theorem, row-check soundness, and row induction.
- `AKLT/W/H1C014/Sparse.lean` — sparse decoding from the proved dense signed-digit theorem.
- `AKLT/W/H1C014/Layout.lean` — distinctness and range of accepted remapped indices.

`Main.lean` imports both helper files. No source files outside `AKLT/W/H1C014/` were edited.
Validation artifacts in this report directory are `Check.lean`, `build.log`, `build.time`,
`check.log`, and `check.time`. The earlier `report.luna.md` is preserved.

## Exported declarations

All four declarations are in namespace `AKLT.W.H1C014`. The following signatures
use `AKLT.Cert.H1` and `AKLT.Cert.H1.Production` names opened as in the source files.

```lean
theorem main : AKLT.Cert.H1.Production.Leaves.acceptedDecode
```

This is the exact requested closed proposition, with no additional hypotheses.

```lean
theorem signedSparseDecode (width lanes : Nat) (hw : 0 < width)
    (positions : List Nat) (values : List Int)
    (hlen : positions.length = values.length) (hnd : positions.Nodup)
    (hrange : ∀ j ∈ positions, j < lanes)
    (hbound : ∀ a ∈ values,
      -((2 : Nat)^(width-1) : Int) ≤ a ∧ a < ((2 : Nat)^(width-1) : Int)) :
    positions.map (fun j =>
      signedDigit (sparsePack width positions values + signedBias width lanes) width j) =
      values
```

```lean
theorem layoutIndexing (c : Case) (hc : c.MetadataAccepted) (b : Bundle)
    (hb : b.LayoutAccepted c) :
    b.mapped.Nodup ∧ ∀ j ∈ b.mapped,
      j < (b.sector.map (fun s => s.coordinates.length)).prod
```

```lean
theorem rows_decode
    (ss : List SectorSite) (out width lanes p q : Nat)
    (columns positions : List Nat) (rows : IntRows)
    (hw : 0 < width) (hnd : columns.Nodup)
    (hpos : ∀ j ∈ columns, j < lanes)
    (hrows : SectorRowsAccepted ss out width p q columns positions rows) :
    positions.map (fun row => constructedSectorRow ss out width lanes p q row columns) = rows
```

## Proved-leaf dependencies

Both dependencies appear in `/home/ubuntu/aklt/state/lw/proved-index.tsv`:

- `AKLT.W.H1C017.main : AKLT.Cert.H1.Production.Leaves.signedPacking`, imported
  through `AKLT.W.H1C017.Main`.
- `AKLT.W.H1C024.main : AKLT.Cert.H1.Production.Leaves.metadataFacts`, imported
  through `AKLT.W.H1C024.Main`; only its positive-width conclusion is needed.

No other blueprint leaves are assumed. There are no residual statements.

## Proof

The parameter check supplies positive base dimensions, dimension four for diluted
pairs, and canonical suffix-product strides. The basis check identifies the source
indices with a filtered range, giving distinct source indices, their range bound,
and the specified parity.

The parity-fold lemmas recover each site's parity bit by division by the suffix
power of two. Together with the sector-network check, this proves that each source
digit belongs to its site's chosen coordinates. The remapping fold then stays
inside the product of coordinate lengths. Equality of two remapped values recovers
every source digit; canonical base strides recover the original index modulo the
base dimension product. The source range bound makes this an actual equality of
indices, proving distinctness of the mapped columns.

For each accepted row, the literal coefficient guard bounds every selected value.
A dense coefficient function places these values at their distinct sparse positions
and zero elsewhere. Its finite sum equals `sparsePack`, so the proved signed-packing
leaf recovers each selected value. The accepted Gaussian equality identifies the
packed real part, and induction over `SectorRowsAccepted` proves equality of all
constructed rows with the literal matrix.

## Axiom audit

The source files audit every public theorem. The separate import/type check
produced this output:

```text
AKLT.W.H1C014.main : AKLT.Cert.H1.Production.Leaves.acceptedDecode
'AKLT.W.H1C014.signedSparseDecode' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C014.layoutIndexing' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C014.rows_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C014.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof mechanisms or increased heartbeat limits are used. The proof
uses symbolic arithmetic and list lemmas; it does not reduce large concrete
certificate objects to establish definitional equalities.

## Build and validation

Commands ran from `/home/ubuntu/aklt/wt/LW_H1C014` with `$HOME/.elan/bin` on `PATH`:

```text
lake build AKLT.W.H1C014.Main
  PASS — final incremental build: 9.76 seconds wall time; Main module: 4.3 seconds.

lake env lean /home/ubuntu/aklt/reports/LW/H1C014/Check.lean
  PASS — 6.33 seconds wall time.
```

The separate check imports `Main` and checks
`example : AKLT.Cert.H1.Production.Leaves.acceptedDecode := AKLT.W.H1C014.main`,
as well as the four axiom audits. Earlier successful helper compilations reported
5.9 seconds for `Sparse` and 6.3 seconds for `Layout`.

## Open issues

No mathematical or Lean proof obligations remain. Validation here used Lean's
kernel; the campaign's con-ron/NanoDa rechecks remain for its harness.

## ORCH-SUMMARY

- Delivered `AKLT.W.H1C014.main` with exactly the requested type.
- Status: PROVED FROM DEPS.
- Proved-leaf dependencies: H1C017 (`signedPacking`) and H1C024 (`metadataFacts`).
- Layout distinctness, layout range, and sparse decoding are proved in the task directory.
- No residual propositions or additional hypotheses remain.
- Every helper source is imported by `Main.lean`.
- All four exported theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- Requested build and separate import/exact-type check passed.
- No scope deviations or mathematical limitations.
- Orchestrator can register H1C014 and run the campaign's independent kernel checks.
