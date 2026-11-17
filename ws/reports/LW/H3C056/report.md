STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Main.lean)
- [Masks.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Masks.lean)
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Geometry.lean)
- [Spatial.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Spatial.lean)
- [Pull.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Pull.lean)
- [RewardTranslation.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/RewardTranslation.lean)
- [Table.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Table.lean)
- [Coefficients.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Coefficients.lean)
- [Row.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Row.lean)
- [Semantic.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Semantic.lean)
- [Audit.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Audit.lean)

All Lean writes are confined to `AKLT/W/H3C056/`. No statement-layer, certificate, package, or other leaf file was edited.

## Exported declarations

The requested declaration is closed and has exactly the required name and type:

```lean
theorem AKLT.W.H3C056.main : AKLT.Cert.H3.RowTermsAgreement
```

The main proof also exports:

```lean
def AKLT.W.H3C056.RowTermsAgreementV2 : Prop
theorem AKLT.W.H3C056.rowTerms_v2 : AKLT.W.H3C056.RowTermsAgreementV2
theorem AKLT.W.H3C056.legacy_transfer
    (hV2 : AKLT.W.H3C056.RowTermsAgreementV2) : AKLT.Cert.H3.RowTermsAgreement
```

`RowTermsAgreementV2` is the exact row-agreement formula with `stationaryCoefficientV2`. It is proved unconditionally by `rowTerms_v2`; there is no residual premise on `main`. Exact statements of all 67 public helper theorems, and the public definition signatures, are in [declarations.md](/home/ubuntu/aklt/reports/LW/H3C056/declarations.md).

## Proof

The proof establishes subtraction and addition of complete-lane masks using the generic Packed lemmas, identifies all spatial masks, and proves that `pull` reads the ambient neighbour with the supplied cap at each missing boundary. It never evaluates a whole stationary certificate.

The response calculation translates to the origin and verifies all sixty admitted direction/dead-neighbour entries by exact rational arithmetic. The individual response pairs are summed before the ceiling is taken. Correctness of the memory quotient supplies the non-revisit arrival, straight/turn classification, and forbidden-reversal facts.

The direction-wise identity in `edge_agreement` uses `stationaryCoefficientV2`. `rowTerms_v2` sums those identities. The retained centre-zero transfer then proves the frozen legacy statement, including its different known-site incoming-centre edge. The checked zero-centre lane makes that difference contribute zero.

The existing cheaper-model attempt in `report.luna.md` supplied the transfer argument and was retained where useful. No sub-agents were used. The generic reward-translation argument was reused from the retained H3 proof in `AKLT/W/H3M020/Main.lean`; the delivered local helper proves it without an additional premise.

## Axioms and exact-type check

[Audit.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Audit.lean) compiles this exact-type check:

```lean
example : AKLT.Cert.H3.RowTermsAgreement := AKLT.W.H3C056.main
```

Its `#check` output is:

```text
AKLT.W.H3C056.main : AKLT.Cert.H3.RowTermsAgreement
```

The main declarations produce:

```text
'AKLT.W.H3C056.rowTerms_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C056.legacy_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C056.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every one of the 67 exported theorems was checked with `#print axioms`. All axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`; full output is in [axioms.log](/home/ubuntu/aklt/reports/LW/H3C056/axioms.log). Static checks found no forbidden proof constructs, debug traces, or trailing whitespace in the eleven delivered Lean files. The finite `decide` calls use `decide +kernel`.

## Builds and timings

- `lake build AKLT.W.H3C056.Main`: successful after the final edits; wall time **44.95 s**, Main module **3.9 s**, peak reported RSS **6,866,156 KB**. [Build log](/home/ubuntu/aklt/reports/LW/H3C056/build.log).
- `lake build AKLT.W.H3C056.Table`: successful; the exact sixty-entry response verification took **84 s**. [Table build log](/home/ubuntu/aklt/reports/LW/H3C056/table-build.log).
- `lake env lean AKLT/W/H3C056/Audit.lean`: successful; wall time **4.75 s**, peak reported RSS **6,858,588 KB**. [Audit output](/home/ubuntu/aklt/reports/LW/H3C056/axioms.log).

The final Main build reused the already compiled response table. Existing libraries were replayed from their built artifacts. There are ordinary unused-argument and exponentiation-threshold warnings; no build errors remain.

## Open issues

None. There are no residual statements, missing blueprint leaves, new assumptions, or changes to the frozen statement. The only practical resource limitation observed is the approximately 6.6 GiB peak RSS recorded above.

## ORCH-SUMMARY

- H3C056 is PROVED.
- Delivered `AKLT/W/H3C056/Main.lean` and ten local helper/audit files.
- Exact closed export: `AKLT.W.H3C056.main : AKLT.Cert.H3.RowTermsAgreement`.
- The V2 packed row identity is fully proved.
- The checked zero-centre lane transfers V2 to the frozen legacy coefficient.
- No residual premises or unavailable dependency leaves remain.
- All 67 public theorem axiom sets were audited and are allowed.
- Requested Main build and independent exact-type audit both pass.
- Final build: 44.95 s; separate response-table verification: 84 s.
- Peak reported RSS is about 6.6 GiB; only routine linter/threshold warnings remain.
- No existing files outside the assigned directory were edited; no sub-agents were used.
- No orchestrator decision or additional proof work is required.
