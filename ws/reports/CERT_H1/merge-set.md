# H1 phase-3 merge instructions

`merge-set.txt` is the exact merge list: 39 hand-written source files.
No generated data, check modules, artifacts or historical phase-1 files are included.
`leaves-open.json` contains exactly the accepted 33 open closed-Prop obligations;
there are no data blocks in that queue. Their definitions are in
`AKLT.Cert.H1.Production.TopLeaves` and `AKLT.Cert.H1.Production.Leaves`.

Build the source entry point with:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake build AKLT.Cert.H1.Production.All
lake build AKLT.Cert.H1.Production.Audit
```

Verification: all 17 reusable Lean modules compiled with strict implicit settings
on a fresh archive of main `6f171dccd76d8641416d2609ed2caa5968f6afdb`, overlaid with only this merge set.
The isolated check uses the supplied prebuilt Mathlib/AKLT dependencies after
verifying every transitive external AKLT source against that main snapshot.
No existing H1 artifact or generated H1 source was visible to that check.
All 36 Prop checks and all nine assembly axiom audits passed; only propext,
Classical.choice and Quot.sound occur. Detailed receipt:
`phase3/merge-verification.json`. Documentation/Python receipt helper changes
after that compilation are separately listed in that receipt.

Generated attachment: `CertData/H1/Generated/`, a separate opt-in Lake library
`CertDataH1`. The added target has root `CertData.H1.Generated` and selects the
`Batch` and `Bridge` owner directories. Preserve main's existing generic
`CertData` target. After attaching/producing the compressed source tree, run:

```sh
python3 AKLT/Cert/H1/tools/production_receipts.py restore-sources
lake build CertDataH1
```

The production runner can use retained oleans and `.lean.gz` directly. The
owner map in the production manifest maps public Data/Check declaration
namespaces to their actual Batch/Bridge files. The full final target is owned
by `CertData.H1.Generated.Bridge.Targetassembly0000`. It remains conditional
on the 33 open Props. Generated modules have no imports from the AKLT library
back to CertData. `defaultTargets = ["AKLT"]` and the AKLT globs are unchanged;
ordinary builds do not compile the generated certificates.

Statement compatibility: current main and the supplied prebuilt statement
sources agree. The active worktree's `AKLT/Defs/OperatorContracts.lean` and
`AKLT/Blueprint/Top/Operator.lean` are older. They were neither copied nor
edited, and are excluded from the merge set. The clean-main check validates
the bridge against main, including the H1SectorWitnesses and V2 handoff.
See `phase3/statement-compatibility.json`. Unrelated future main commits do
not change that pinned compatibility result.

Historical Phase1 prototypes that import their generated Data/Check files are
archival rather than dependencies of the current bridge. They are retained
unchanged in the worktree, excluded from this minimal merge set and from the
production Lake globs. No old mathematical proof is claimed newly proved.

Phase-3 production is complete: all 7,964 owner oleans are retained, with the full receipt
in `phase3/verified-production.json`. To reuse them for final assembly, keep the matching
core/dependency artifact versions and compile the final file with `lake env lean FILE.lean`
on the configured import path. Restoring sources and requesting the Lake target is the
source rebuild route and may repeat reductions when Lake traces are absent.
