# H1 finite certificate library

The hand-written H1 checkers, soundness theorems, and mathematical proofs use
Lean's module system. The 7,964 generated production sources belong under
`CertData/H1/Generated/Batch/` and `Bridge/` and are excluded from Git.
The Lake library is `CertDataH1`; the closing module imports
`CertData.H1.Generated.Bridge.Targetassembly0000`.

The release provides numeric inputs, generated-source archives, and receipts.
See [artifacts](../../docs/ARTIFACTS.md), [the interface](../../docs/REGEN-INTERFACE.md),
and [the H1 regeneration guide](../../docs/regeneration/H1.md). Generator
scripts stay under `AKLT/Cert/H1/tools/`. `CertData.H1.Close.Main` and
`CertData.H1.Close.Audit` consume the checked generated family.
