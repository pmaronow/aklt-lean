# H1 finite certificate library

The hand-written H1 checkers, soundness theorems, and mathematical leaves are
ported to Lean's module system. Generated production sources belong under
`CertData/H1/Generated/` and are excluded from Git. They must be regenerated and
rebuilt against this release; legacy oleans are not compatible artifacts.

The retained generator scripts are under `AKLT/Cert/H1/tools/`. The regeneration
agent must adapt their output headers and supply the exact pinned numeric inputs,
module manifest, source archive, and build/axiom receipts. The old generation
workflow used production owner modules under `Batch/` and `Bridge/`; preserve all
module and declaration names. The closing module imports
`CertData.H1.Generated.Bridge.Targetassembly0000`.

See `REGEN-INTERFACE.md` and `verification/generated-modules.json` for the complete
API, generated inventory, and compiling cross-module samples. `CertDataH1` is the
Lake library. `CertData.H1.Close.Main` and its Audit require the regenerated family.
