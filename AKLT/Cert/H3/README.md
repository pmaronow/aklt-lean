# H3 finite certificate library

The executable interface is in `CertData/H3/Kernel/Production/Model.lean`,
`Replay.lean`, and `Batching.lean`; the kernel, packed arithmetic, and soundness
layers are hand-written module-system files. Generated literals, checks, and
data-dependent assemblies belong to `CertDataH3` and are excluded from Git.
The unconditional closing module imports `CertData.H3.Bridge.All`.

Regenerate all five production cases B1, B2, C1, C2, and C3 against the ported
kernels. Preserve module and declaration names. The retained generator scripts
in this directory still need module-header adaptation and pinned numeric data
inputs from the regeneration agent. Do not reuse legacy certificate oleans.
See `REGEN-INTERFACE.md` for the exposed API and compiling cross-module samples,
and `verification/generated-modules.json` for the exact 5,032-module inventory.
