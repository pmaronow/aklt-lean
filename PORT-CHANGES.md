# Module-system port changes

Base: unported commit `933e99cddadb1ae6b85d5f4aff551b6f14f91f42`, materialized from main `d77c3ca85754582f91354dd848ac5a830f73727d`.

- All 615 AKLT sources: added `module`, public imports and a public/exposed section, with `backward.privateInPublic` and `backward.proofsInPublic` migration options. Original declarations, statements and proof bodies are preserved.
- `AKLT/Challenge/Main.lean`, `AKLT.Challenge.size_neZero`: added explicit `@[expose]` to the Prop-valued instance, matching Challenge. The proof body is unchanged.

- `Challenge.lean`, `AKLT.Defs.moment`: retain this original definition verbatim solely to preserve the shared numeral-proof helper referenced by `spinWeight`. The challenge generator records this selection; mathematical statements are unchanged.

## Proof-body changes

None. All original proof bodies and definition bodies are byte-preserved after accounting for the documented module/import/section visibility edits. The three statement aliases are unchanged, and h1_iff, h3_iff and main_iff retain their original Iff.rfl proofs. The module port resolves the legacy/modern Compass matcher difference. The first modern comparison additionally identified a shared numeral-proof helper in spinWeight: the original tree refers to moment._proof_1. Challenge now includes the original moment definition verbatim at its original position, so the generated helper has the same owner. The existing spinWeight body and all three advertised statement aliases are unchanged. No proof body was edited.

## Complete release hand-written extension

Source revision: `8f59d336acf2fc13428893faf26097890f4f288b`. The release adds every
hand-written file in the transitive import closure of `CertData.Close.All`, keeps
the existing development, and retains the empty H1 generation root and its closing
Audit. Generated certificate sources and legacy objects are not copied into Git.

- New legacy modules receive `module`, public imports, a public/exposed section,
  and the same two backward visibility migration options. All existing private
  modifiers, declaration names, definition bodies, and proof bodies are retained.
- `AKLT/Cert/H1/Literals.lean`: a `meta section` marks `rowExpr` and `elabIntRow`
  as elaborator code. Lean's module system requires a term elaborator to be meta.
  The functions' bodies are unchanged; generated terms remain ordinary literals.
- `CertData/H3/Kernel/Literal.lean`: the same `meta section` marks
  `decodeHexBalanced` and `elabH3Hex`. Their bodies are unchanged.
- `CertData/H3/Kernel/PrefixView.lean`: add
  `import all Init.Data.List.Sort.Basic` so `mergeFuel_eq` and `mergeSortFuel_eq`
  can use the original standard-library bodies in their existing simp calls.
  Neither proof body changes. No standard-library source or object is modified.
- The explicit exposure of `AKLT.Challenge.size_neZero` from the previous port is
  retained. All certificate-kernel public definitions receive exposed bodies,
  including Boolean checkers, signed packing, structure projections, and literal
  consumers. The exact inventory is in `verification/regen-interface/` and
  `REGEN-INTERFACE.md`; the H1 and H3 samples exercise reduction from another module.
- `ClosedTrail` keeps its name and body. Its doc comments now identify a first-hit
  path, including the retained regression template. Paper references to nonexistent
  labels are replaced with `d:model` and `d:poly` at their actual manuscript files.
- Comments, doc strings, and notes use American English. Lean identifiers and paper
  labels retain their spelling. `BRITISH-IDENTIFIERS.tsv` lists source identifier
  tokens with British spelling and their locations.

### Original proof-body changes in this extension

None. The token-level fidelity receipt checks all 1,104 imported hand-written
files against the pinned source after exactly the visibility edits above and
comment removal. No original statement or definition changes meaning. The
retained two-input Solution is code-identical to its earlier version. Its
`h1_iff`, `h3_iff`, and `main_iff` proofs remain `Iff.rfl`.

### New package proof bodies

The authorized root Solution is changed from the conditional wrapper to
`AKLTPalomar.aklt_gap : Main := main_iff.mpr CertData.Close.main`. Root Challenge
has the corresponding unconditional placeholder. New `RegenSamples` theorems
are tiny kernel reductions and applications of the existing H1/H3 soundness
lemmas; they are interface tests and are not production certificate claims.

### Build configuration repair

The explicit `CertData.H1.Generated` root was added to its library globs; a
submodule-only glob does not build that empty hand-written root when Handwritten
imports it. No Lean declaration or proof changes for this repair.
