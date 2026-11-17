# Module-system port changes

Base: unported commit `933e99cddadb1ae6b85d5f4aff551b6f14f91f42`, materialized from main `d77c3ca85754582f91354dd848ac5a830f73727d`.

- All 615 AKLT sources: added `module`, public imports and a public/exposed section, with `backward.privateInPublic` and `backward.proofsInPublic` migration options. Original declarations, statements and proof bodies are preserved.
- `AKLT/Challenge/Main.lean`, `AKLT.Challenge.size_neZero`: added explicit `@[expose]` to the Prop-valued instance, matching Challenge. The proof body is unchanged.

- `Challenge.lean`, `AKLT.Defs.moment`: retain this original definition verbatim solely to preserve the shared numeral-proof helper referenced by `spinWeight`. The challenge generator records this selection; mathematical statements are unchanged.

## Proof-body changes

None so far. Every subsequent proof-body edit must be listed here by file, declaration and reason. The module port resolves the legacy/modern Compass matcher difference. The first modern comparison additionally identified a shared numeral-proof helper in spinWeight: the original tree refers to moment._proof_1. Challenge now includes the original moment definition verbatim at its original position, so the generated helper has the same owner. The existing spinWeight body and all three advertised statement aliases are unchanged. No proof body was edited.
