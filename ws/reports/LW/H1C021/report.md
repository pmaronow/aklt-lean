STATUS: PARTIAL

The frozen leaf is reduced to one explicit, closed algebraic residual. The requested unconditional declaration `AKLT.W.H1C021.main` is **not** delivered. No conditional theorem is presented as a proof of that declaration.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Main.lean) — Exact reduction to the frozen leaf, including all center insertions and current/next scalars.
- [Congruence.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Congruence.lean) — Closed residual definitions and reduction from local polynomial products to pure monomial congruence.
- [Monomials.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Monomials.lean) — Local moment-term expansions; distribution of products; integer coefficient factorization; color and slot bounds.
- [Expansion.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Expansion.lean) — Symbolic four-color path expansions of both contractions and replacement of accepted tables by local entries.
- [Radix.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Radix.lean) — Generic mixed-radix encoding/decoding and its application to exchangeBasisCode and network strides.
- [Basic.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Basic.lean) — Gaussian arithmetic, Pauli Y signs, pair-basis forms and norms, and accepted-table indexing.
- [Basis.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Basis.lean) — Token/group equivalence and sitewise factorization of the actual integer exchange-basis congruence.
- [Rational.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Rational.lean) — Rational-complex arithmetic bridge and factorization of a single Pauli-exponent monomial.
- [Linearity.lean](/home/ubuntu/aklt/wt/LW_H1C021/AKLT/W/H1C021/Linearity.lean) — Finite-sum and scalar linearity of rationalSectorEntry.

All nine Lean files are transitively imported by `Main.lean`; no orphan Lean files remain. Only the assigned task directory and report directory were modified. The previous report remains in `report.luna.md`.

## Exported declarations and statements

The principal reduction is:

```lean
theorem AKLT.W.H1C021.main_of_monomialCongruence
    (hm : AKLT.W.H1C021.Residual_monomialCongruence) :
    AKLT.Cert.H1.Production.Leaves.tensorSubstitution
```

The only independent unresolved proposition is:

```lean
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production
namespace AKLT.W.H1C021

def Residual_monomialCongruence : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
  ∀ a b : CentralBasis π r ε, ∀ css : List (List Nat), css.length = 8 →
    css.map List.length =
      (List.range 8).map (fun i => groupSlots π r (groupPoint i)) →
    (∀ cs ∈ css, ∀ c ∈ cs, c < 4) →
    (formProduct π r ε a.val b.val 0 css).re =
      (rationalSectorEntry π r ε (monomialProduct 0 css) a b : ℝ)

end AKLT.W.H1C021
```

Here `monomialProduct` multiplies one `vectorMonomial` per ring group, and `formProduct` multiplies the corresponding complex `localForm` entries at the mathematical `groupDigit` values. The real part is taken **after** multiplying the complex factors. This retains all cross-site Y signs. The residual has no network matrices, accepted tables, mixed-radix codes, moment coefficients, outgoing site, current/next Boolean, or center-insertion sum.

Further principal exports:

- `productCongruence_of_monomialCongruence : Residual_monomialCongruence → Residual_productCongruence`. Thus `Residual_productCongruence` is an intermediate obligation, not a second independent assumption.
- `main_of_productCongruence : Residual_productCongruence → AKLT.Cert.H1.Production.Leaves.tensorSubstitution`.
- `network_basis_digit`: for any accepted network and site index, decoding `exchangeBasisCode` with that site's stride and dimension returns `groupDigit`.
- `acceptedTable_entry`: every bounded accepted table entry equals the corresponding `localEntry`.
- `directRingValue_expansion` and `polynomialRingValue_expansion`: both ring contractions expand over the same color paths into products of local entries/polynomials.
- `tensorProduct_complex_terms` and `tensorProduct_polynomial_terms`: local moment sums distribute over the products.
- `termsComplex_factor` and `termsPolynomial_factor`: the same integer coefficient factors out of the complex and polynomial terms.
- `sectorTensor_congruence`: the **actual** `exchangeBasisVector` congruence of any product of one-token matrices factors into one local congruence per group.
- `rationalSectorEntry_complex_re`: the exact rational entry is the real part of the corresponding complex Pauli congruence.
- `rationalSectorEntry_pauliMonomial`: for a polynomial already presented as `monomial (pauliExponent J d) 1`, the sector entry is the real part of the product of the local congruence sums.
- `pairForm_value` and `pair_basis_norms`: the literal pair form has the integer symmetric/exterior coordinates, with squared norms 1, 2, 1, 2. `pauliZ_value` checks the imaginary signs against `Defs.pauli`.

All **82** exported theorem declarations, with their exact Lean types, are recorded in [declarations.txt](/home/ubuntu/aklt/reports/LW/H1C021/declarations.txt). Their source-file inventory is [exports.tsv](/home/ubuntu/aklt/reports/LW/H1C021/exports.tsv). The transparent intermediate definitions are in the linked Lean sources.

## Remaining proof

Open exact name: `AKLT.W.H1C021.Residual_monomialCongruence`.

The remaining work is to connect the eight lists of colors to the token-indexed Pauli label:

1. Construct the label `d : reductionVectors π r → Fin 4` from the group color lists and prove `monomialProduct 0 css = MvPolynomial.monomial (pauliExponent (reductionVectors π r) d) 1`. This needs the ring-site/group permutation, the leader/second-token correspondence, and the fact that inactive groups contribute the constant factor.
2. Instantiate `rationalSectorEntry_pauliMonomial`, identify its local one-slot/two-slot sums with `localForm` using `pauliZ_value` and `pairForm_value`, and reindex the group product into the eight-site order. In the exterior case the local basis digit must be 3, while its `GroupBasis` coordinate is 0; `groupDigit` already implements this distinction.

The global finite-sum factorization is proved in `sectorTensor_congruence`; what is still missing is its complete connection to the list-indexed monomial and local-form representation. No counterexample or missing premise was found. No unproved blueprint leaf is imported as a lemma. The permitted proved-index modules `AKLT.W.H1M032.Main` and `AKLT.W.H1M047.Main` supply group-geometry and Pauli-exponent injectivity lemmas.

The earlier `Residual_vacuumTransfer` and `Residual_centerTransfer` have been replaced: the ring expansion and all center/scalar assembly are now proved from the smaller monomial residual.

## Build and validation

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C021.Main` — succeeded; final timed build **43.66 s**. Log: [build.log](/home/ubuntu/aklt/reports/LW/H1C021/build.log).
- `lake env lean /tmp/h1c021-axioms.lean` — succeeded, **6.35 s**; audited every exported theorem.
- `lake env lean /tmp/h1c021-signatures.lean` — succeeded; ELAPSED_SECONDS=6.70.
- Forbidden-form scan of the delivered Lean sources found none. No `sorry`, new axioms, unsafe code, native evaluation, or unbounded heartbeat setting is used.
- Checked that all nine task Lean files are transitively imported by `Main.lean`.
- The independent con-ron/NanoDa checks were not run here. The original unconditional exact-type check cannot pass until the residual is proved and `AKLT.W.H1C021.main` is added.

## Axiom audit

All 82 exported theorems use only subsets of `propext`, `Classical.choice`, and `Quot.sound`. Full `#print axioms` output follows (also saved in [axioms.txt](/home/ubuntu/aklt/reports/LW/H1C021/axioms.txt)):

```text
'AKLT.W.H1C021.list_sum_flatMap' depends on axioms: [propext]
'AKLT.W.H1C021.gaussianValue_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.gaussianValue_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.gaussianValue_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.gaussianValue_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.gaussianValue_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.gaussianValue_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.gaussianValue_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.pauliZ_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.basisPair_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.pairForm_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.pair_basis_norms' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.localTable_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.localTable_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.acceptedTable_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupSlotToken_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupSlotToken_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupSlotToken_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupSlotEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupConfigEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.sum_sum_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.tensor_basis_congruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupSlotToken_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupSlotToken_last' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.exchangeBasisVector_group_product' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.sectorTensor_congruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.network_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.network_leaf_slots_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.productCongruence_of_monomialCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.colorPaths_length' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.colorPaths_bound' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.colorContraction_expansion' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.directSiteMatrix_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.fourMul_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.polyMul_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.directRingProduct_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.polynomialRingProduct_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.directRingValue_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.polynomialRingValue_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.tensorProduct_congr' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.tableColorEntry_eq_localColorEntry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.network_tensorProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalOperatorEntry_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalSectorEntry_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalSectorEntry_list_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalOperatorEntry_C_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalSectorEntry_C_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.sumGaussian_re_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.complex_re_list_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.ringTransfer_of_productCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.centerCodes_bound' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.centerTransfer_of_productCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.main_of_productCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.main_of_monomialCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.localPolynomial_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.localEntry_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.colorChoices_spec' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.network_leaf_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.localTerms_spec' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.tensorProduct_polynomial_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.tensorProduct_complex_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.termsPolynomial_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.termsComplex_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.termChoices_spec' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.radixCode_start' depends on axioms: [propext]
'AKLT.W.H1C021.radixCode_append' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C021.radixCode_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.radixCode_decode_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.radixCode_decode' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupDigit_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.groupDim_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.exchangeBasisCode_radix' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.exchangeBasisCode_digit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.network_dimensions' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.network_basis_digit' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalComplexValue_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalPauli_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalComplexValue_foldl' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalOperatorEntry_complex_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalSectorEntry_complex_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.pauliOperator_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.rationalSectorEntry_pauliMonomial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PARTIAL.
- Nine compiled Lean files, all imported by `AKLT.W.H1C021.Main`.
- Exact frozen leaf reduced by `AKLT.W.H1C021.main_of_monomialCongruence`.
- Open: `AKLT.W.H1C021.Residual_monomialCongruence` only.
- `Residual_productCongruence` is derived from that residual.
- `AKLT.W.H1C021.main` is absent; unconditional exact-type check remains unsatisfied.
- Accepted-table entry decoding and mixed-radix basis-digit alignment are proved.
- Ring color-path expansion, local moment distribution, and all center/current/next assembly are proved.
- Actual exchange-basis tensor congruence factors sitewise; rational/complex identification is proved.
- Pauli signs and unnormalized norms 1,2,1,2 are proved; no square-root normalization.
- Remaining: color-list → Pauli-exponent dictionary, local sum identification, eight-site/group reindexing.
- Reused indexed modules H1M032.Main and H1M047.Main.
- Build succeeded in 43.66 s; all 82 exported theorem axiom audits passed.
- No false-statement claim; no new axioms or soundness escapes; independent kernels not run.
- Pass the single named monomial residual and existing supporting lemmas to the next proof writer.
