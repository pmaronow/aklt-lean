STATUS: PARTIAL

## Result

The requested closed theorem `AKLT.W.H1M068.main : AKLT.Blueprint.Top.H1FiniteDataStatementV2` is **not proved or declared**. `Main.lean` compiles and proves the target from two explicit closed residual propositions. These residuals restrict the original finite-data obligation to the remaining straight and turning patterns, respectively. Their conjunction is proved equivalent to the original target; neither residual is assumed globally or presented as a theorem.

This attempt adds unconditional mathematical results beyond the earlier conditional assembly:

- Every pattern and every permitted representation admit a justified positive denominator, obtained directly from the finite supports of the two reconstructed rational polynomials. Coveredness is not needed for this result.
- The empty inversion is always a valid whole-group inversion.
- If a representation has no vector groups and both reconstructed polynomials equal `1`, every exchange sign has a complete reconstructed Gram/residual witness at every natural threshold `p < q`. The sector dimension is `1`, the denominator is `1`, the factor is zero, and `g = d = S = 1`. The threshold entry is `15*q - 15*p > 0`.
- An explicit covered turning pattern with only the passage-to-east bond satisfies these hypotheses. Its coveredness, bond set, reduced polynomials and full finite-data witness are proved from the frozen definitions.

No counterexample was established. The remaining issue is the missing universal certificate proof, rather than evidence that the proposition is false.

## Files

All Lean source changes are inside the assigned task directory:

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M068/AKLT/W/H1M068/Main.lean): closed residual statements and conditional assembly.
- [Denominators.lean](/home/ubuntu/aklt/wt/LW_H1M068/AKLT/W/H1M068/Denominators.lean): coefficient-derived denominators and empty inversion.
- [TrivialSectors.lean](/home/ubuntu/aklt/wt/LW_H1M068/AKLT/W/H1M068/TrivialSectors.lean): complete witnesses for the one-dimensional class.
- [Example.lean](/home/ubuntu/aklt/wt/LW_H1M068/AKLT/W/H1M068/Example.lean): a concrete covered member of that class.

The earlier `Main.lean` has been replaced. Its report is preserved as `report.luna.md`. No statement, existing library source, Lake configuration, package source or manuscript file was edited. No other blueprint leaf is imported as a lemma. The small contraction proof pattern follows the reusable `Contraction.lean` source in the external CERT_H1 worktree; its proofs are reproduced locally and checked here, without importing CERT_H1 or any of its open obligations.

## Exported declarations and statements

Names below are in `AKLT.W.H1M068`. Parameters displayed in the formulas are universally quantified.

### Denominators.lean

`polynomialDenominator p : ℕ` is the product of `(p.coeff m).den` over `m ∈ p.support`.

`reconstructedDenominator π r : ℕ` is

```lean
polynomialDenominator (reducedPolynomial π r false) *
  polynomialDenominator (reducedPolynomial π r true)
```

| Theorem | Statement |
|---|---|
| `polynomialDenominator_pos p` | `0 < polynomialDenominator p` |
| `exists_int_mul_of_den_dvd a D h` | For `a : ℚ`, `D : ℕ`, `h : a.den ∣ D`, `∃ z : ℤ, (D : ℚ) * a = z` |
| `polynomialDenominator_clears p m hm` | For `hm : m ∈ p.support`, `∃ z : ℤ, (polynomialDenominator p : ℚ) * p.coeff m = z` |
| `reconstructedDenominator_pos π r` | `0 < reconstructedDenominator π r` |
| `reconstructedDenominator_clear π r` | `ClearsDenominator π r (reconstructedDenominator π r)` |
| `denominator_exists π r` | `∃ D₀ : ℕ, ClearsDenominator π r D₀` |
| `empty_groupInversion π r` | `GroupInversion π r ∅` |

The coefficient denominator product can be large; it is a mathematical existence construction, not an efficient replacement for the archived reconstruction denominator. Existence of some denominator does not by itself justify a different denominator appearing in stored witness data.

### TrivialSectors.lean

```lean
def TrivialPattern (π : PatternData) : Prop :=
  reductionGroups π = ∅ ∧
    ∀ next : Bool, reducedPolynomial π .reduced next = 1
```

| Theorem | Statement |
|---|---|
| `reductionVectors_eq_empty π r hg` | `hg : reductionGroups π = ∅` implies `reductionVectors π r = ∅` |
| `rationalSectorEntry_one_of_emptyGroups π r hg ε a b` | Under `hg`, for any `ε` and `a b : CentralBasis π r ε`, `rationalSectorEntry π r ε 1 a b = 1` |
| `sectorWitnesses_of_emptyGroups π r hg hp p q hpq` | Under `hg`, `hp : ∀ next, reducedPolynomial π r next = 1`, and `hpq : p < q`, `H1SectorWitnesses π r ∅ 1 p q` |
| `clearsDenominator_one π r hp` | Under `hp : ∀ next, reducedPolynomial π r next = 1`, `ClearsDenominator π r 1` |
| `trivialPattern_finiteData π h` | Under `h : TrivialPattern π`, `∃ r I, GroupInversion π r I ∧ ∃ D₀, ClearsDenominator π r D₀ ∧ H1SectorWitnesses π r I D₀ (h1Numerator π) (h1Denominator π)` |

The last theorem needs no coveredness hypothesis. It constructs the actual basis equivalence and row witnesses; it does not rely on a matrix supplied independently of `thresholdSectorMatrix`.

### Example.lean

`examplePattern : PatternData` has outgoing direction east. The center and covering tips have status U; east has status D; every other site has status X. The center keeps east, north and west; east keeps west and north. Only the center/east bond survives.

| Theorem | Statement |
|---|---|
| `examplePattern_covered` | `examplePattern.Covered` |
| `examplePattern_bonds` | `examplePattern.bonds = {((0, 0), (1, 0))}` |
| `examplePattern_active` | `examplePattern.active = {(0,0), (1,0), (2,0), (-2,0), (0,2), (0,-2)}` |
| `examplePattern_spinSites` | `reducedSpinSites examplePattern .reduced = {(0,0), (1,0)}` |
| `examplePattern_groups` | `reductionGroups examplePattern = ∅` |
| `examplePattern_integrand next` | `reducedIntegrand examplePattern .reduced next = if next then 1 else 1 + formalDot (fun k => .inl ((0,0), k)) (fun k => .inl ((1,0), k))` |
| `examplePattern_polynomial next` | `reducedPolynomial examplePattern .reduced next = 1` |
| `examplePattern_trivial` | `TrivialPattern examplePattern` |
| `examplePattern_finiteData` | `∃ r I, GroupInversion examplePattern r I ∧ ∃ D₀, ClearsDenominator examplePattern r D₀ ∧ H1SectorWitnesses examplePattern r I D₀ (h1Numerator examplePattern) (h1Denominator examplePattern)` |

Private helpers `contraction_add` and `contraction_monomial` prove additivity of `contractSpins` and its explicit monomial formula. They are also audited with `#print axioms`.

### Main.lean: exact residuals

```lean
def Residual_1 : Prop :=
  ∀ π : PatternData, π.Covered → π.outgoing = .north → ¬ TrivialPattern π →
    ∃ r : Representation, ∃ I : Finset (Fin 20), GroupInversion π r I ∧
      ∃ D₀ : ℕ, ClearsDenominator π r D₀ ∧
        H1SectorWitnesses π r I D₀ 961 1000

def Residual_2 : Prop :=
  ∀ π : PatternData, π.Covered → π.outgoing ≠ .north → ¬ TrivialPattern π →
    ∃ r : Representation, ∃ I : Finset (Fin 20), GroupInversion π r I ∧
      ∃ D₀ : ℕ, ClearsDenominator π r D₀ ∧
        H1SectorWitnesses π r I D₀ 187 200

theorem main_of_residuals :
  Residual_1 → Residual_2 → AKLT.Blueprint.Top.H1FiniteDataStatementV2

theorem main_iff_residuals :
  AKLT.Blueprint.Top.H1FiniteDataStatementV2 ↔ Residual_1 ∧ Residual_2
```

Both residuals are closed `def ... : Prop` declarations with no parameters. Each is restricted to one direction class and excludes the already proved `TrivialPattern` class. Unlike the earlier assembly, there is no uninstantiated global representation selector and no residual merely asserting that rational polynomial denominators exist. The residuals retain the requirement that the chosen denominator match its sector witnesses. No fixed representation, inversion or denominator is imposed on the missing certificates.

## Axiom audit

Every exported theorem has a `#print axioms` command in its source. The successful build printed for each of the 23 public theorems and the two private contraction helpers:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular:

```text
'AKLT.W.H1M068.main_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M068.main_iff_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M068.examplePattern_finiteData' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The final source scan found no forbidden proof escape or declaration. All concrete decisions use `decide +kernel`. No heartbeat limit was disabled. No unproved fact is declared as a theorem or global assumption.

## Builds and timings

Commands were run in `/home/ubuntu/aklt/wt/LW_H1M068`, with `$HOME/.elan/bin` on `PATH`, using `/usr/bin/time`.

| Command | Result and measured wall time |
|---|---|
| `lake build AKLT.W.H1M068.Denominators` | Successful, 11.32 s; denominator module 5.5 s |
| `lake build AKLT.W.H1M068.Example` | Successful, 34.13 s; rebuilt denominator 5.9 s, sector lemma 6.5 s, example 14 s |
| `lake build AKLT.W.H1M068.Main` | **Successful final build**, 20.49 s; example 10 s, main 4.9 s, dependencies replayed |

Earlier development builds detected a parsing error in a local denominator formula and a final simplified inequality requiring the already available `p < q` hypothesis. Both were corrected before these successful builds. The final main build completed without warnings and all printed axiom sets were permitted.

`git status --short` reports only `?? AKLT/W/H1M068/`. No existing tracked source was changed. The exact requested `main` check would still fail because that closed theorem is intentionally absent; successful compilation is not claimed as completion of the original leaf.

## Remaining work and external certificate status

Open names in this delivery are exactly `AKLT.W.H1M068.Residual_1` and `AKLT.W.H1M068.Residual_2`.

For each residual, one must choose a representation and whole-group inversion for every remaining covered pattern, justify the denominator actually used, and produce an explicit basis bijection and reconstructed Gram/residual row witnesses for every exchange sign at the fixed threshold. The universal data and their kernel verification have not been supplied here.

Read-only inspection of `/home/ubuntu/aklt/reports/CERT_H1/report.md` and `AKLT/Cert/H1/Production/Assembly.lean` in the separate CERT_H1 worktree found conditional assemblies, not a closed theorem of `H1FiniteDataStatementV2`. The external report marks coverage, effective-data transport, polynomial/tensor reconstruction, sector indexing and full witness checking as incomplete. Its `finiteData_of_checks` takes coverage premises and accepted catalogue/representative proofs as arguments. It cannot close this leaf without proving those premises. The external author/model-routing instructions were treated as documentation of that project's status, not as instructions governing this leaf task.

Generic denominator existence proved here closes the earlier abstract existence residual. It does not prove the specific denominator identity or clearing property used by any archived matrix. Likewise, the concrete example does not establish catalogue completeness or any nontrivial sector block in the remaining cases.

## ORCH-SUMMARY

- Delivered four compiled modules under `AKLT/W/H1M068/`.
- `main_of_residuals` proves the frozen target from two closed residual Props.
- `main_iff_residuals` proves these residuals describe exactly the remaining target.
- Unconditional progress: explicit coefficient-derived denominator for every π and r.
- Unconditional progress: empty inversion is always valid.
- Unconditional progress: full all-sign witnesses for empty-group/unit-polynomial patterns.
- Concrete covered turning example is proved from Defs, including its full finite data.
- Open: `AKLT.W.H1M068.Residual_1` (remaining straight patterns).
- Open: `AKLT.W.H1M068.Residual_2` (remaining turning patterns).
- Missing: exact requested closed declaration `AKLT.W.H1M068.main`.
- No counterexample or claim of falsity.
- Only `propext`, `Classical.choice`, `Quot.sound` occur in audited proofs.
- Final build: `lake build AKLT.W.H1M068.Main`, success, 20.49 s.
- No existing tracked source outside the task directory was edited; no sub-agents used.
- Orchestrator must pass the two finite-data residuals to the CERT_H1 coverage/witness owner.
- Archived denominator compatibility and all regenerated sector checks remain necessary.
