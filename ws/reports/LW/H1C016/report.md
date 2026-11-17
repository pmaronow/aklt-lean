STATUS: PROVED

Delivered the unconditional theorem with the exact requested name and type:

```lean
theorem AKLT.W.H1C016.main :
  AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound
```

Files:

- `AKLT/W/H1C016/Main.lean`: final assembly.
- `AKLT/W/H1C016/Norms.lean`: Gaussian L1 arithmetic and disjoint table-lookup bounds.
- `AKLT/W/H1C016/Ring.lean`: entrywise contraction and closed-ring bounds.
- `AKLT/W/H1C016/Geometry.lean`: Boolean-check decoding, sector/base equality, positive dimensions, and center-pair counts.
- `AKLT/W/H1C016/Threshold.lean`: current/next and threshold estimates.
- `report.md`, `build.log`, and `exact-type.log` in this report directory.

All five Lean files are transitively imported by `Main.lean`. Only files in the assigned Lean directory and report directory were changed. The earlier partial implementation was replaced; its original report remains in `report.luna.md`.

The proof sets `L(z) = z.re.natAbs + z.im.natAbs` and lets `B` be the product of the local `tableAbs` values. Distinct table lookups use disjoint leaves, so their L1 sum is bounded by `tableAbs`, without a table-shape assumption. For a positive local dimension, the sixteen indices obtained by varying the two four-state matrix indices are distinct. This bounds each local matrix's total L1 mass by its table absolute sum. Matrix multiplication then bounds every entry of a ring tail by its product of local masses. Closing a nonempty ring uses the first matrix's total mass and yields `L(directSectorRingValue) ≤ B`, without an additional factor of four.

Accepted geometry allows at most three center sites, at ring positions 0, 2, and 4, and includes the outgoing site. Hence there are at most three center pairs and at most one pair avoiding the outgoing site. Each pair contributes three ring values. The resulting estimates are `L(current) ≤ 12*B` and `L(next) ≤ 8*B`. Gaussian scaling and addition give

```text
L(directSectorThreshold) ≤ B * (5*q*12 + 3*p*8).
```

The checked inequality in `parametersCheck` is exactly the strict comparison of this quantity with `2^(width-1)`. `sectorNetworkCheck` identifies the sector base tables with the original network tables. This proves the bound for all natural row and column indices. It bounds the real-plus-imaginary coefficient magnitudes requested by the leaf.

No other proved blueprint leaf was imported or assumed. No residual statements remain.

Exported declarations and statements follow. Every name below is in namespace `AKLT.W.H1C016`; the displayed signatures use `open AKLT.Cert.H1 AKLT.Cert.H1.Production` and `open scoped BigOperators`. Private implementation lemmas are omitted.

Main.lean:

```lean
theorem main : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound
```

Norms.lean:

```lean
def gaussianL1 (z : Gaussian) : Nat := z.re.natAbs + z.im.natAbs

@[simp] theorem gaussianL1_zero : gaussianL1 Gaussian.zero = 0

@[simp] theorem gaussianL1_one : gaussianL1 Gaussian.one = 1

theorem gaussianL1_add_le (a b : Gaussian) :
    gaussianL1 (a.add b) ≤ gaussianL1 a + gaussianL1 b

theorem gaussianL1_scale (n : Int) (a : Gaussian) :
    gaussianL1 (a.scale n) = n.natAbs * gaussianL1 a

theorem gaussianL1_mul_le (a b : Gaussian) :
    gaussianL1 (a.mul b) ≤ gaussianL1 a * gaussianL1 b

theorem gaussianL1_sumGaussian_le (xs : List Gaussian) :
    gaussianL1 (sumGaussian xs) ≤ (xs.map gaussianL1).sum

theorem sum_range_list {α : Type} [AddCommMonoid α] (n : Nat) (f : Nat → α) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i

theorem gaussianL1_sum_range (n : Nat) (f : Nat → Gaussian) :
    gaussianL1 (sumGaussian ((List.range n).map f)) ≤
      ∑ i ∈ Finset.range n, gaussianL1 (f i)

theorem table_sum_le (t : Table) (s : Finset Nat) :
    ∑ i ∈ s, gaussianL1 (t.get i) ≤ tableAbs t

def fourMass (a : FourMatrix) : Nat :=
  ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4, gaussianL1 (matrixEntry a i j)

theorem matrixEntry_tabulate (f : Nat → Nat → Gaussian) {i j : Nat}
    (hi : i < 4) (hj : j < 4) :
    matrixEntry ((List.range 4).map fun l => (List.range 4).map (f l)) i j = f i j

theorem table_slice_le (t : Table) (dim : Nat) (hd : 0 < dim) (a b v : Nat) :
    (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
      gaussianL1 (t.get (tableIndex dim a i j v b))) ≤ tableAbs t

theorem local_mass_le (s : SectorSite) (hd : 0 < s.base.spec.dim) (row col v : Nat) :
    fourMass (directSectorSiteMatrix s row col v) ≤ tableAbs s.base.table
```

Ring.lean:

```lean
theorem matrixEntry_fourMul (a b : FourMatrix) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    matrixEntry (fourMul a b) i j = sumGaussian ((List.range 4).map fun k =>
      (matrixEntry a i k).mul (matrixEntry b k j))

theorem matrixEntry_fourIdentity_le {i j : Nat} (hi : i < 4) (hj : j < 4) :
    gaussianL1 (matrixEntry fourIdentity i j) ≤ 1

theorem row_mass_le (a : FourMatrix) {i : Nat} (hi : i < 4) :
    (∑ k ∈ Finset.range 4, gaussianL1 (matrixEntry a i k)) ≤ fourMass a

theorem matrixEntry_mul_le (a b : FourMatrix) (B : Nat)
    (hb : ∀ i < 4, ∀ j < 4, gaussianL1 (matrixEntry b i j) ≤ B)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    gaussianL1 (matrixEntry (fourMul a b) i j) ≤
      (∑ k ∈ Finset.range 4, gaussianL1 (matrixEntry a i k)) * B

theorem trace_mul_le (a b : FourMatrix) (B : Nat)
    (hb : ∀ i < 4, ∀ j < 4, gaussianL1 (matrixEntry b i j) ≤ B) :
    gaussianL1 (fourTrace (fourMul a b)) ≤ fourMass a * B

theorem ring_entry_le (ss : List SectorSite)
    (hd : ∀ s ∈ ss, 0 < s.base.spec.dim) (row col : Nat) (codes : List Nat)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    gaussianL1 (matrixEntry (directSectorRingProduct row col ss codes) i j) ≤
      (ss.map (fun s => tableAbs s.base.table)).prod

theorem ring_value_le (ss : List SectorSite) (hn : ss ≠ [])
    (hd : ∀ s ∈ ss, 0 < s.base.spec.dim) (row col : Nat) (codes : List Nat) :
    gaussianL1 (directSectorRingValue ss row col codes) ≤
      (ss.map (fun s => tableAbs s.base.table)).prod
```

Geometry.lean:

```lean
theorem sector_bases_eq (base : List PackedSite) (ss : List SectorSite) (parity : Nat)
    (h : sectorNetworkCheck base parity ss = true) : ss.map SectorSite.base = base

theorem parameters_dimensions (base : List PackedSite) (out width lanes denominator p q : Nat)
    (h : parametersCheck base out width lanes denominator p q = true) :
    ∀ s ∈ base, 0 < s.spec.dim

theorem geometry_spec (a : Input) (base : List PackedSite) (h : geometryCheck a base = true) :
    base.length = 8 ∧ ∀ i (hi : i < base.length), base[i].spec = inputSpec a i

theorem center_counts (a : Input) (base : List PackedSite) (out : Nat)
    (hi : inputCheck a = true) (hg : geometryCheck a base = true) (ho : out = 2*a.outgoing) :
    (centerPairs base).length ≤ 3 ∧
      ((centerPairs base).filter (fun (x,y) => x != out && y != out)).length ≤ 1
```

Threshold.lean:

```lean
theorem gaussianL1_sum_map_le {α : Type} (xs : List α) (f : α → Gaussian) (B : Nat)
    (h : ∀ x ∈ xs, gaussianL1 (f x) ≤ B) :
    gaussianL1 (sumGaussian (xs.map f)) ≤ xs.length * B

theorem gaussianL1_sum_skip_le {α : Type} (xs : List α) (skip : α → Bool)
    (f : α → Gaussian) (B : Nat) (h : ∀ x ∈ xs, gaussianL1 (f x) ≤ B) :
    gaussianL1 (sumGaussian (xs.filterMap (fun x => if skip x then none else some (f x)))) ≤
      (xs.filter (fun x => !skip x)).length * B

theorem current_next_bound (ss : List SectorSite) (out row col B : Nat)
    (h : ∀ codes, gaussianL1 (directSectorRingValue ss row col codes) ≤ B) (next : Bool) :
    gaussianL1 (directSectorCurrentNext ss out row col next) ≤
      (if next then 5 else 3) * B +
      ((centerPairs (ss.map SectorSite.base)).filter (fun xy =>
        !(next && (xy.1 == out || xy.2 == out)))).length * (3*B)

theorem threshold_bound (ss : List SectorSite) (out p q row col B : Nat)
    (h : ∀ codes, gaussianL1 (directSectorRingValue ss row col codes) ≤ B)
    (hc : (centerPairs (ss.map SectorSite.base)).length ≤ 3)
    (hn : ((centerPairs (ss.map SectorSite.base)).filter
      (fun xy => xy.1 != out && xy.2 != out)).length ≤ 1) :
    gaussianL1 (directSectorThreshold ss out p q row col) ≤ B * (5*q*12+3*p*8)
```

`#print axioms` was run on every exported theorem. Output from the successful build:

```text
'AKLT.W.H1C016.gaussianL1_zero' depends on axioms: [propext]
'AKLT.W.H1C016.gaussianL1_one' depends on axioms: [propext]
'AKLT.W.H1C016.gaussianL1_add_le' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C016.gaussianL1_scale' depends on axioms: [propext]
'AKLT.W.H1C016.gaussianL1_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.gaussianL1_sumGaussian_le' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C016.sum_range_list' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.gaussianL1_sum_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.table_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.matrixEntry_tabulate' depends on axioms: [propext]
'AKLT.W.H1C016.table_slice_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.local_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.sector_bases_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.parameters_dimensions' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C016.geometry_spec' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C016.center_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.matrixEntry_fourMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.matrixEntry_fourIdentity_le' depends on axioms: [propext]
'AKLT.W.H1C016.row_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.matrixEntry_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.trace_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.ring_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.ring_value_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.gaussianL1_sum_map_le' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C016.gaussianL1_sum_skip_le' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C016.current_next_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.threshold_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C016.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All reported axioms belong to the permitted set. A source scan found none of the forbidden proof or execution constructs.

Validation:

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C016.Main` succeeded. The timed build rebuilt all five task modules and took 27.15 seconds overall. Lean reported 5.7 seconds for Norms, 7.9 for Geometry, 5.4 for Ring, 5.6 for Threshold, and 5.3 for Main; independent dependency builds overlapped. The only warnings were replayed warnings from existing `AKLT.Gen.Gram` modules.
- A separate `lake env lean --stdin` invocation imported `Main`, checked its exported name, elaborated `example : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound := AKLT.W.H1C016.main`, and printed its axioms. It succeeded in 6.11 seconds, with output:

```text
AKLT.W.H1C016.main : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound
'AKLT.W.H1C016.main' depends on axioms: [propext, Classical.choice, Quot.sound]
ELAPSED_SECONDS=6.11
```

Open issues: none for the mathematical proof or requested declaration. Con-ron/NanoDa checks were not run in this session; the campaign's later independent checks remain external validation.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/H1C016/Main.lean` and four imported helper modules.
- Exact theorem: `AKLT.W.H1C016.main : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound`.
- All three gaps from the earlier partial attempt are closed.
- No residual propositions, additional mathematical hypotheses, or proved-leaf dependencies.
- Full task-module build and separate exact-type check passed.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- No frozen sources or files outside the assigned directories were modified.
- Independent Con-ron/NanoDa validation was not executed locally.
- Open mathematical names: none.
- Orchestrator action: run the standard independent checks and register this leaf if they pass.
