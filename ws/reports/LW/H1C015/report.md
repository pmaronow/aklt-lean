STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C015/AKLT/W/H1C015/Main.lean): the exact requested theorem and all 41 theorem axiom audits.
- [Algebra.lean](/home/ubuntu/aklt/wt/LW_H1C015/AKLT/W/H1C015/Algebra.lean): faithful Gaussian integer embedding, finite sums, matrix entries, and Horner evaluation.
- [Expansion.lean](/home/ubuntu/aklt/wt/LW_H1C015/AKLT/W/H1C015/Expansion.lean): accepted strides, column periodicity, mixed-radix reindexing, and ring-product/trace expansion.
- [Linearity.lean](/home/ubuntu/aklt/wt/LW_H1C015/AKLT/W/H1C015/Linearity.lean): distribution through centre sums, filtering, and the threshold combination.

The import chain is `Main → Linearity → Expansion → Algebra`. Every Lean file in the task directory is transitively imported by Main. The previous partial Main was replaced; source files outside this task directory were not edited. The prior report remains in `report.luna.md`.

## Result and proof

```lean
theorem AKLT.W.H1C015.main :
    AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion
```

The proof establishes the more general `threshold_expansion` for every sector list satisfying the recursively defined `Strides` predicate. `strides_of_check` proves that predicate from the sector-layout checker, so no residual hypothesis is needed in `main`. No proved blueprint leaf is imported or used.

`value : Gaussian → Zsqrtd (-1)` preserves both integer components and is injective. It turns Gaussian addition, scaling, multiplication, and list summation into ordinary ring operations. Local Horner packs expand into weighted column sums. The product induction reindexes each column as `a * lanes tail + b`; `digit_block` proves the head coordinate, and `direct_product_period` proves equality of the tail inputs before rewriting the product. Taking the trace and distributing the centre colour sums and centre-pair filters gives the full threshold identity. This proves polynomial evaluation directly, with no signed-digit extraction or coefficient-bound assumption.

The argument permits empty coordinate lists and arbitrary width; it needs only the checked strides. It uses symbolic list/Finset identities and named index lemmas, without evaluating a concrete certificate or enumerating a concrete matrix.

## Exported declarations and statements

All supporting names below are in namespace `AKLT.W.H1C015`. The auxiliary definitions are:

```lean
abbrev R := Zsqrtd (-1)
def value (a : Gaussian) : R := ⟨a.re, a.im⟩
def entry (m : FourMatrix) (i j : Nat) : R := value (matrixEntry m i j)
def weight (width col : Nat) : R := (2 : R) ^ (width*col)
def lanes (ss : List SectorSite) : Nat :=
  (ss.map fun s => s.coordinates.length).prod
def Strides : List SectorSite → Prop
  | [] => True
  | s :: ss => s.stride = lanes ss ∧ Strides ss
def coefficient (s : SectorSite) (row digit v i j : Nat) : R :=
  value (s.base.table.get (tableIndex s.base.spec.dim
    (s.coordinates.getD (row / s.stride % s.coordinates.length) 0) i j v
    (s.coordinates.getD digit 0)))
def Expands (width n : Nat) (packed : Gaussian) (direct : Nat → Gaussian) : Prop :=
  value packed = ∑ col ∈ Finset.range n, value (direct col) * weight width col
def packedCurrentNext (ss : List SectorSite) (out row width : Nat) (next : Bool) : Gaussian :=
  ((sectorRingValue ss row width []).scale (if next then 5 else 3)).add
    (sumGaussian ((centerPairs (ss.map fun s => s.base)).filterMap fun (x,y) =>
      if next && (x == out || y == out) then none else
        some (sumGaussian ((List.range 3).map fun k =>
          sectorRingValue ss row width (centerCodes ss.length x y (k+1))))))
```

The complete theorem signatures follow, with proofs omitted from this inventory.

### Algebra.lean

```lean
theorem value_injective : Function.Injective value

@[simp] theorem value_zero : value Gaussian.zero = 0

@[simp] theorem value_one : value Gaussian.one = 1

@[simp] theorem value_add (a b : Gaussian) : value (a.add b) = value a + value b

@[simp] theorem value_scale (n : Int) (a : Gaussian) :
    value (a.scale n) = (n : R) * value a

lemma gaussian_beq_zero_eq (a : Gaussian) (h : a == Gaussian.zero) : a = Gaussian.zero

lemma gaussian_mul_raw (a b : Gaussian) :
    a.mul b = ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

@[simp] theorem value_mul (a b : Gaussian) : value (a.mul b) = value a * value b

@[simp] theorem value_sum (xs : List Gaussian) :
    value (sumGaussian xs) = (xs.map value).sum

theorem sum_list_range {S : Type*} [AddCommMonoid S] (n : Nat) (f : Nat → S) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i

@[simp] theorem value_sum_range (n : Nat) (f : Nat → Gaussian) :
    value (sumGaussian ((List.range n).map f)) =
      ∑ i ∈ Finset.range n, value (f i)

theorem sum_blocks {S : Type*} [AddCommMonoid S] (m n : Nat) (f : Nat → S) :
    (∑ c ∈ Finset.range (m*n), f c) =
      ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, f (a*n+b)

theorem getD_map_range {S : Type*} (n : Nat) (f : Nat → S) (d : S)
    (i : Nat) (hi : i < n) : ((List.range n).map f).getD i d = f i

theorem matrixEntry_map (f : Nat → Nat → Gaussian) (i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    matrixEntry ((List.range 4).map fun l => (List.range 4).map (f l)) i j = f i j

theorem entry_mul (a b : FourMatrix) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    entry (fourMul a b) i j =
      ∑ k ∈ Finset.range 4, entry a i k * entry b k j

@[simp] theorem value_trace (m : FourMatrix) :
    value (fourTrace m) = ∑ i ∈ Finset.range 4, entry m i i

@[simp] theorem weight_zero (width : Nat) : weight width 0 = 1

theorem weight_add (width a b : Nat) :
    weight width (a+b) = weight width a * weight width b

theorem weight_pow (width stride digit : Nat) :
    (weight width stride)^digit = weight width (digit*stride)

theorem value_pack_map {S : Type*} (base : Int) (xs : List S) (f : S → Gaussian)
    (d : S) :
    value (packGaussian base (xs.map f)) =
      ∑ i ∈ Finset.range xs.length, value (f (xs.getD i d)) * (base : R)^i
```

### Expansion.lean

```lean
@[simp] theorem lanes_nil : lanes [] = 1

@[simp] theorem lanes_cons (s : SectorSite) (ss : List SectorSite) :
    lanes (s :: ss) = s.coordinates.length * lanes ss

theorem strides_of_indexed (ss : List SectorSite)
    (h : ∀ (i : Nat) (hi : i < ss.length), ss[i].stride = lanes (ss.drop (i+1))) :
    Strides ss

theorem strides_of_check (base : List PackedSite) (parity : Nat) (ss : List SectorSite)
    (h : sectorNetworkCheck base parity ss = true) : Strides ss

theorem digit_period (a m n c : Nat) :
    (a*(m*n)+c) / n % m = c / n % m

theorem direct_product_period : ∀ (ss : List SectorSite), Strides ss →
    ∀ (row a col : Nat) (codes : List Nat),
    directSectorRingProduct row (a*lanes ss+col) ss codes =
      directSectorRingProduct row col ss codes

theorem entry_direct_site (s : SectorSite) (row col v i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    entry (directSectorSiteMatrix s row col v) i j =
      coefficient s row (col / s.stride % s.coordinates.length) v i j

theorem entry_packed_site (s : SectorSite) (row v width i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    entry (sectorSiteMatrix s row v width) i j =
      ∑ digit ∈ Finset.range s.coordinates.length,
        coefficient s row digit v i j * weight width (digit*s.stride)

theorem digit_block (a m n b : Nat) (ha : a < m) (hb : b < n) :
    (a*n+b) / n % m = a

theorem product_expansion : ∀ (ss : List SectorSite), Strides ss →
    ∀ (row width : Nat) (codes : List Nat) (i j : Nat), i < 4 → j < 4 →
    entry (sectorRingProduct row width ss codes) i j =
      ∑ col ∈ Finset.range (lanes ss),
        entry (directSectorRingProduct row col ss codes) i j * weight width col

theorem ring_expansion (ss : List SectorSite) (h : Strides ss)
    (row width : Nat) (codes : List Nat) :
    value (sectorRingValue ss row width codes) =
      ∑ col ∈ Finset.range (lanes ss),
        value (directSectorRingValue ss row col codes) * weight width col
```

### Linearity.lean

```lean
theorem expands_zero (width n : Nat) :
    Expands width n Gaussian.zero (fun _ => Gaussian.zero)

theorem expands_add (width n : Nat) (a b : Gaussian) (f g : Nat → Gaussian)
    (ha : Expands width n a f) (hb : Expands width n b g) :
    Expands width n (a.add b) (fun col => (f col).add (g col))

theorem expands_scale (width n : Nat) (a : Gaussian) (f : Nat → Gaussian) (z : Int)
    (ha : Expands width n a f) :
    Expands width n (a.scale z) (fun col => (f col).scale z)

theorem expands_sum {S : Type*} (width n : Nat) (xs : List S)
    (a : S → Gaussian) (f : S → Nat → Gaussian)
    (h : ∀ x ∈ xs, Expands width n (a x) (f x)) :
    Expands width n (sumGaussian (xs.map a))
      (fun col => sumGaussian (xs.map fun x => f x col))

theorem expands_filterMap {S : Type*} (width n : Nat) (xs : List S)
    (skip : S → Bool) (a : S → Gaussian) (f : S → Nat → Gaussian)
    (h : ∀ x ∈ xs, Expands width n (a x) (f x)) :
    Expands width n
      (sumGaussian (xs.filterMap fun x => if skip x then none else some (a x)))
      (fun col => sumGaussian (xs.filterMap fun x =>
        if skip x then none else some (f x col)))

theorem current_expansion (ss : List SectorSite) (h : Strides ss)
    (out row width : Nat) (next : Bool) :
    Expands width (lanes ss) (packedCurrentNext ss out row width next)
      (fun col => directSectorCurrentNext ss out row col next)

theorem filter_center_terms (xs : List (Nat × Nat)) (f : Nat → Nat → Gaussian) (out : Nat) :
    ((xs.map fun (x,y) => (x,y,f x y)).filterMap fun (x,y,c) =>
      if x != out && y != out then some c else none) =
    xs.filterMap (fun (x,y) => if x == out || y == out then none else some (f x y))

theorem packed_threshold_eq (ss : List SectorSite) (out row width p q : Nat) :
    packedSectorThresholdRow ss out row width p q =
      ((packedCurrentNext ss out row width false).scale (5*q)).add
        ((packedCurrentNext ss out row width true).scale (-(3*(p : Int))))

theorem threshold_expansion (ss : List SectorSite) (h : Strides ss)
    (out row width p q : Nat) :
    packedSectorThresholdRow ss out row width p q =
      sumGaussian ((List.range (lanes ss)).map fun col =>
        (directSectorThreshold ss out p q row col).scale
          ((2 : Nat)^(width*col) : Int))
```

### Main.lean

```lean
theorem main : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion
```

## Axiom audit

`Main.lean` executes `#print axioms` for every exported theorem. The complete output is:

```text
'AKLT.W.H1C015.value_injective' does not depend on any axioms
'AKLT.W.H1C015.value_zero' does not depend on any axioms
'AKLT.W.H1C015.value_one' does not depend on any axioms
'AKLT.W.H1C015.value_add' does not depend on any axioms
'AKLT.W.H1C015.value_scale' depends on axioms: [propext]
'AKLT.W.H1C015.gaussian_beq_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.gaussian_mul_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.value_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.value_sum' depends on axioms: [propext]
'AKLT.W.H1C015.sum_list_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.value_sum_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.sum_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.getD_map_range' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.matrixEntry_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.entry_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.value_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.weight_zero' depends on axioms: [propext]
'AKLT.W.H1C015.weight_add' depends on axioms: [propext]
'AKLT.W.H1C015.weight_pow' depends on axioms: [propext]
'AKLT.W.H1C015.value_pack_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.lanes_nil' does not depend on any axioms
'AKLT.W.H1C015.lanes_cons' does not depend on any axioms
'AKLT.W.H1C015.strides_of_indexed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.strides_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.digit_period' depends on axioms: [propext]
'AKLT.W.H1C015.direct_product_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.entry_direct_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.entry_packed_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.digit_block' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C015.product_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.ring_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.expands_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.expands_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.expands_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.expands_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.expands_filterMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.current_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.filter_center_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.packed_threshold_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.threshold_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C015.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every audit is a subset of the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Validation

Run from `/home/ubuntu/aklt/wt/LW_H1C015`, with the existing elan toolchain on PATH:

```sh
/usr/bin/time -f 'ELAPSED_SECONDS=%e' lake build AKLT.W.H1C015.Main
```

Passed. Successful final build: **39.15 s** wall time, including Lake dependency replay, Linearity compilation (12 s), and Main compilation plus all audits (13 s). Algebra and Expansion had already compiled successfully in 5.3 s and 6.0 s respectively. No Mathlib build or package update was run. Replayed warnings came from existing upstream modules; the delivered modules have no warnings.

A separate file `/tmp/H1C015-ExactType.lean` contained:

```lean
import AKLT.W.H1C015.Main

example : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion :=
  AKLT.W.H1C015.main

#check (AKLT.W.H1C015.main : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion)
#print axioms AKLT.W.H1C015.main
```

`lake env lean /tmp/H1C015-ExactType.lean` passed in **15.97 s**. Output:

```text
AKLT.W.H1C015.main : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion
'AKLT.W.H1C015.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A source scan found no forbidden proof constructs. There are no residual statements or open mathematical issues. Lean kernel compilation and the separate exact-type check were run; con-ron/NanoDa replay remains for the campaign checker.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered exact theorem `AKLT.W.H1C015.main : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion`.
- Main imports all three helper modules; no extra task-directory files remain.
- General identity: `AKLT.W.H1C015.threshold_expansion`, under the proved layout predicate `Strides`.
- Both Gaussian components are preserved by an injective embedding into `Zsqrtd (-1)`.
- Mixed-radix input equalities are proved before rewriting matrix products.
- Centre sums and filtering are fully distributed; no digit extraction is used.
- No dependency on another blueprint leaf; no residual assumptions or open leaves.
- All 41 theorem axiom audits contain only permitted axioms.
- `lake build AKLT.W.H1C015.Main` passed (39.15 s final wall time).
- Separate import/exact-type check passed (15.97 s).
- Existing source outside the assigned directory was not edited.
- Limitation: independent con-ron/NanoDa replay was not run here.
- Orchestrator: run the standard independent campaign checks and accept the leaf if they pass.
