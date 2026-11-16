import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C016

open AKLT.Cert.H1 AKLT.Cert.H1.Production
open scoped BigOperators

def gaussianL1 (z : Gaussian) : Nat := z.re.natAbs + z.im.natAbs

@[simp] theorem gaussianL1_zero : gaussianL1 Gaussian.zero = 0 := by
  simp only [gaussianL1, Gaussian.zero, Int.natAbs_zero, Nat.zero_add]

@[simp] theorem gaussianL1_one : gaussianL1 Gaussian.one = 1 := by
  simp only [gaussianL1, Gaussian.one, Int.natAbs_one, Int.natAbs_zero, Nat.add_zero]

theorem gaussianL1_add_le (a b : Gaussian) :
    gaussianL1 (a.add b) ≤ gaussianL1 a + gaussianL1 b := by
  simp only [gaussianL1, Gaussian.add]
  calc
    _ ≤ (a.re.natAbs + b.re.natAbs) + (a.im.natAbs + b.im.natAbs) :=
      Nat.add_le_add (Int.natAbs_add_le _ _) (Int.natAbs_add_le _ _)
    _ = (a.re.natAbs + a.im.natAbs) + (b.re.natAbs + b.im.natAbs) := by omega

theorem gaussianL1_scale (n : Int) (a : Gaussian) :
    gaussianL1 (a.scale n) = n.natAbs * gaussianL1 a := by
  simp [gaussianL1, Gaussian.scale, Int.natAbs_mul, Nat.mul_add]

theorem gaussianL1_mul_le (a b : Gaussian) :
    gaussianL1 (a.mul b) ≤ gaussianL1 a * gaussianL1 b := by
  unfold Gaussian.mul
  split
  · simp only [gaussianL1_zero, Nat.zero_le]
  · calc
      _ ≤ (a.re * b.re).natAbs + (a.im * b.im).natAbs +
          ((a.re * b.im).natAbs + (a.im * b.re).natAbs) :=
        Nat.add_le_add (Int.natAbs_sub_le _ _) (Int.natAbs_add_le _ _)
      _ = gaussianL1 a * gaussianL1 b := by
        simp only [Int.natAbs_mul, gaussianL1]
        ring

theorem gaussianL1_sumGaussian_le (xs : List Gaussian) :
    gaussianL1 (sumGaussian xs) ≤ (xs.map gaussianL1).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      change gaussianL1 (x.add (sumGaussian xs)) ≤ gaussianL1 x + (xs.map gaussianL1).sum
      exact (gaussianL1_add_le x (sumGaussian xs)).trans
        (Nat.add_le_add_left ih (gaussianL1 x))

theorem sum_range_list {α : Type} [AddCommMonoid α] (n : Nat) (f : Nat → α) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  simpa only [List.toFinset_range] using (List.sum_toFinset f (List.nodup_range)).symm

theorem gaussianL1_sum_range (n : Nat) (f : Nat → Gaussian) :
    gaussianL1 (sumGaussian ((List.range n).map f)) ≤
      ∑ i ∈ Finset.range n, gaussianL1 (f i) := by
  simpa only [List.map_map, Function.comp_def, sum_range_list] using
    gaussianL1_sumGaussian_le ((List.range n).map f)

/-- Distinct lookups use disjoint leaves, even for a table with no shape check. -/
theorem table_sum_le (t : Table) (s : Finset Nat) :
    ∑ i ∈ s, gaussianL1 (t.get i) ≤ tableAbs t := by
  induction t generalizing s with
  | empty => simp only [Table.get, gaussianL1_zero, Finset.sum_const_zero, tableAbs, le_refl]
  | leaf z =>
      simp only [Table.get, beq_iff_eq]
      have he : (∑ i ∈ s, gaussianL1 (if i = 0 then z else Gaussian.zero)) =
          if 0 ∈ s then gaussianL1 z else 0 := by
        simp only [apply_ite gaussianL1, gaussianL1_zero, Finset.sum_ite_eq']
      rw [he]
      split <;> simp only [tableAbs, gaussianL1, le_refl, Nat.zero_le]
  | node cut l r hl hr =>
      let left := s.filter (· < cut)
      let right := s.filter (fun i => ¬ i < cut)
      have hinj : Set.InjOn (fun i => i - cut) (↑right : Set Nat) := by
        intro i hi j hj hij
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        change i - cut = j - cut at hij
        omega
      have hsplit : (∑ i ∈ s, gaussianL1 ((Table.node cut l r).get i)) =
          (∑ i ∈ left, gaussianL1 (l.get i)) +
          ∑ i ∈ right, gaussianL1 (r.get (i-cut)) := by
        rw [← Finset.sum_filter_add_sum_filter_not s (· < cut)]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_filter] at hi
          simp only [Table.get, ite_eq_left hi.2]
        · apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_filter] at hi
          simp only [Table.get, ite_eq_right hi.2]
      rw [hsplit]
      apply Nat.add_le_add (hl left)
      rw [← Finset.sum_image (f := fun k => gaussianL1 (r.get k)) hinj]
      exact hr _

def fourMass (a : FourMatrix) : Nat :=
  ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4, gaussianL1 (matrixEntry a i j)

theorem matrixEntry_tabulate (f : Nat → Nat → Gaussian) {i j : Nat}
    (hi : i < 4) (hj : j < 4) :
    matrixEntry ((List.range 4).map fun l => (List.range 4).map (f l)) i j = f i j := by
  simp only [matrixEntry, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some, List.getElem?_range hj]

theorem table_slice_le (t : Table) (dim : Nat) (hd : 0 < dim) (a b v : Nat) :
    (∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
      gaussianL1 (t.get (tableIndex dim a i j v b))) ≤ tableAbs t := by
  let indices := Finset.range 4 ×ˢ Finset.range 4
  let index : Nat × Nat → Nat := fun lr => tableIndex dim a lr.1 lr.2 v b
  have hinj : Set.InjOn index (↑indices : Set (Nat × Nat)) := by
    intro x hx y hy hxy
    rcases Finset.mem_product.mp hx with ⟨hx1,hx2⟩
    rcases Finset.mem_product.mp hy with ⟨hy1,hy2⟩
    simp only [Finset.mem_range] at hx1 hx2 hy1 hy2
    change ((((a*4+x.1)*4+x.2)*4+v)*dim+b) =
      ((((a*4+y.1)*4+y.2)*4+v)*dim+b) at hxy
    have h := Nat.eq_of_mul_eq_mul_right hd (Nat.add_right_cancel hxy)
    change ((a*4+x.1)*4+x.2)*4+v = ((a*4+y.1)*4+y.2)*4+v at h
    apply Prod.ext <;> omega
  calc
    _ = ∑ lr ∈ indices, gaussianL1 (t.get (index lr)) :=
      (Finset.sum_product (Finset.range 4) (Finset.range 4)
        (fun lr : Nat × Nat => gaussianL1 (t.get (index lr)))).symm
    _ = ∑ k ∈ indices.image index, gaussianL1 (t.get k) :=
      (Finset.sum_image (f := fun k => gaussianL1 (t.get k)) hinj).symm
    _ ≤ tableAbs t := table_sum_le _ _

theorem local_mass_le (s : SectorSite) (hd : 0 < s.base.spec.dim) (row col v : Nat) :
    fourMass (directSectorSiteMatrix s row col v) ≤ tableAbs s.base.table := by
  let a := s.coordinates.getD (row / s.stride % s.coordinates.length) 0
  let b := s.coordinates.getD (col / s.stride % s.coordinates.length) 0
  calc
    _ = ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4,
        gaussianL1 (s.base.table.get (tableIndex s.base.spec.dim a i j v b)) := by
      unfold fourMass
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg gaussianL1 (matrixEntry_tabulate (fun l r =>
        s.base.table.get (tableIndex s.base.spec.dim a l r v b))
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))
    _ ≤ tableAbs s.base.table := table_slice_le _ _ hd a b v

#print axioms gaussianL1_zero
#print axioms gaussianL1_one
#print axioms gaussianL1_add_le
#print axioms gaussianL1_scale
#print axioms gaussianL1_mul_le
#print axioms gaussianL1_sumGaussian_le
#print axioms sum_range_list
#print axioms gaussianL1_sum_range
#print axioms table_sum_le
#print axioms matrixEntry_tabulate
#print axioms table_slice_le
#print axioms local_mass_le

end AKLT.W.H1C016
