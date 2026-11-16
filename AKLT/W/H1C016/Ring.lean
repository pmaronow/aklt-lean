import AKLT.W.H1C016.Norms

namespace AKLT.W.H1C016

open AKLT.Cert.H1 AKLT.Cert.H1.Production
open scoped BigOperators

theorem matrixEntry_fourMul (a b : FourMatrix) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    matrixEntry (fourMul a b) i j = sumGaussian ((List.range 4).map fun k =>
      (matrixEntry a i k).mul (matrixEntry b k j)) :=
  matrixEntry_tabulate _ hi hj

theorem matrixEntry_fourIdentity_le {i j : Nat} (hi : i < 4) (hj : j < 4) :
    gaussianL1 (matrixEntry fourIdentity i j) ≤ 1 := by
  rw [show matrixEntry fourIdentity i j = (if i == j then Gaussian.one else Gaussian.zero)
    from matrixEntry_tabulate _ hi hj]
  split <;> simp only [gaussianL1_one, gaussianL1_zero, le_refl, Nat.zero_le]

theorem row_mass_le (a : FourMatrix) {i : Nat} (hi : i < 4) :
    (∑ k ∈ Finset.range 4, gaussianL1 (matrixEntry a i k)) ≤ fourMass a := by
  unfold fourMass
  exact Finset.single_le_sum (f := fun j =>
    ∑ k ∈ Finset.range 4, gaussianL1 (matrixEntry a j k))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

theorem matrixEntry_mul_le (a b : FourMatrix) (B : Nat)
    (hb : ∀ i < 4, ∀ j < 4, gaussianL1 (matrixEntry b i j) ≤ B)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    gaussianL1 (matrixEntry (fourMul a b) i j) ≤
      (∑ k ∈ Finset.range 4, gaussianL1 (matrixEntry a i k)) * B := by
  rw [matrixEntry_fourMul a b hi hj, Finset.sum_mul]
  apply (gaussianL1_sum_range _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  exact (gaussianL1_mul_le _ _).trans
    (Nat.mul_le_mul_left _ (hb k (Finset.mem_range.mp hk) j hj))

theorem trace_mul_le (a b : FourMatrix) (B : Nat)
    (hb : ∀ i < 4, ∀ j < 4, gaussianL1 (matrixEntry b i j) ≤ B) :
    gaussianL1 (fourTrace (fourMul a b)) ≤ fourMass a * B := by
  unfold fourTrace fourMass
  rw [Finset.sum_mul]
  apply (gaussianL1_sum_range _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  exact matrixEntry_mul_le a b B hb (Finset.mem_range.mp hi) (Finset.mem_range.mp hi)

theorem ring_entry_le (ss : List SectorSite)
    (hd : ∀ s ∈ ss, 0 < s.base.spec.dim) (row col : Nat) (codes : List Nat)
    {i j : Nat} (hi : i < 4) (hj : j < 4) :
    gaussianL1 (matrixEntry (directSectorRingProduct row col ss codes) i j) ≤
      (ss.map (fun s => tableAbs s.base.table)).prod := by
  induction ss generalizing codes i j with
  | nil => exact matrixEntry_fourIdentity_le hi hj
  | cons s ss ih =>
      simp only [directSectorRingProduct, List.map_cons, List.prod_cons]
      exact (matrixEntry_mul_le _ _ _ (fun k hk l hl =>
        ih (fun t ht => hd t (List.mem_cons_of_mem s ht)) codes.tail
          (i := k) (j := l) hk hl) hi hj).trans
        (Nat.mul_le_mul_right _ ((row_mass_le _ hi).trans
          (local_mass_le s (hd s List.mem_cons_self) row col (codes.headD 0))))

/-- A nonempty closed ring uses one total local mass and entry bounds for its tail. -/
theorem ring_value_le (ss : List SectorSite) (hn : ss ≠ [])
    (hd : ∀ s ∈ ss, 0 < s.base.spec.dim) (row col : Nat) (codes : List Nat) :
    gaussianL1 (directSectorRingValue ss row col codes) ≤
      (ss.map (fun s => tableAbs s.base.table)).prod := by
  cases ss with
  | nil => exact (hn rfl).elim
  | cons s ss =>
      simp only [directSectorRingValue, directSectorRingProduct, List.map_cons, List.prod_cons]
      exact (trace_mul_le _ _ _ (fun i hi j hj =>
        ring_entry_le ss (fun t ht => hd t (List.mem_cons_of_mem s ht))
          row col codes.tail (i := i) (j := j) hi hj)).trans
        (Nat.mul_le_mul_right _ (local_mass_le s (hd s List.mem_cons_self)
          row col (codes.headD 0)))

#print axioms matrixEntry_fourMul
#print axioms matrixEntry_fourIdentity_le
#print axioms row_mass_le
#print axioms matrixEntry_mul_le
#print axioms trace_mul_le
#print axioms ring_entry_le
#print axioms ring_value_le

end AKLT.W.H1C016
