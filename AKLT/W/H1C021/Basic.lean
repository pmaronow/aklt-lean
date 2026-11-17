module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C021

private instance : LawfulBEq Gaussian where
  eq_of_beq := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    simp only [BEq.beq, instBEqGaussian.beq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  rfl := by intro z; cases z; simp [BEq.beq, instBEqGaussian.beq]

theorem list_sum_flatMap {α β M : Type*} [AddCommMonoid M]
    (xs : List α) (f : α → List β) (g : β → M) :
    ((xs.flatMap f).map g).sum =
      (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The literal Gaussian integer interpreted in the complex field. -/
def gaussianValue (z : Gaussian) : ℂ := (z.re : ℂ) + (z.im : ℂ) * Complex.I

@[simp] theorem gaussianValue_zero : gaussianValue .zero = 0 := by
  simp [gaussianValue, Gaussian.zero]

@[simp] theorem gaussianValue_one : gaussianValue .one = 1 := by
  simp [gaussianValue, Gaussian.one]

@[simp] theorem gaussianValue_add (z w : Gaussian) :
    gaussianValue (z.add w) = gaussianValue z + gaussianValue w := by
  simp only [gaussianValue, Gaussian.add, Int.cast_add]
  ring

@[simp] theorem gaussianValue_scale (k : ℤ) (z : Gaussian) :
    gaussianValue (z.scale k) = (k : ℂ) * gaussianValue z := by
  simp only [gaussianValue, Gaussian.scale, Int.cast_mul]
  ring

@[simp] theorem gaussianValue_mul (z w : Gaussian) :
    gaussianValue (z.mul w) = gaussianValue z * gaussianValue w := by
  unfold Gaussian.mul
  split
  · rename_i h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl <;> simp
  · simp only [gaussianValue, Int.cast_add, Int.cast_sub, Int.cast_mul]
    calc
      _ = (z.re : ℂ) * w.re - z.im * w.im +
          ((z.re : ℂ) * w.im + z.im * w.re) * Complex.I := rfl
      _ = _ := by ring_nf; simp only [Complex.I_sq]; ring

@[simp] theorem gaussianValue_sum (zs : List Gaussian) :
    gaussianValue (sumGaussian zs) = (zs.map gaussianValue).sum := by
  induction zs with
  | nil => simp [sumGaussian]
  | cons z zs ih => simp [sumGaussian, ih]

@[simp] theorem gaussianValue_re (z : Gaussian) :
    (gaussianValue z).re = (z.re : ℝ) := by
  simp [gaussianValue]

theorem pauliZ_value (a : Fin 4) (i j : Fin 2) :
    gaussianValue (pauliZ a.val i.val j.val) = pauli a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, gaussianValue, pauli]

/-- Integer coordinates of all four unnormalized two-spin basis vectors. -/
def pairCoeff (a : Nat) (i j : Fin 2) : ℤ :=
  if a = 0 then if i = 0 ∧ j = 0 then 1 else 0
  else if a = 1 then if i ≠ j then 1 else 0
  else if a = 2 then if i = 1 ∧ j = 1 then 1 else 0
  else if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0

theorem basisPair_sum (a : Nat) (f : Nat → Nat → ℂ) :
    ((basisPair a).map (fun (i,j,k) => (k : ℂ) * f i j)).sum =
      ∑ i : Fin 2, ∑ j : Fin 2, (pairCoeff a i j : ℂ) * f i.val j.val := by
  rcases a with _ | _ | _ | a <;>
    simp [basisPair, pairCoeff, Fin.sum_univ_two]

theorem pairForm_value (c e : Fin 4) (a b : Nat) :
    gaussianValue (pairForm c.val e.val a b) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
        (pairCoeff a i j : ℂ) * (pauli c i k * pauli e j l) *
          (pairCoeff b k l : ℂ) := by
  unfold pairForm
  rw [gaussianValue_sum, list_sum_flatMap]
  simp only [List.map_map, Function.comp_def,
    gaussianValue_scale, gaussianValue_mul, Int.cast_mul]
  have hinner (i j : Nat) (u : ℤ) :
      ((basisPair b).map (fun (k,l,v) =>
        ((u : ℂ) * v) *
          (gaussianValue (pauliZ c.val i k) * gaussianValue (pauliZ e.val j l)))).sum =
        (u : ℂ) * ∑ k : Fin 2, ∑ l : Fin 2,
          (pairCoeff b k l : ℂ) *
            (gaussianValue (pauliZ c.val i k.val) *
              gaussianValue (pauliZ e.val j l.val)) := by
    rw [show ((basisPair b).map (fun (k,l,v) => ((u : ℂ) * v) *
          (gaussianValue (pauliZ c.val i k) * gaussianValue (pauliZ e.val j l)))).sum =
        (u : ℂ) * ((basisPair b).map (fun (k,l,v) => (v : ℂ) *
          (gaussianValue (pauliZ c.val i k) * gaussianValue (pauliZ e.val j l)))).sum by
      simpa only [mul_assoc] using
        (List.sum_map_mul_left (basisPair b)
          (fun (k,l,v) => (v : ℂ) *
            (gaussianValue (pauliZ c.val i k) * gaussianValue (pauliZ e.val j l)))
          (u : ℂ))]
    exact congrArg (fun z : ℂ => (u : ℂ) * z)
      (basisPair_sum b (fun k l =>
        gaussianValue (pauliZ c.val i k) * gaussianValue (pauliZ e.val j l)))
  simp_rw [hinner]
  calc
    _ = ∑ i : Fin 2, ∑ j : Fin 2, (pairCoeff a i j : ℂ) *
        ∑ k : Fin 2, ∑ l : Fin 2, (pairCoeff b k l : ℂ) *
          (gaussianValue (pauliZ c.val i.val k.val) *
            gaussianValue (pauliZ e.val j.val l.val)) :=
      basisPair_sum a (fun i j => ∑ k : Fin 2, ∑ l : Fin 2,
        (pairCoeff b k l : ℂ) *
          (gaussianValue (pauliZ c.val i k.val) * gaussianValue (pauliZ e.val j l.val)))
    _ = _ := ?_
  simp_rw [pauliZ_value, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pair_basis_norms (a : Fin 4) :
    (∑ i : Fin 2, ∑ j : Fin 2, (pairCoeff a.val i j : ℤ)^2) =
      if a.val = 0 ∨ a.val = 2 then 1 else 2 := by
  simp only [Fin.sum_univ_two]
  fin_cases a <;> norm_num [pairCoeff]

private theorem radix_bound {a b n m : Nat} (ha : a < n) (hb : b < m) :
    a*m+b < n*m := by
  calc
    a*m+b < a*m+m := Nat.add_lt_add_left hb _
    _ = (a+1)*m := by rw [Nat.add_mul, one_mul]
    _ ≤ n*m := Nat.mul_le_mul_right m (by omega)

private theorem flatMap_range_length {α : Type*} (n m : Nat) (f : Nat → List α)
    (hf : ∀ i < n, (f i).length = m) :
    ((List.range n).flatMap f).length = n * m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
    rw [ih (fun i hi => hf i (by omega)), hf n (by omega)]
    simp only [Nat.succ_mul]

private theorem getD_flatMap_range {α : Type*} (n m : Nat) (f : Nat → List α)
    (hf : ∀ i < n, (f i).length = m) (d : α) (i j : Nat)
    (hi : i < n) (hj : j < m) :
    ((List.range n).flatMap f).getD (i*m+j) d = (f i).getD j d := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlen := flatMap_range_length n m f (fun k hk => hf k (by omega))
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact radix_bound hin hj)]
      exact ih (fun k hk => hf k (by omega)) hin
    · have hie : i = n := by omega
      subst i
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

theorem localTable_length (s : SiteSpec) :
    (localTable s).length = s.dim * (4 * (4 * (4 * s.dim))) := by
  unfold localTable
  apply flatMap_range_length
  intro a ha
  apply flatMap_range_length
  intro l hl
  apply flatMap_range_length
  intro r hr
  apply flatMap_range_length
  intro v hv
  simp

theorem localTable_getD (s : SiteSpec) (a l r v b : Nat)
    (ha : a < s.dim) (hl : l < 4) (hr : r < 4) (hv : v < 4) (hb : b < s.dim) :
    (localTable s).getD (tableIndex s.dim a l r v b) .zero =
      localEntry s a l r v b := by
  unfold localTable
  have hidx : tableIndex s.dim a l r v b =
      a*(4*(4*(4*s.dim))) + (l*(4*(4*s.dim)) + (r*(4*s.dim) + (v*s.dim+b))) := by
    unfold tableIndex
    ring
  have h1 := radix_bound hv hb
  have h2 := radix_bound hr h1
  have h3 := radix_bound hl h2
  rw [hidx]
  rw [getD_flatMap_range s.dim (4*(4*(4*s.dim))) _ (by
    intro i hi
    apply flatMap_range_length
    intro k hk
    apply flatMap_range_length
    intro q hq
    apply flatMap_range_length
    intro t ht
    simp) _ a _ ha h3]
  rw [getD_flatMap_range 4 (4*(4*s.dim)) _ (by
    intro i hi
    apply flatMap_range_length
    intro k hk
    apply flatMap_range_length
    intro t ht
    simp) _ l _ hl h2]
  rw [getD_flatMap_range 4 (4*s.dim) _ (by
    intro i hi
    apply flatMap_range_length
    intro t ht
    simp) _ r _ hr h1]
  rw [getD_flatMap_range 4 s.dim _ (by intro i hi; simp) _ v b hv hb]
  simp [hb]

theorem acceptedTable_entry (s : PackedSite) (ht : tableCheck s.spec s.table = true)
    (a l r v b : Nat) (ha : a < s.spec.dim) (hl : l < 4) (hr : r < 4)
    (hv : v < 4) (hb : b < s.spec.dim) :
    s.table.get (tableIndex s.spec.dim a l r v b) = localEntry s.spec a l r v b := by
  have h1 := radix_bound hv hb
  have h2 := radix_bound hr h1
  have h3 := radix_bound hl h2
  have h4 := radix_bound ha h3
  have hidx : tableIndex s.spec.dim a l r v b =
      a*(4*(4*(4*s.spec.dim))) +
        (l*(4*(4*s.spec.dim)) + (r*(4*s.spec.dim) + (v*s.spec.dim+b))) := by
    unfold tableIndex
    ring
  rw [tableCheck_sound ht _ (by rw [localTable_length, hidx]; exact h4)]
  exact localTable_getD s.spec a l r v b ha hl hr hv hb

end AKLT.W.H1C021
