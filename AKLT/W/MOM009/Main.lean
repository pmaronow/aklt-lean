module
public import AKLT.Blueprint.Mom.NodesCore

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM009

private theorem finiteFunctional_sum {α : Type} [Fintype α] (w : α → ℝ) (v : α → Vec3)
    {ι : Type} [Fintype ι] (f : ι → Vec3 → ℝ) :
    finiteFunctional w v (fun x => ∑ i, f i x) = ∑ i, finiteFunctional w v (f i) := by
  unfold finiteFunctional
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

private theorem finiteFunctional_const_mul {α : Type} [Fintype α] (w : α → ℝ) (v : α → Vec3)
    (r : ℝ) (f : Vec3 → ℝ) :
    finiteFunctional w v (fun x => r * f x) = r * finiteFunctional w v f := by
  unfold finiteFunctional
  calc
    (∑ a, w a * (r * f (v a))) = ∑ a, r * (w a * f (v a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = r * ∑ a, w a * f (v a) := by rw [← Finset.mul_sum]

private theorem finiteFunctional_rotated_prod {α : Type} [Fintype α] (w : α → ℝ) (v : α → Vec3)
    (R : Matrix (Fin 3) (Fin 3) ℝ) {n : ℕ} (idx : Fin n → Fin 3) :
    finiteFunctional w (fun a => R.mulVec (v a)) (fun z => ∏ t, z (idx t)) =
      ∑ b : Fin n → Fin 3, finiteFunctional w v
        (fun z => (∏ t, R (idx t) (b t)) * ∏ t, z (b t)) := by
  have pointwise (z : Vec3) :
      (∏ t, (R.mulVec z) (idx t)) =
        ∑ b : Fin n → Fin 3, (∏ t, R (idx t) (b t)) * ∏ t, z (b t) := by
    simp_rw [Matrix.mulVec_apply_eq_sum]
    rw [Fintype.prod_sum]
    simp_rw [Finset.prod_mul_distrib]
  unfold finiteFunctional
  simp_rw [pointwise, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem row_orthogonal (R : Matrix (Fin 3) (Fin 3) ℝ)
    (h : R.transpose * R = 1) (i j : Fin 3) :
    ∑ k, R i k * R j k = if i = j then 1 else 0 := by
  have h' : R * R.transpose = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 3) (Fin 3) ℝ
      (A := R.transpose) (B := R) (by rfl)).mp h
  have hh := congrFun (congrFun h' i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hh

private theorem sum_fin2 {β : Type} [AddCommMonoid β] (f : (Fin 2 → Fin 3) → β) :
    (∑ b : Fin 2 → Fin 3, f b) = ∑ i : Fin 3, ∑ j : Fin 3, f ![i, j] := by
  calc
    (∑ b : Fin 2 → Fin 3, f b) =
        ∑ p : Fin 3 × Fin 3, f ((finTwoArrowEquiv (Fin 3)).symm p) := by
      apply Fintype.sum_equiv (finTwoArrowEquiv (Fin 3)) f _
      intro b
      congr 1
      ext t
      fin_cases t <;> simp
    _ = ∑ i : Fin 3, ∑ j : Fin 3, f ![i, j] := by
      rw [Fintype.sum_prod_type]
      simp

private def finFourArrowEquiv : (Fin 4 → Fin 3) ≃ ((Fin 2 → Fin 3) × (Fin 2 → Fin 3)) where
  toFun b := (fun i => b (Fin.castAdd 2 i), fun i => b (Fin.natAdd 2 i))
  invFun p := Fin.addCases (m := 2) (n := 2) (motive := fun _ => Fin 3)
    (fun i => p.1 i) (fun i => p.2 i)
  left_inv b := by
    funext i
    fin_cases i <;> simp [Fin.addCases]
  right_inv p := by
    rcases p with ⟨p, q⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Fin.addCases]
    · funext i
      fin_cases i <;> simp [Fin.addCases]

private theorem finFourArrowEquiv_symm_tuple (i j k l : Fin 3) :
    finFourArrowEquiv.symm (![i, j], ![k, l]) = ![i, j, k, l] := by
  ext t
  fin_cases t <;> simp [finFourArrowEquiv, Fin.addCases]

private theorem sum_fin4 {β : Type} [AddCommMonoid β] (f : (Fin 4 → Fin 3) → β) :
    (∑ b : Fin 4 → Fin 3, f b) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, f ![i, j, k, l] := by
  calc
    (∑ b : Fin 4 → Fin 3, f b) =
        ∑ p : (Fin 2 → Fin 3) × (Fin 2 → Fin 3), f (finFourArrowEquiv.symm p) := by
      apply Fintype.sum_equiv finFourArrowEquiv f _
      intro b
      congr 1
      ext t
      fin_cases t <;> simp [finFourArrowEquiv, Fin.addCases]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, f ![i, j, k, l] := by
      rw [Fintype.sum_prod_type]
      simp_rw [sum_fin2]
      simp_rw [finFourArrowEquiv_symm_tuple]

private theorem contract_fin2 (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ i j : Fin 3, ∑ k, R i k * R j k = if i = j then 1 else 0)
    (i j : Fin 3) :
    (∑ b : Fin 2 → Fin 3, (R i (b 0) * R j (b 1)) *
      (if b 0 = b 1 then 1 else 0)) = if i = j then 1 else 0 := by
  rw [sum_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.isValue, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  exact hrow i j

private theorem contract_fin2_scaled (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ i j : Fin 3, ∑ k, R i k * R j k = if i = j then 1 else 0)
    (s : ℝ) (i j : Fin 3) :
    (∑ b : Fin 2 → Fin 3, (R i (b 0) * R j (b 1)) *
      (if b 0 = b 1 then s else 0)) = s * (if i = j then 1 else 0) := by
  simp_rw [show ∀ b : Fin 2 → Fin 3,
    (if b 0 = b 1 then s else 0) = s * (if b 0 = b 1 then 1 else 0) from
      fun b => by split_ifs <;> ring]
  calc
    (∑ b : Fin 2 → Fin 3, R i (b 0) * R j (b 1) *
        (s * (if b 0 = b 1 then 1 else 0))) =
      ∑ b : Fin 2 → Fin 3, s *
        (R i (b 0) * R j (b 1) * (if b 0 = b 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = s * ∑ b : Fin 2 → Fin 3,
        R i (b 0) * R j (b 1) * (if b 0 = b 1 then 1 else 0) := by
      exact (Finset.mul_sum Finset.univ
        (fun b : Fin 2 → Fin 3 => R i (b 0) * R j (b 1) *
          (if b 0 = b 1 then 1 else 0)) s).symm
    _ = s * (if i = j then 1 else 0) := by rw [contract_fin2 R hrow i j]

private theorem delta_and (a b c d : Fin 3) :
    (if a = b ∧ c = d then (1 : ℝ) else 0) =
      (if a = b then 1 else 0) * (if c = d then 1 else 0) := by
  by_cases hab : a = b <;> by_cases hcd : c = d <;> simp [hab, hcd]

private theorem contract_fin4_pair (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ i j : Fin 3, ∑ k, R i k * R j k = if i = j then 1 else 0)
    (i j k l : Fin 3) :
    (∑ b : Fin 4 → Fin 3,
      (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
        (if b 0 = b 1 ∧ b 2 = b 3 then 1 else 0)) =
      (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
  rw [sum_fin4]
  simp
  have hsum :
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        R i a * R j b * R k c * R l d * (if a = b ∧ c = d then 1 else 0)) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        R i a * R j b * R k c * R l d * ((if a = b then 1 else 0) * (if c = d then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    rw [delta_and]
  conv_lhs => change (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    R i a * R j b * R k c * R l d * (if a = b ∧ c = d then 1 else 0))
  rw [hsum]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_irrel]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
  calc
    (∑ x : Fin 3, ∑ y : Fin 3, R i x * R j x * R k y * R l y) =
        ∑ x : Fin 3, ∑ y : Fin 3, (R i x * R j x) * (R k y * R l y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = (∑ x : Fin 3, R i x * R j x) * (∑ y : Fin 3, R k y * R l y) := by
      rw [← Fintype.sum_mul_sum]
    _ = (if i = j then 1 else 0) * (if k = l then 1 else 0) := by
      rw [hrow, hrow]
    _ = if k = l then if i = j then 1 else 0 else 0 := by
      by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl]

private theorem contract_fin4_cross12 (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ i j : Fin 3, ∑ k, R i k * R j k = if i = j then 1 else 0)
    (i j k l : Fin 3) :
    (∑ b : Fin 4 → Fin 3,
      (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
        (if b 0 = b 2 ∧ b 1 = b 3 then 1 else 0)) =
      (if i = k then 1 else 0) * (if j = l then 1 else 0) := by
  rw [sum_fin4]
  simp
  have hsum :
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        R i a * R j b * R k c * R l d * (if a = c ∧ b = d then 1 else 0)) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        R i a * R j b * R k c * R l d * ((if a = c then 1 else 0) * (if b = d then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    rw [delta_and a c b d]
  conv_lhs => change (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    R i a * R j b * R k c * R l d * (if a = c ∧ b = d then 1 else 0))
  rw [hsum]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
  calc
    (∑ a : Fin 3, ∑ b : Fin 3, R i a * R j b * R k a * R l b) =
        ∑ a : Fin 3, ∑ b : Fin 3, (R i a * R k a) * (R j b * R l b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = (∑ a : Fin 3, R i a * R k a) * (∑ b : Fin 3, R j b * R l b) := by
      rw [← Fintype.sum_mul_sum]
    _ = (if i = k then 1 else 0) * (if j = l then 1 else 0) := by rw [hrow, hrow]
    _ = (if j = l then if i = k then 1 else 0 else 0) := by
      by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]

private theorem contract_fin4_cross13 (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hrow : ∀ i j : Fin 3, ∑ k, R i k * R j k = if i = j then 1 else 0)
    (i j k l : Fin 3) :
    (∑ b : Fin 4 → Fin 3,
      (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
        (if b 0 = b 3 ∧ b 1 = b 2 then 1 else 0)) =
      (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  rw [sum_fin4]
  simp
  have hsum :
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        R i a * R j b * R k c * R l d * (if a = d ∧ b = c then 1 else 0)) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        R i a * R j b * R k c * R l d * ((if a = d then 1 else 0) * (if b = c then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    rw [delta_and a d b c]
  conv_lhs => change (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    R i a * R j b * R k c * R l d * (if a = d ∧ b = c then 1 else 0))
  rw [hsum]
  simp_rw [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq, Finset.mem_univ]
  calc
    (∑ a : Fin 3, ∑ b : Fin 3, R i a * R j b * R k b * R l a) =
        ∑ a : Fin 3, ∑ b : Fin 3, (R i a * R l a) * (R j b * R k b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = (∑ a : Fin 3, R i a * R l a) * (∑ b : Fin 3, R j b * R k b) := by
      rw [← Fintype.sum_mul_sum]
    _ = (if i = l then 1 else 0) * (if j = k then 1 else 0) := by rw [hrow, hrow]
    _ = (if j = k then if i = l then 1 else 0 else 0) := by
      by_cases hil : i = l <;> by_cases hjk : j = k <;> simp [hil, hjk]

theorem main : AKLT.Blueprint.Mom.OrthogonalTensorStatement := by
  intro α inst w v c hLaw R hR
  rcases hLaw with ⟨hconst, hfirst, hthird, hsecond, hfourth⟩
  have hrow := row_orthogonal R hR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [finiteFunctional] using hconst
  · intro i
    have hp : (fun z : Vec3 => z i) =
        (fun z => ∏ t : Fin 1, z ((fun _ : Fin 1 => i) t)) := by
      funext z
      simp
    rw [hp]
    rw [finiteFunctional_rotated_prod w v R (fun _ : Fin 1 => i)]
    simp_rw [finiteFunctional_const_mul]
    simp [hfirst]
  · intro i j k
    have hp : (fun z : Vec3 => z i * z j * z k) =
        (fun z => ∏ t : Fin 3, z ((![i, j, k] : Fin 3 → Fin 3) t)) := by
      funext z
      simp [Fin.prod_univ_succ] <;> ring
    rw [hp]
    rw [finiteFunctional_rotated_prod w v R (![i, j, k])]
    simp_rw [finiteFunctional_const_mul]
    have hm (b : Fin 3 → Fin 3) :
        finiteFunctional w v (fun z => ∏ t : Fin 3, z (b t)) = 0 := by
      have hf : (fun z : Vec3 => ∏ t : Fin 3, z (b t)) =
          (fun z => z (b 0) * z (b 1) * z (b 2)) := by
        funext z
        simp [Fin.prod_univ_succ] <;> ring
      rw [hf, hthird]
    simp_rw [hm]
    simp
  · intro i j
    have hp : (fun z : Vec3 => z i * z j) =
        (fun z => ∏ t : Fin 2, z ((![i, j] : Fin 2 → Fin 3) t)) := by
      funext z
      simp [Fin.prod_univ_succ]
    rw [hp]
    rw [finiteFunctional_rotated_prod w v R (![i, j])]
    simp_rw [finiteFunctional_const_mul]
    have hm (b : Fin 2 → Fin 3) :
        finiteFunctional w v (fun z => ∏ t : Fin 2, z (b t)) =
          if b 0 = b 1 then c / 3 else 0 := by
      have hf : (fun z : Vec3 => ∏ t : Fin 2, z (b t)) =
          (fun z => z (b 0) * z (b 1)) := by
        funext z
        simp [Fin.prod_univ_succ]
      rw [hf, hsecond]
    simp_rw [show ∀ b : Fin 2 → Fin 3,
      finiteFunctional w v (fun z => ∏ t : Fin 2, z (b t)) =
        if b 0 = b 1 then c / 3 else 0 from fun b => by
          exact hm b]
    simpa using contract_fin2_scaled R hrow (c / 3) i j
  · intro i j k l
    have hp : (fun z : Vec3 => z i * z j * z k * z l) =
        (fun z => ∏ t : Fin 4, z ((![i, j, k, l] : Fin 4 → Fin 3) t)) := by
      funext z
      simp [Fin.prod_univ_succ] <;> ring
    rw [hp]
    rw [finiteFunctional_rotated_prod w v R (![i, j, k, l])]
    simp_rw [finiteFunctional_const_mul]
    have hm (b : Fin 4 → Fin 3) :
        finiteFunctional w v (fun z => ∏ t : Fin 4, z (b t)) =
          c * ((if b 0 = b 1 ∧ b 2 = b 3 then 1 else 0) +
            (if b 0 = b 2 ∧ b 1 = b 3 then 1 else 0) +
            (if b 0 = b 3 ∧ b 1 = b 2 then 1 else 0)) / 15 := by
      have hf : (fun z : Vec3 => ∏ t : Fin 4, z (b t)) =
          (fun z => z (b 0) * z (b 1) * z (b 2) * z (b 3)) := by
        funext z
        simp [Fin.prod_univ_succ] <;> ring
      rw [hf, hfourth]
    simp_rw [show ∀ b : Fin 4 → Fin 3,
      finiteFunctional w v (fun z => ∏ t : Fin 4, z (b t)) =
        c * ((if b 0 = b 1 ∧ b 2 = b 3 then 1 else 0) +
          (if b 0 = b 2 ∧ b 1 = b 3 then 1 else 0) +
          (if b 0 = b 3 ∧ b 1 = b 2 then 1 else 0)) / 15 from fun b => by
          exact hm b]
    have hcoef (b : Fin 4 → Fin 3) :
        (∏ t : Fin 4, R (![i, j, k, l] t) (b t)) =
          R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3) := by
      simp [Fin.prod_univ_succ] <;> ring
    simp_rw [hcoef]
    have hsum :
        (∑ b : Fin 4 → Fin 3,
          (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
            (c * ((if b 0 = b 1 ∧ b 2 = b 3 then 1 else 0) +
              (if b 0 = b 2 ∧ b 1 = b 3 then 1 else 0) +
              (if b 0 = b 3 ∧ b 1 = b 2 then 1 else 0)) / 15)) =
          (c / 15) * ((∑ b : Fin 4 → Fin 3,
            (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
              (if b 0 = b 1 ∧ b 2 = b 3 then 1 else 0)) +
            (∑ b : Fin 4 → Fin 3,
              (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 2 ∧ b 1 = b 3 then 1 else 0)) +
            (∑ b : Fin 4 → Fin 3,
              (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 3 ∧ b 1 = b 2 then 1 else 0))) := by
      calc
        _ = ∑ b : Fin 4 → Fin 3,
            ((c / 15) * ((R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 1 ∧ b 2 = b 3 then 1 else 0)) +
              (c / 15) * ((R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 2 ∧ b 1 = b 3 then 1 else 0)) +
              (c / 15) * ((R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 3 ∧ b 1 = b 2 then 1 else 0))) := by
          apply Finset.sum_congr rfl
          intro b hb
          ring
        _ = (c / 15) * ((∑ b : Fin 4 → Fin 3,
              (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 1 ∧ b 2 = b 3 then 1 else 0)) +
            (∑ b : Fin 4 → Fin 3,
              (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 2 ∧ b 1 = b 3 then 1 else 0)) +
            (∑ b : Fin 4 → Fin 3,
              (R i (b 0) * R j (b 1) * R k (b 2) * R l (b 3)) *
                (if b 0 = b 3 ∧ b 1 = b 2 then 1 else 0))) := by
          simp_rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
    rw [hsum, contract_fin4_pair R hrow i j k l,
      contract_fin4_cross12 R hrow i j k l, contract_fin4_cross13 R hrow i j k l]
    simp_rw [← delta_and]
    ring

end AKLT.W.MOM009
