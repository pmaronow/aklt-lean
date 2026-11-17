module
public import AKLT.Blueprint.Q.NodesTight

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

namespace AKLT.W.Q009

private theorem product_degree_bound (p q r : MvPolynomial (Fin 3) ℂ)
    (a b c : ℕ) (hp : p.totalDegree ≤ 1) (hq : q.totalDegree ≤ 1)
    (hr : r.totalDegree ≤ 1) :
    (MvPolynomial.C (1 / 16 : ℂ) * p ^ a * q ^ b * r ^ c).totalDegree ≤ a + b + c := by
  let K : MvPolynomial (Fin 3) ℂ := MvPolynomial.C (1 / 16 : ℂ)
  have hK : K.totalDegree = 0 := by simp [K]
  have hpa : (p ^ a).totalDegree ≤ a := by
    calc
      _ ≤ a * p.totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ a := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left a hp
  have hqb : (q ^ b).totalDegree ≤ b := by
    calc
      _ ≤ b * q.totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ b := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hq
  have hrc : (r ^ c).totalDegree ≤ c := by
    calc
      _ ≤ c * r.totalDegree := MvPolynomial.totalDegree_pow _ _
      _ ≤ c := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left c hr
  change (K * p ^ a * q ^ b * r ^ c).totalDegree ≤ a + b + c
  calc
    _ ≤ (K * p ^ a * q ^ b).totalDegree + (r ^ c).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ ((K * p ^ a).totalDegree + (q ^ b).totalDegree) + (r ^ c).totalDegree :=
      Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
    _ ≤ ((K.totalDegree + (p ^ a).totalDegree) + (q ^ b).totalDegree) + (r ^ c).totalDegree :=
      Nat.add_le_add_right (Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _) _
    _ ≤ ((0 + a) + b) + c := by rw [hK]; omega
    _ = a + b + c := by omega

theorem main : AKLT.Blueprint.Q.QuarticKernelDegreeStatement := by
  classical
  intro j k
  by_cases hjk : j ≤ k
  · have hjkv : j.val ≤ k.val := Fin.le_iff_val_le_val.mp hjk
    have hsum : (4 - k.val) + j.val + (k.val - j.val) = 4 := by omega
    simp only [AKLT.Blueprint.Q.quarticKernel, if_pos hjk]
    let X : Fin 3 → MvPolynomial (Fin 3) ℂ := MvPolynomial.X
    have hplus : (1 + X 2).totalDegree ≤ 1 := by
      calc
        _ ≤ max (1 : MvPolynomial (Fin 3) ℂ).totalDegree (X 2).totalDegree :=
          MvPolynomial.totalDegree_add _ _
        _ = 1 := by simp [X]
    have hminus : (1 - X 2).totalDegree ≤ 1 := by
      calc
        _ ≤ max (1 : MvPolynomial (Fin 3) ℂ).totalDegree (X 2).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
        _ = 1 := by simp [X]
    have hlin : (X 0 + MvPolynomial.C Complex.I * X 1).totalDegree ≤ 1 := by
      have hprod : (MvPolynomial.C Complex.I * X 1).totalDegree ≤ 1 := by
        calc
          _ ≤ (MvPolynomial.C Complex.I).totalDegree + (X 1).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ = 1 := by simp [X]
      calc
        _ ≤ max (X 0).totalDegree (MvPolynomial.C Complex.I * X 1).totalDegree :=
          MvPolynomial.totalDegree_add _ _
        _ ≤ max 1 1 := max_le_max (by simp [X]) hprod
        _ = 1 := by simp
    calc
      _ ≤ (4 - k.val) + j.val + (k.val - j.val) :=
        product_degree_bound (1 + X 2) (1 - X 2)
          (X 0 + MvPolynomial.C Complex.I * X 1)
          (4 - k.val) j.val (k.val - j.val) hplus hminus hlin
      _ = 4 := hsum
  · have hkj : k.val < j.val := by
      have hnot : ¬ j.val ≤ k.val := by
        intro hv
        exact hjk (Fin.le_iff_val_le_val.mpr hv)
      omega
    have hsum : (4 - j.val) + k.val + (j.val - k.val) = 4 := by omega
    simp only [AKLT.Blueprint.Q.quarticKernel, if_neg hjk]
    let X : Fin 3 → MvPolynomial (Fin 3) ℂ := MvPolynomial.X
    have hplus : (1 + X 2).totalDegree ≤ 1 := by
      calc
        _ ≤ max (1 : MvPolynomial (Fin 3) ℂ).totalDegree (X 2).totalDegree :=
          MvPolynomial.totalDegree_add _ _
        _ = 1 := by simp [X]
    have hminus : (1 - X 2).totalDegree ≤ 1 := by
      calc
        _ ≤ max (1 : MvPolynomial (Fin 3) ℂ).totalDegree (X 2).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
        _ = 1 := by simp [X]
    have hlin : (X 0 - MvPolynomial.C Complex.I * X 1).totalDegree ≤ 1 := by
      have hprod : (MvPolynomial.C Complex.I * X 1).totalDegree ≤ 1 := by
        calc
          _ ≤ (MvPolynomial.C Complex.I).totalDegree + (X 1).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ = 1 := by simp [X]
      calc
        _ ≤ max (X 0).totalDegree (MvPolynomial.C Complex.I * X 1).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
        _ ≤ max 1 1 := max_le_max (by simp [X]) hprod
        _ = 1 := by simp
    calc
      _ ≤ (4 - j.val) + k.val + (j.val - k.val) :=
        product_degree_bound (1 + X 2) (1 - X 2)
          (X 0 - MvPolynomial.C Complex.I * X 1)
          (4 - j.val) k.val (j.val - k.val) hplus hminus hlin
      _ = 4 := hsum

end AKLT.W.Q009
