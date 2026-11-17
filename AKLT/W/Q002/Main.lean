import AKLT.Blueprint.Q.NodesFrames

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q002

private def insertZero (i : Fin 3) : Fin 1 × Fin 3 := (0, i)

private theorem separateDegreeFour_rename
    (p : MvPolynomial (Fin 3) ℝ) (hp : DegreeFour p) :
    SeparateDegreeFour (MvPolynomial.rename insertZero p) := by
  intro m hm x
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  have hsum : (∑ k : Fin 3, m ((0 : Fin 1), k)) = m.sum (fun _ e => e) := by
    classical
    calc
      (∑ k : Fin 3, m ((0 : Fin 1), k)) =
          ∑ x : Fin 1, ∑ k : Fin 3, m (x, k) := by simp
      _ = m.sum (fun _ e => e) := by
        rw [Finsupp.sum_fintype, Fintype.sum_prod_type]
        simp
  rw [hsum]
  exact (MvPolynomial.le_totalDegree hm).trans
    ((MvPolynomial.totalDegree_rename_le insertZero p).trans hp)

private theorem productFunctional_one_site
    (f : (Fin 1 → Vec3) → ℝ) :
    productFunctional (fun _ : Fin 1 => Status.U) f =
      ∑ s : SpinLetter, spinWeight Status.U s * f (fun _ : Fin 1 => spinVector s) := by
  classical
  letI : DecidableEq (Fin 1) := Classical.decEq _
  unfold productFunctional
  let e : (Fin 1 → SpinLetter) ≃ SpinLetter := Equiv.funUnique (Fin 1) SpinLetter
  calc
    _ = ∑ s : SpinLetter,
        (∏ x : Fin 1, spinWeight Status.U ((e.symm s) x)) *
          f (fun x : Fin 1 => spinVector ((e.symm s) x)) := by
            exact Fintype.sum_equiv e
              (fun n => (∏ x : Fin 1, spinWeight Status.U (n x)) *
                f (fun x : Fin 1 => spinVector (n x)))
              (fun s => (∏ x : Fin 1, spinWeight Status.U ((e.symm s) x)) *
                f (fun x : Fin 1 => spinVector ((e.symm s) x)))
              (by
                intro n
                have hn : n = fun _ : Fin 1 => n 0 := by
                  funext x
                  congr 1
                  exact Subsingleton.elim x 0
                rw [hn]
                simp [e])
    _ = ∑ s : SpinLetter, spinWeight Status.U s *
          f (fun _ : Fin 1 => spinVector s) := by
            simp [e]

private theorem productFunctional_U_eval
    (f : Vec3 → ℝ) :
    productFunctional (fun _ : Fin 1 => Status.U) (fun a => f (a 0)) = moment f := by
  rw [productFunctional_one_site]
  simp [moment, spinWeight, spinVector, ← Finset.mul_sum]

theorem main : AKLT.Blueprint.Q.OneSiteMomentEncodingStatement := by
  intro p hp
  let q : MvPolynomial (Fin 1 × Fin 3) ℝ := MvPolynomial.rename insertZero p
  have hqdeg : SeparateDegreeFour q := by
    exact separateDegreeFour_rename p hp
  refine ⟨q, hqdeg, ?_, ?_⟩
  · have heval : ∀ a : Fin 1 → Vec3,
        MvPolynomial.eval (fun v : Fin 1 × Fin 3 => a v.1 v.2) q =
          MvPolynomial.eval (a 0) p := by
      intro a
      change MvPolynomial.eval (fun v : Fin 1 × Fin 3 => a v.1 v.2)
          (MvPolynomial.rename insertZero p) = _
      rw [MvPolynomial.eval_rename]
      congr 1
    calc
      productFunctional (fun _ : Fin 1 => Status.U)
          (fun a => MvPolynomial.eval (fun v => a v.1 v.2) q) =
          productFunctional (fun _ : Fin 1 => Status.U)
            (fun a => MvPolynomial.eval (a 0) p) := by
              congr 1
              funext a
              exact heval a
      _ = moment (fun a => MvPolynomial.eval a p) :=
        productFunctional_U_eval (fun a => MvPolynomial.eval a p)
  · intro R
    have heval : ∀ a : Fin 1 → Vec3,
        MvPolynomial.eval
            (fun v : Fin 1 × Fin 3 => (R.mulVec (a v.1)) v.2) q =
          MvPolynomial.eval (R.mulVec (a 0)) p := by
      intro a
      change MvPolynomial.eval
          (fun v : Fin 1 × Fin 3 => (R.mulVec (a v.1)) v.2)
          (MvPolynomial.rename insertZero p) = _
      rw [MvPolynomial.eval_rename]
      congr 1
    calc
      productFunctional (fun _ : Fin 1 => Status.U)
          (fun a => MvPolynomial.eval
            (fun v => (R.mulVec (a v.1)) v.2) q) =
          productFunctional (fun _ : Fin 1 => Status.U)
            (fun a => MvPolynomial.eval (R.mulVec (a 0)) p) := by
              congr 1
              funext a
              exact heval a
      _ = moment (fun a => MvPolynomial.eval (R.mulVec a) p) :=
        productFunctional_U_eval (fun a => MvPolynomial.eval (R.mulVec a) p)

end AKLT.W.Q002

#print axioms AKLT.W.Q002.main
