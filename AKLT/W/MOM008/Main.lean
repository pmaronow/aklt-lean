import AKLT.Blueprint.Mom.NodesCore

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM008

theorem main : AKLT.Blueprint.Mom.TensorMonomialStatement := by
  classical
  intro L c hLaw m hm
  change L (fun v : Vec3 => ∏ i : Fin 3, v i ^ m i) = scaledMoment c m
  rcases hLaw with ⟨hConst, hOne, hThree, hTwo, hFour⟩
  have hThreeR : ∀ i j k : Fin 3, L (fun v => v i * (v j * v k)) = 0 := by
    intro i j k
    simpa [mul_assoc] using hThree i j k
  have hFourR : ∀ i j k l : Fin 3,
      L (fun v => v i * (v j * (v k * v l))) =
        c * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
          (if i = l ∧ j = k then 1 else 0)) / 15 := by
    intro i j k l
    simpa [mul_assoc] using hFour i j k l
  have hsum : m 0 + (m 1 + m 2) ≤ 4 := by
    simpa [Fin.sum_univ_succ] using hm
  have hb0 : m 0 ≤ 4 := by omega
  have hb1 : m 1 ≤ 4 := by omega
  have hb2 : m 2 ≤ 4 := by omega
  interval_cases h0 : m 0 <;>
    interval_cases h1 : m 1 <;>
    interval_cases h2 : m 2 <;>
    all_goals first
    | omega
    | have hmEq : m = (fun i : Fin 3 =>
          if i = 0 then m 0 else if i = 1 then m 1 else m 2) := by
        funext i
        fin_cases i <;> simp
      simp [h0, h1, h2] at hmEq
      subst m
      simp [scaledMoment, rationalMoment, Fin.sum_univ_three,
        Fin.prod_univ_three]
      norm_num [scaledMoment, rationalMoment, Fin.sum_univ_three]
      try simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      first
      | refine hConst.trans ?_
      | refine (hOne 0).trans ?_
      | refine (hOne 1).trans ?_
      | refine (hOne 2).trans ?_
      | refine (hTwo 0 0).trans ?_
      | refine (hTwo 1 1).trans ?_
      | refine (hTwo 2 2).trans ?_
      | refine (hTwo 0 1).trans ?_
      | refine (hTwo 0 2).trans ?_
      | refine (hTwo 1 2).trans ?_
      | refine (hThreeR 0 0 0).trans ?_
      | refine (hThreeR 1 1 1).trans ?_
      | refine (hThreeR 2 2 2).trans ?_
      | refine (hThreeR 0 0 1).trans ?_
      | refine (hThreeR 0 0 2).trans ?_
      | refine (hThreeR 0 1 1).trans ?_
      | refine (hThreeR 1 1 2).trans ?_
      | refine (hThreeR 0 2 2).trans ?_
      | refine (hThreeR 1 2 2).trans ?_
      | refine (hThreeR 0 1 2).trans ?_
      | refine (hFourR 0 0 0 0).trans ?_
      | refine (hFourR 1 1 1 1).trans ?_
      | refine (hFourR 2 2 2 2).trans ?_
      | refine (hFourR 0 0 0 1).trans ?_
      | refine (hFourR 0 0 0 2).trans ?_
      | refine (hFourR 0 1 1 1).trans ?_
      | refine (hFourR 1 1 1 2).trans ?_
      | refine (hFourR 0 2 2 2).trans ?_
      | refine (hFourR 1 2 2 2).trans ?_
      | refine (hFourR 0 0 1 1).trans ?_
      | refine (hFourR 0 0 2 2).trans ?_
      | refine (hFourR 1 1 2 2).trans ?_
      | refine (hFourR 0 0 1 2).trans ?_
      | refine (hFourR 0 1 1 2).trans ?_
      | refine (hFourR 0 1 2 2).trans ?_
      all_goals norm_num [scaledMoment, rationalMoment, Fin.sum_univ_three, Fin.exists_fin_succ, Fin.forall_fin_succ]
      all_goals ring

end AKLT.W.MOM008
