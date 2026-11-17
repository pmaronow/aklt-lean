module
public import AKLT.Blueprint.Mom.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM012

private lemma phi_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  dsimp [goldenRatio]
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

private lemma phi_pos : 0 < goldenRatio := by
  dsimp [goldenRatio]
  positivity

private lemma radius_pos : 0 < icoRadius := by
  apply Real.sqrt_pos.2
  linarith [phi_pos]

private lemma radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  change (Real.sqrt (goldenRatio + 2)) ^ 2 = goldenRatio + 2
  exact Real.sq_sqrt (by linarith [phi_pos])

private lemma normSq_add (x y : Vec3) :
    normSq (x + y) = normSq x + 2 * dot x y + normSq y := by
  unfold normSq dot
  calc
    (∑ i, (x i + y i) * (x i + y i)) =
        ∑ i, (x i * x i + 2 * (x i * y i) + y i * y i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, x i * x i) + 2 * (∑ i, x i * y i) + ∑ i, y i * y i := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp [Finset.mul_sum]

private lemma icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt radius_pos] <;>
    nlinarith [phi_sq, radius_sq]

private lemma icoVector_injective : Function.Injective icoVector := by
  intro j l h
  classical
  rcases j with ⟨a, b, c⟩
  rcases l with ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
    first
    | rfl
    | exfalso
      have h0 := congrArg (fun z : ℝ => z * icoRadius) (congrFun h 0)
      have h1 := congrArg (fun z : ℝ => z * icoRadius) (congrFun h 1)
      have h2 := congrArg (fun z : ℝ => z * icoRadius) (congrFun h 2)
      simp [icoVector, signValue, div_eq_mul_inv, ne_of_gt radius_pos] at h0 h1 h2
      <;> nlinarith [phi_sq, phi_pos, radius_pos]

private lemma normSq_nonneg' (v : Vec3) : 0 ≤ normSq v := by
  unfold normSq dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private lemma zero_dot_forces_neg (v b : Vec3)
    (hv : normSq v = 1) (hb : normSq b ≤ 1)
    (hz : 1 + dot v b = 0) : b = -v := by
  have hdot : dot v b = -1 := by linarith
  have hnonneg : 0 ≤ normSq (v + b) := normSq_nonneg' _
  have hexp := normSq_add v b
  have hbEq : normSq b = 1 := by nlinarith [hexp]
  have hzero : normSq (v + b) = 0 := by nlinarith [hexp]
  funext i
  have hle : (v i + b i) ^ 2 ≤ normSq (v + b) := by
    unfold normSq dot
    simpa [pow_two, Pi.add_apply] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun q : Fin 3 => (v q + b q) ^ 2)
        (fun q hq => sq_nonneg (v q + b q)) (Finset.mem_univ i))
  dsimp
  nlinarith [sq_nonneg (v i + b i)]

private def forbidden (b : Vec3) : Finset IcoLetter :=
  Finset.univ.filter fun j => 1 + dot (icoVector j) b = 0

private lemma forbidden_card_le_one (b : Vec3) (hb : normSq b ≤ 1) :
    (forbidden b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj l hl
  have hj0 : 1 + dot (icoVector j) b = 0 := (Finset.mem_filter.mp hj).2
  have hl0 : 1 + dot (icoVector l) b = 0 := (Finset.mem_filter.mp hl).2
  have hjneg : b = -icoVector j :=
    zero_dot_forces_neg (icoVector j) b (icoVector_normSq j) hb hj0
  have hlneg : b = -icoVector l :=
    zero_dot_forces_neg (icoVector l) b (icoVector_normSq l) hb hl0
  have hjeq : icoVector j = -b := by
    simpa using congrArg Neg.neg hjneg.symm
  have hleq : icoVector l = -b := by
    simpa using congrArg Neg.neg hlneg.symm
  exact icoVector_injective (hjeq.trans hleq.symm)

theorem main : AKLT.Blueprint.Mom.LetterAvoidanceStatement := by
  classical
  intro k hk b hb
  let bad : Fin k → Finset IcoLetter := fun i => forbidden (b i)
  let allBad : Finset IcoLetter := Finset.univ.biUnion bad
  have hbad_le : ∀ i, (bad i).card ≤ 1 := by
    intro i
    exact forbidden_card_le_one (b i) (hb i)
  have hsum : ∑ i : Fin k, (bad i).card ≤ k := by
    calc
      ∑ i : Fin k, (bad i).card ≤ ∑ _i : Fin k, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hbad_le i
      _ = k := by simp
  have hallBad : allBad.card ≤ k := by
    calc
      allBad.card ≤ ∑ i : Fin k, (bad i).card := Finset.card_biUnion_le
      _ ≤ k := hsum
  have hsmall : allBad.card < (Finset.univ : Finset IcoLetter).card := by
    rw [Finset.card_univ]
    norm_num [IcoLetter, Fintype.card_prod]
    omega
  have hgood : ∃ j : IcoLetter, j ∉ allBad := by
    by_contra h
    have hall : ∀ j : IcoLetter, j ∈ allBad := by simpa using h
    have huniv : (Finset.univ : Finset IcoLetter) ⊆ allBad := by
      intro j hj
      exact hall j
    have hcard : (Finset.univ : Finset IcoLetter).card ≤ allBad.card :=
      Finset.card_le_card huniv
    omega
  obtain ⟨j, hj⟩ := hgood
  refine ⟨j, ?_⟩
  intro i
  have hnot : j ∉ bad i := by
    intro hmem
    apply hj
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ i, hmem⟩
  have hne : 1 + dot (icoVector j) (b i) ≠ 0 := by
    intro hz
    apply hnot
    simp [bad, forbidden, hz]
  have hnonneg : 0 ≤ 1 + dot (icoVector j) (b i) := by
    have hexp := normSq_add (icoVector j) (b i)
    have hpos := normSq_nonneg' (icoVector j + b i)
    nlinarith [icoVector_normSq j, hb i]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end AKLT.W.MOM012

#print axioms AKLT.W.MOM012.main
