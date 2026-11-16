import AKLT.Blueprint.Q.NodesEnergy
import AKLT.Uniq.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q053

private noncomputable def fibreUpdateMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, DecidableEq (S x)]
    (x : ι) (σ : (y : ι) → S y) (f : ((y : ι) → S y) → ℝ) :
    ℝ := by
  classical
  exact ∑ τ, if AKLT.Blueprint.Q.fullFibreEvent x σ τ then f τ else 0

private noncomputable def fibreUpdatePointMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, DecidableEq (S x)]
    (x : ι) (σ : (y : ι) → S y) (a : S x) (f : ((y : ι) → S y) → ℝ) : ℝ := by
  classical
  exact ∑ τ, if AKLT.Blueprint.Q.fullFibreEvent x σ τ ∧ τ x = a then f τ else 0

private theorem sum_fibre_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, DecidableEq (S x)]
    (x : ι) (σ : (y : ι) → S y) (f : ((y : ι) → S y) → ℝ) :
    fibreUpdateMass x σ f = ∑ a : S x, f (Function.update σ x a) := by
  classical
  let E : ((y : ι) → S y) → Prop := AKLT.Blueprint.Q.fullFibreEvent x σ
  let e : S x ≃ {τ // E τ} :=
    { toFun := fun a => ⟨Function.update σ x a, by
        intro y hy
        change Function.update σ x a y = σ y
        rw [Function.update_of_ne hy]⟩
      invFun := fun τ => τ.1 x
      left_inv := by intro a; simp
      right_inv := by
        intro τ
        apply Subtype.ext
        funext y
        by_cases hy : y = x
        · subst y
          simp
        · change Function.update σ x (τ.1 x) y = τ.1 y
          rw [Function.update_of_ne hy]
          exact (τ.2 y hy).symm }
  calc
    fibreUpdateMass x σ f = ∑ τ ∈ Finset.univ.filter E, f τ := by
      simp [fibreUpdateMass, E, ← Finset.sum_filter]
    _ = ∑ τ : {τ // E τ}, f τ.1 := by
      exact Finset.sum_subtype (Finset.univ.filter E) (by intro τ; simp) f
    _ = ∑ a : S x, f (Function.update σ x a) := by
      symm
      exact Fintype.sum_equiv e (fun a : S x => f (Function.update σ x a))
        (fun τ : {τ // E τ} => f τ.1) (by intro a; rfl)

private theorem sum_fibre_update_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, DecidableEq (S x)]
    (x : ι) (σ : (y : ι) → S y) (a : S x)
    (f : ((y : ι) → S y) → ℝ) :
    fibreUpdatePointMass x σ a f =
      f (Function.update σ x a) := by
  classical
  rw [show fibreUpdatePointMass x σ a f =
      ∑ τ, if AKLT.Blueprint.Q.fullFibreEvent x σ τ ∧ τ x = a then f τ else 0 by rfl]
  have hmass : (∑ τ, if AKLT.Blueprint.Q.fullFibreEvent x σ τ ∧ τ x = a then f τ else 0) =
      fibreUpdateMass x σ (fun τ => if τ x = a then f τ else 0) := by
    unfold fibreUpdateMass
    apply Finset.sum_congr rfl
    intro τ hτ
    by_cases hE : AKLT.Blueprint.Q.fullFibreEvent x σ τ
    · by_cases ha : τ x = a <;> simp [hE, ha]
    · simp [hE]
  rw [hmass, sum_fibre_update]
  simp [Function.update, eq_comm]

private theorem frameBound_pos : 0 < frameBound := by
  unfold frameBound
  have hs : Real.sqrt 5 < 5 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (5:ℝ) by norm_num)]
  positivity

private theorem frameBound_lt_two : frameBound < 2 := by
  unfold frameBound
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem frameRatio_pos : 0 < frameRatio := by
  unfold frameRatio
  exact div_pos frameBound_pos (by linarith [frameBound_lt_two])

private theorem four_incident_card {L N : Size} (x : Site L N) :
    ((Finset.univ : Finset (Bond L N)).filter fun e => x ∈ bondSites e).card = 4 := by
  classical
  let I : Finset (Bond L N) := Finset.univ.filter fun e => x ∈ bondSites e
  have hdegree (e : Bond L N) : AKLT.Uniq.bondDegree e x = if e ∈ I then 1 else 0 := by
    rcases e with ⟨y, d⟩
    have hloop := (AKLT.Uniq.torusGeometry L N).2.1 (y, d)
    change (if y = x then 1 else 0) + (if nextSite y d = x then 1 else 0) =
      if (y, d) ∈ Finset.univ.filter (fun e => x ∈ bondSites e) then 1 else 0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hs : y = x
    · subst y
      have hloop' : x ≠ nextSite x d := by simpa using hloop
      simp [bondSites, hloop'.symm]
    · by_cases ht : nextSite y d = x
      · have hs' : x ≠ y := by
          intro h
          apply hloop
          exact h.symm.trans ht.symm
        simp [bondSites, hs, ht, hs']
      · have hs' : x ≠ y := by
          intro h
          exact hs h.symm
        have ht' : x ≠ nextSite y d := by
          intro h
          exact ht h.symm
        simp [bondSites, hs, ht, hs', ht']
  calc
    I.card = ∑ e : Bond L N, if e ∈ I then 1 else 0 := by simp [I]
    _ = ∑ e : Bond L N, AKLT.Uniq.bondDegree e x := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hdegree]
    _ = 4 := AKLT.Uniq.sum_bondDegree x

private theorem weight_fibre_lower {L N : Size} (hB : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColouring κ)
    (x : Site L N) (σ : TorusConfiguration L N) (a b : IcoLetter) :
    frameRatio ^ 4 * torusWeight L N κ (Function.update σ x b) ≤
      torusWeight L N κ (Function.update σ x a) := by
  classical
  let r : ℝ := frameRatio
  let fac (τ : TorusConfiguration L N) (e : Bond L N) :=
    1 - dot (frameVector (κ e.1) (τ e.1))
      (frameVector (κ (nextSite e.1 e.2)) (τ (nextSite e.1 e.2)))
  have hbpos := frameBound_pos
  have hb2 := frameBound_lt_two
  have hrpos := frameRatio_pos
  have hfac (τ : TorusConfiguration L N) (e : Bond L N) :
      frameBound ≤ fac τ e ∧ fac τ e ≤ 2 - frameBound := by
    dsimp [fac]
    have hc := hκ e
    exact ⟨(hB (κ e.1) (κ (nextSite e.1 e.2)) hc
        (τ e.1) (τ (nextSite e.1 e.2))).2.2.1,
      (hB (κ e.1) (κ (nextSite e.1 e.2)) hc
        (τ e.1) (τ (nextSite e.1 e.2))).2.2.2⟩
  have hone (e : Bond L N) :
      (if x ∈ bondSites e then r * fac (Function.update σ x b) e
        else fac (Function.update σ x b) e) ≤ fac (Function.update σ x a) e := by
    by_cases hx : x ∈ bondSites e
    · have hb := hfac (Function.update σ x a) e
      have ha := hfac (Function.update σ x b) e
      simp only [if_pos hx]
      dsimp [r, frameRatio]
      have hden : 0 < 2 - frameBound := by linarith
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).2
      have hfa : 0 ≤ fac (Function.update σ x a) e - frameBound := by linarith [hb.1]
      have hfb : 0 ≤ (2 - frameBound) - fac (Function.update σ x b) e := by
        linarith [ha.2]
      nlinarith [mul_nonneg (le_of_lt hden) hfa,
        mul_nonneg (le_of_lt hbpos) hfb]
    · have he₁ : e.1 ≠ x := by
        intro hh
        exact hx (by simp [bondSites, hh])
      have he₂ : nextSite e.1 e.2 ≠ x := by
        intro hh
        exact hx (by simp [bondSites, hh])
      simp [hx, fac, Function.update_of_ne, he₁, he₂]
  have hprod :
      (∏ e : Bond L N,
        (if x ∈ bondSites e then r else 1) * fac (Function.update σ x b) e) ≤
        ∏ e : Bond L N, fac (Function.update σ x a) e := by
    apply Finset.prod_le_prod₀
    · intro e he
      by_cases hx : x ∈ bondSites e
      · exact mul_nonneg (by simp [hx]; exact le_of_lt hrpos)
          (le_of_lt (lt_of_lt_of_le hbpos (hfac _ e).1))
      · simpa [hx] using (le_of_lt (lt_of_lt_of_le hbpos (hfac _ e).1)
          : 0 ≤ fac (Function.update σ x b) e)
    · intro e he
      by_cases hx : x ∈ bondSites e
      · simpa [hx] using hone e
      · simpa [hx] using hone e
  have hcard := four_incident_card x
  let I : Finset (Bond L N) := Finset.univ.filter fun e => x ∈ bondSites e
  have hmult : (∏ e : Bond L N, if x ∈ bondSites e then r else 1) = r ^ 4 := by
    calc
      (∏ e : Bond L N, if x ∈ bondSites e then r else 1) = ∏ e ∈ I, r := by
        simp only [I]
        rw [← Finset.prod_filter]
      _ = r ^ I.card := by simp
      _ = r ^ 4 := by rw [hcard]
  have hfacprod :
      (∏ e : Bond L N, (if x ∈ bondSites e then r else 1) * fac (Function.update σ x b) e) =
        r ^ 4 * ∏ e : Bond L N, fac (Function.update σ x b) e := by
    rw [Finset.prod_mul_distrib, hmult]
  have hweightA : torusWeight L N κ (Function.update σ x a) =
      (∏ _y : Site L N, (1 / 12 : ℝ)) *
        ∏ e : Bond L N, fac (Function.update σ x a) e := by
    simp [torusWeight, fac]
  have hweightB : torusWeight L N κ (Function.update σ x b) =
      (∏ _y : Site L N, (1 / 12 : ℝ)) *
        ∏ e : Bond L N, fac (Function.update σ x b) e := by
    simp [torusWeight, fac]
  rw [hfacprod] at hprod
  rw [hweightA, hweightB]
  have hconst : 0 ≤ ∏ _y : Site L N, (1 / 12 : ℝ) := by positivity
  calc
    frameRatio ^ 4 * ((∏ _y : Site L N, (1 / 12 : ℝ)) *
        ∏ e : Bond L N, fac (Function.update σ x b) e) =
      (∏ _y : Site L N, (1 / 12 : ℝ)) *
        (frameRatio ^ 4 * ∏ e : Bond L N, fac (Function.update σ x b) e) := by ring
    _ ≤ (∏ _y : Site L N, (1 / 12 : ℝ)) *
        ∏ e : Bond L N, fac (Function.update σ x a) e :=
      mul_le_mul_of_nonneg_left hprod hconst

private theorem torusWeight_pos {L N : Size}
    (hB : AKLT.Blueprint.Q.interactionBounds)
    (κ : Site L N → Fin 3) (hκ : ProperTorusColouring κ)
    (σ : TorusConfiguration L N) : 0 < torusWeight L N κ σ := by
  rw [torusWeight]
  apply mul_pos
  · apply Finset.prod_pos
    intro y hy
    norm_num
  · apply Finset.prod_pos
    intro e he
    exact lt_of_lt_of_le frameBound_pos
      ((hB (κ e.1) (κ (nextSite e.1 e.2)) (hκ e) (σ e.1)
        (σ (nextSite e.1 e.2))).2.2.1)

private theorem conditionalProbability_normalize {Ω : Type*} [Fintype Ω]
    (w : Weight Ω) (E A : Ω → Prop)
    (hZ : (∑ x, w x) ≠ 0)
    (hD : AKLT.Defs.eventMass w E ≠ 0) :
    conditionalProbability (AKLT.Defs.normalize w) E A =
      conditionalProbability w E A := by
  classical
  have hD' : (∑ x, if E x then w x else 0) ≠ 0 := by
    simpa [AKLT.Defs.eventMass] using hD
  unfold conditionalProbability AKLT.Defs.normalize
  letI : DecidablePred (fun x : Ω => E x ∧ A x) := fun x =>
    @instDecidableAnd (E x) (A x)
      (Classical.propDecidable (E x)) (Classical.propDecidable (A x))
  have hsum (P : Ω → Prop) [DecidablePred P] :
      (∑ x, if P x then w x / (∑ y, w y) else 0) =
        (∑ x, if P x then w x else 0) / (∑ y, w y) := by
    calc
      (∑ x, if P x then w x / (∑ y, w y) else 0) =
        ∑ x, (if P x then w x else 0) / (∑ y, w y) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hp : P x <;> simp [hp]
      _ = (∑ x, if P x then w x else 0) / (∑ y, w y) := by
        rw [Finset.sum_div]
  calc
    (∑ σ, if E σ ∧ A σ then w σ / (∑ y, w y) else 0) /
        (∑ σ, if E σ then w σ / (∑ y, w y) else 0) =
      ((∑ σ, if E σ ∧ A σ then w σ else 0) / (∑ y, w y)) /
        ((∑ σ, if E σ then w σ else 0) / (∑ y, w y)) := by
          exact congrArg₂ (fun n d : ℝ => n / d)
            (hsum (fun x => E x ∧ A x)) (hsum E)
    _ = (∑ σ, if E σ ∧ A σ then w σ else 0) /
        (∑ σ, if E σ then w σ else 0) := by
          field_simp [hZ, hD']

private theorem raw_torus_fibre_probability {L N : Size}
    (κ : Site L N → Fin 3) (x : Site L N)
    (σ : TorusConfiguration L N) (a : IcoLetter) :
    conditionalProbability (torusWeight L N κ)
      (AKLT.Blueprint.Q.fullFibreEvent x σ) (fun τ => τ x = a) =
        torusWeight L N κ (Function.update σ x a) /
          ∑ b : IcoLetter, torusWeight L N κ (Function.update σ x b) := by
  classical
  letI : DecidableEq IcoLetter := fun c d => Classical.propDecidable (c = d)
  unfold conditionalProbability
  have hnum :
      (∑ τ, if AKLT.Blueprint.Q.fullFibreEvent x σ τ ∧ τ x = a then
        torusWeight L N κ τ else 0) =
        torusWeight L N κ (Function.update σ x a) := by
    calc
      (∑ τ, if AKLT.Blueprint.Q.fullFibreEvent x σ τ ∧ τ x = a then
          torusWeight L N κ τ else 0) =
        fibreUpdateMass x σ (fun τ => if τ x = a then torusWeight L N κ τ else 0) := by
          unfold fibreUpdateMass
          apply Finset.sum_congr rfl
          intro τ hτ
          by_cases hE : AKLT.Blueprint.Q.fullFibreEvent x σ τ
          · by_cases ha : τ x = a <;> simp [hE, ha]
          · simp [hE]
      _ = ∑ b : IcoLetter,
          if (Function.update σ x b) x = a then
            torusWeight L N κ (Function.update σ x b) else 0 :=
        sum_fibre_update x σ (fun τ => if τ x = a then torusWeight L N κ τ else 0)
      _ = torusWeight L N κ (Function.update σ x a) := by
        simp [Function.update, eq_comm]
  have hden :
      (∑ τ, if AKLT.Blueprint.Q.fullFibreEvent x σ τ then
        torusWeight L N κ τ else 0) =
        ∑ b : IcoLetter, torusWeight L N κ (Function.update σ x b) := by
    simpa [fibreUpdateMass] using
      (sum_fibre_update x σ (torusWeight L N κ))
  exact congrArg₂ (fun n d : ℝ => n / d) hnum hden

theorem main : AKLT.Blueprint.Q.TorusOneSiteEnergyStatement := by
  classical
  intro hB L N κ hκ x σ a
  have hZpos : 0 < ∑ τ : TorusConfiguration L N, torusWeight L N κ τ := by
    apply Finset.sum_pos
    · intro τ hτ
      exact torusWeight_pos hB κ hκ τ
    · exact Finset.univ_nonempty
  have hDpos : 0 < ∑ b : IcoLetter, torusWeight L N κ (Function.update σ x b) := by
    apply Finset.sum_pos
    · intro b hb
      exact torusWeight_pos hB κ hκ (Function.update σ x b)
    · exact Finset.univ_nonempty
  have hraw := raw_torus_fibre_probability κ x σ a
  have hmass : (∑ τ : TorusConfiguration L N,
      if AKLT.Blueprint.Q.fullFibreEvent x σ τ then torusWeight L N κ τ else 0) =
      ∑ b : IcoLetter, torusWeight L N κ (Function.update σ x b) := by
    simpa [fibreUpdateMass] using sum_fibre_update x σ (torusWeight L N κ)
  rw [← conditionalProbability_normalize (torusWeight L N κ)
    (AKLT.Blueprint.Q.fullFibreEvent x σ) (fun τ => τ x = a)
    (ne_of_gt hZpos) (by
      change (∑ τ : TorusConfiguration L N,
        if AKLT.Blueprint.Q.fullFibreEvent x σ τ then torusWeight L N κ τ else 0) ≠ 0
      rw [hmass]
      exact ne_of_gt hDpos)] at hraw
  rw [torusLaw]
  change frameEnergy ≤ conditionalProbability (normalize (torusWeight L N κ))
    (AKLT.Blueprint.Q.fullFibreEvent x σ) (fun τ => τ x = a)
  rw [hraw]
  apply (le_div_iff₀ hDpos).2
  have hsum :
      frameRatio ^ 4 *
          (∑ b : IcoLetter, torusWeight L N κ (Function.update σ x b)) ≤
        12 * torusWeight L N κ (Function.update σ x a) := by
    calc
      frameRatio ^ 4 *
          (∑ b : IcoLetter, torusWeight L N κ (Function.update σ x b)) =
        ∑ b : IcoLetter,
          frameRatio ^ 4 * torusWeight L N κ (Function.update σ x b) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ b : IcoLetter, torusWeight L N κ (Function.update σ x a) := by
        apply Finset.sum_le_sum
        intro b hb
        exact weight_fibre_lower hB κ hκ x σ a b
      _ = 12 * torusWeight L N κ (Function.update σ x a) := by
        simp [IcoLetter, Fintype.card_prod]
  have hscaled :
      frameEnergy *
          (∑ b : IcoLetter, torusWeight L N κ (Function.update σ x b)) ≤
        torusWeight L N κ (Function.update σ x a) := by
    dsimp [frameEnergy]
    nlinarith [hsum]
  exact hscaled

#print axioms main

end AKLT.W.Q053
