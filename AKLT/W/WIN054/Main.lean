import AKLT.Blueprint.Win.NodesRemoval

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN054

private lemma normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  unfold normSq dot
  apply Finset.sum_nonneg
  intro i hi
  exact mul_self_nonneg (v i)

private lemma normSq_sum_identity (s : Finset Plane) (m : Plane → Vec3) :
    normSq (∑ z ∈ s, m z) = ∑ z ∈ s, ∑ w ∈ s, dot (m z) (m w) := by
  classical
  unfold normSq dot
  simp only [Finset.sum_apply]
  calc
    (∑ i : Fin 3, (∑ z ∈ s, m z i) * (∑ w ∈ s, m w i)) =
        ∑ i : Fin 3, ∑ z ∈ s, ∑ w ∈ s, m z i * m w i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_mul_sum s s (fun z => m z i) (fun w => m w i)
    _ = ∑ z ∈ s, ∑ w ∈ s, ∑ i : Fin 3, m z i * m w i := by
          rw [Finset.sum_comm (s := Finset.univ) (t := s)]
          apply Finset.sum_congr rfl
          intro z hz
          rw [Finset.sum_comm (s := Finset.univ) (t := s)]

private lemma pairSum_identity (s : Finset Plane) (m : Plane → Vec3) :
    pairSum s m = (1 / 2 : ℝ) *
      (normSq (∑ z ∈ s, m z) - ∑ z ∈ s, normSq (m z)) := by
  classical
  unfold pairSum
  have hdiag : ∀ z ∈ s,
      (∑ w ∈ s, if z = w then 0 else dot (m z) (m w)) =
        (∑ w ∈ s, dot (m z) (m w)) - dot (m z) (m z) := by
    intro z hz
    calc
      (∑ w ∈ s, if z = w then 0 else dot (m z) (m w)) =
          ∑ w ∈ s, (dot (m z) (m w) - if z = w then dot (m z) (m w) else 0) := by
            apply Finset.sum_congr rfl
            intro w hw
            by_cases hzw : z = w <;> simp [hzw]
      _ = (∑ w ∈ s, dot (m z) (m w)) -
            ∑ w ∈ s, (if z = w then dot (m z) (m w) else 0) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ w ∈ s, dot (m z) (m w)) - dot (m z) (m z) := by
            simp [hz]
  have htotal :
      (∑ z ∈ s, ∑ w ∈ s, if z = w then 0 else dot (m z) (m w)) =
        (∑ z ∈ s, ∑ w ∈ s, dot (m z) (m w)) -
          ∑ z ∈ s, dot (m z) (m z) := by
    calc
      _ = ∑ z ∈ s,
            ((∑ w ∈ s, dot (m z) (m w)) - dot (m z) (m z)) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hdiag z hz
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [htotal, normSq_sum_identity]
  simp only [normSq, dot]

private lemma pairSum_lower (s : Finset Plane) (m : Plane → Vec3)
    (hm : ∀ z ∈ s, normSq (m z) ≤ (3 / 5 : ℝ) ^ 2) :
    -(9 / 50 : ℝ) * (s.card : ℝ) ≤ pairSum s m := by
  have htot := normSq_nonneg (∑ z ∈ s, m z)
  have hsum : (∑ z ∈ s, normSq (m z)) ≤ (s.card : ℝ) * (9 / 25 : ℝ) := by
    calc
      (∑ z ∈ s, normSq (m z)) ≤ ∑ z ∈ s, (9 / 25 : ℝ) := by
        apply Finset.sum_le_sum
        intro z hz
        have h := hm z hz
        norm_num [pow_two] at h ⊢
        exact h
      _ = (s.card : ℝ) * (9 / 25 : ℝ) := by simp
  rw [pairSum_identity]
  nlinarith

private lemma fibreMean_sum {D : Finset Plane} (p : Weight (PlaneConfiguration D))
    (V : Finset Plane) (σ : PlaneConfiguration D) (s : Finset Plane)
    (f : Plane → PlaneConfiguration D → ℝ) :
    fibreMean p V σ (fun ω => ∑ z ∈ s, f z ω) =
      ∑ z ∈ s, fibreMean p V σ (f z) := by
  classical
  unfold fibreMean
  have hnum :
      (∑ ω, if restEvent V σ ω then p ω * (∑ z ∈ s, f z ω) else 0) =
        ∑ z ∈ s, ∑ ω, if restEvent V σ ω then p ω * f z ω else 0 := by
    calc
      _ = ∑ ω, ∑ z ∈ s, if restEvent V σ ω then p ω * f z ω else 0 := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases he : restEvent V σ ω
        · simp [he, Finset.mul_sum]
        · simp [he]
      _ = _ := Finset.sum_comm
  rw [hnum, Finset.sum_div]

private lemma fibreMean_scale {D : Finset Plane} (p : Weight (PlaneConfiguration D))
    (V : Finset Plane) (σ : PlaneConfiguration D) (c : ℝ)
    (f : PlaneConfiguration D → ℝ) :
    fibreMean p V σ (fun ω => c * f ω) = c * fibreMean p V σ f := by
  classical
  unfold fibreMean
  have hnum :
      (∑ ω, if restEvent V σ ω then p ω * (c * f ω) else 0) =
        c * (∑ ω, if restEvent V σ ω then p ω * f ω else 0) := by
    calc
      _ = ∑ ω, c * (if restEvent V σ ω then p ω * f ω else 0) := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases he : restEvent V σ ω <;> simp [he, mul_left_comm]
      _ = _ := by rw [Finset.mul_sum]
  rw [hnum]
  ring

private def outsideConfig {D : Finset Plane} (V : Finset Plane)
    (σ : PlaneConfiguration D) : PlaneConfiguration (D \ V) :=
  fun z => σ ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩

private lemma restEvent_iff_outsideConfig {D : Finset Plane} (V : Finset Plane)
    (σ ω : PlaneConfiguration D) :
    restEvent V σ ω ↔ outsideConfig V ω = outsideConfig V σ := by
  constructor
  · intro h
    funext z
    exact h ⟨z.val, (Finset.mem_sdiff.mp z.property).1⟩
      (Finset.mem_sdiff.mp z.property).2
  · intro h z hz
    let r : ↥(D \ V) := ⟨z.val, Finset.mem_sdiff.mpr ⟨z.property, hz⟩⟩
    have hz' : outsideConfig V ω r = outsideConfig V σ r := congrFun h r
    exact hz'

private def fibreMass {D : Finset Plane} (p : Weight (PlaneConfiguration D))
    (V : Finset Plane) (q : PlaneConfiguration (D \ V)) : ℝ :=
  ∑ σ, if outsideConfig V σ = q then p σ else 0

private def fibreNumerator {D : Finset Plane} (p : Weight (PlaneConfiguration D))
    (V : Finset Plane) (q : PlaneConfiguration (D \ V))
    (f : PlaneConfiguration D → ℝ) : ℝ :=
  ∑ σ, if outsideConfig V σ = q then p σ * f σ else 0

private lemma eventMass_eq_fibreMass {D : Finset Plane} (p : Weight (PlaneConfiguration D))
    (V : Finset Plane) (σ : PlaneConfiguration D) :
    eventMass p (restEvent V σ) = fibreMass p V (outsideConfig V σ) := by
  classical
  unfold eventMass fibreMass
  apply Finset.sum_congr rfl
  intro ω hω
  simp [restEvent_iff_outsideConfig]

private lemma fibreNumerator_eq_conditional {D : Finset Plane}
    (p : Weight (PlaneConfiguration D)) (V : Finset Plane) (σ : PlaneConfiguration D)
    (f : PlaneConfiguration D → ℝ)
    (hmass : 0 < eventMass p (restEvent V σ)) :
    fibreNumerator p V (outsideConfig V σ) f =
      fibreMean p V σ f * fibreMass p V (outsideConfig V σ) := by
  classical
  have hnum : fibreNumerator p V (outsideConfig V σ) f =
      ∑ ω, if restEvent V σ ω then p ω * f ω else 0 := by
    unfold fibreNumerator
    apply Finset.sum_congr rfl
    intro ω hω
    simp [restEvent_iff_outsideConfig]
  rw [hnum, ← eventMass_eq_fibreMass]
  unfold fibreMean
  dsimp [eventMass]
  have hden : (∑ σ_1, if restEvent V σ σ_1 then p σ_1 else 0) ≠ 0 := by
    simpa [eventMass] using (ne_of_gt hmass)
  field_simp [hden]

private lemma fibrePairMean {D : Finset Plane} (p : Weight (PlaneConfiguration D))
    (V : Finset Plane) (σ : PlaneConfiguration D)
    (hc : NeighbourControl p V) (hmass : 0 < eventMass p (restEvent V σ)) :
    fibreMean p V σ (fun ω => pairSum V (extendIcoSpins ω)) =
      pairSum V (fun z => fibreSpinMean p V σ z) := by
  classical
  have hsum :
      fibreMean p V σ (fun ω =>
        ∑ z ∈ V, ∑ w ∈ V,
          if z = w then 0 else dot (extendIcoSpins ω z) (extendIcoSpins ω w)) =
        ∑ z ∈ V, ∑ w ∈ V,
          if z = w then 0 else dot (fibreSpinMean p V σ z) (fibreSpinMean p V σ w) := by
    rw [fibreMean_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [fibreMean_sum]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hzw : z = w
    · simp [hzw, fibreMean]
    · simp only [hzw, ↓reduceIte]
      exact (hc σ hmass).2 z hz w hw hzw
  change fibreMean p V σ (fun ω => (1 / 2 : ℝ) *
      ∑ z ∈ V, ∑ w ∈ V,
        if z = w then 0 else dot (extendIcoSpins ω z) (extendIcoSpins ω w)) = _
  rw [fibreMean_scale, hsum]
  rfl

theorem main : AKLT.Blueprint.Win.PairMeanAveragingStatement := by
  classical
  intro D V hVD p hp hc
  let f : PlaneConfiguration D → ℝ := fun σ => pairSum V (extendIcoSpins σ)
  let c : ℝ := -(9 / 50 : ℝ) * (V.card : ℝ)
  have hp0 : ∀ σ, 0 ≤ p σ := hp.1
  have hlocal : ∀ σ, 0 < eventMass p (restEvent V σ) →
      c ≤ fibreMean p V σ f := by
    intro σ hmass
    have hcontrol := hc σ hmass
    have hmean := pairSum_lower V (fun z => fibreSpinMean p V σ z)
      (fun z hz => hcontrol.1 z hz)
    rw [show c = -(9 / 50 : ℝ) * (V.card : ℝ) by rfl]
    change -(9 / 50 : ℝ) * (V.card : ℝ) ≤
      fibreMean p V σ (fun ω => pairSum V (extendIcoSpins ω))
    rw [fibrePairMean p V σ hc hmass]
    exact hmean
  have hfibre : ∀ q : PlaneConfiguration (D \ V),
      c * fibreMass p V q ≤ fibreNumerator p V q f := by
    intro q
    have hmassNonneg : 0 ≤ fibreMass p V q := by
      unfold fibreMass
      apply Finset.sum_nonneg
      intro ω hω
      by_cases he : outsideConfig V ω = q
      · simp [he, hp0 ω]
      · simp [he]
    by_cases hmpos : 0 < fibreMass p V q
    · have hq : ∃ σ, outsideConfig V σ = q := by
        by_contra h
        have hneq : ∀ σ, outsideConfig V σ ≠ q := by
          intro σ hσ
          exact h ⟨σ, hσ⟩
        have hz : fibreMass p V q = 0 := by simp [fibreMass, hneq]
        linarith
      let σ : PlaneConfiguration D := Classical.choose hq
      have hσ : outsideConfig V σ = q := Classical.choose_spec hq
      have hmEq : eventMass p (restEvent V σ) = fibreMass p V q := by
        rw [eventMass_eq_fibreMass, hσ]
      have hm : 0 < eventMass p (restEvent V σ) := by
        rw [hmEq]
        exact hmpos
      have hnum := fibreNumerator_eq_conditional p V σ f hm
      have hbound : c ≤ fibreMean p V σ f := hlocal σ hm
      calc
        c * fibreMass p V q ≤ fibreMean p V σ f * fibreMass p V q :=
          mul_le_mul_of_nonneg_right hbound hmassNonneg
        _ = fibreNumerator p V q f := by
          rw [← hσ]
          exact hnum.symm
    · have hmass0 : fibreMass p V q = 0 := le_antisymm (le_of_not_gt hmpos) hmassNonneg
      have hterms : ∀ σ, (if outsideConfig V σ = q then p σ else 0) = 0 := by
        have hsumzero : (∑ σ, if outsideConfig V σ = q then p σ else 0) = 0 := hmass0
        have hnonneg : ∀ σ ∈ (Finset.univ : Finset (PlaneConfiguration D)),
            0 ≤ (if outsideConfig V σ = q then p σ else 0) := by
          intro σ hσ
          by_cases he : outsideConfig V σ = q
          · simp [he, hp0 σ]
          · simp [he]
        exact fun σ =>
          (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumzero σ (Finset.mem_univ σ)
      have hnumzero : fibreNumerator p V q f = 0 := by
        unfold fibreNumerator
        apply Finset.sum_eq_zero
        intro σ hσ
        by_cases he : outsideConfig V σ = q
        · have hpσ : p σ = 0 := by simpa [he] using hterms σ
          simp [he, hpσ]
        · simp [he]
      simp [hmass0, hnumzero]
  have hmassTotal : (∑ q : PlaneConfiguration (D \ V), fibreMass p V q) = 1 := by
    unfold fibreMass
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, hp.2]
  have hdecomp :
      expectation p f = ∑ q : PlaneConfiguration (D \ V), fibreNumerator p V q f := by
    unfold expectation fibreNumerator
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := outsideConfig V)
      (f := fun σ => p σ * f σ)]
    simp [Finset.sum_filter]
  calc
    c = c * (∑ q : PlaneConfiguration (D \ V), fibreMass p V q) := by
      rw [hmassTotal]
      ring
    _ = ∑ q : PlaneConfiguration (D \ V), c * fibreMass p V q := by
      rw [Finset.mul_sum]
    _ ≤ ∑ q : PlaneConfiguration (D \ V), fibreNumerator p V q f :=
      Finset.sum_le_sum (fun q hq => hfibre q)
    _ = expectation p f := hdecomp.symm

end AKLT.W.WIN054
