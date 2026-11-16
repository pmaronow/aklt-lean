import AKLT.Blueprint.Gap.NodesShell

noncomputable section
open scoped BigOperators
namespace AKLT.W.GAP049

open AKLT.Defs AKLT.Blueprint.Gap

private def snocPair {Ω : Type} {m : ℕ} (s : Fin (m + 1) → Ω × Ω) (x : Ω × Ω) :
    Fin (m + 2) → Ω × Ω :=
  Fin.snocEquiv (fun _ : Fin (m + 2) => Ω × Ω) (x, s)

@[simp] private lemma snocPair_castSucc {Ω : Type} {m : ℕ}
    (s : Fin (m + 1) → Ω × Ω) (x : Ω × Ω) (i : Fin (m + 1)) :
    snocPair s x i.castSucc = s i := by
  simp [snocPair, Fin.snocEquiv_apply, Fin.snoc_castSucc]

@[simp] private lemma snocPair_zero {Ω : Type} {m : ℕ}
    (s : Fin (m + 1) → Ω × Ω) (x : Ω × Ω) :
    snocPair s x 0 = s 0 := by
  have hzero : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := by
    apply Fin.ext
    rfl
  rw [hzero]
  exact snocPair_castSucc s x 0

@[simp] private lemma snocPair_last {Ω : Type} {m : ℕ}
    (s : Fin (m + 1) → Ω × Ω) (x : Ω × Ω) :
    snocPair s x (Fin.last (m + 1)) = x := by
  simp [snocPair, Fin.snocEquiv_apply, Fin.snoc_last]

private def finOneFunEquiv (X : Type) : (Fin 1 → X) ≃ X where
  toFun t := t 0
  invFun x := fun _ => x
  left_inv t := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl

private lemma eventMass_compl {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : Probability p) (A : Ω → Prop) :
    eventMass p A + eventMass p (fun x => ¬ A x) = 1 := by
  classical
  letI : DecidablePred (fun x : Ω => ¬ A x) := Classical.decPred _
  unfold eventMass
  have hsum :
      (∑ x, if A x then p x else 0) +
        (∑ x, if (fun y => ¬ A y) x then p x else 0) =
        ∑ x, p x := by
    calc
      _ = ∑ x, ((if A x then p x else 0) +
          (if (fun y => ¬ A y) x then p x else 0)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : A x <;> simp [h]
  calc
    _ = ∑ x, p x := hsum
    _ = 1 := hp.2

private lemma eventMass_compl_le {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : Probability p) (A : Ω → Prop) (δ : ℝ)
    (hδ : δ ≤ eventMass p A) :
    eventMass p (fun x => ¬ A x) ≤ 1 - δ := by
  have hc := eventMass_compl p hp A
  linarith

private lemma sum_mul_event {Ω : Type} [Fintype Ω] (c : ℝ) (p : Weight Ω)
    (A : Ω → Prop) [DecidablePred A] :
    (∑ x, if A x then c * p x else 0) = c * eventMass p A := by
  classical
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : A x <;> simp [h]

private lemma traceLaw_nonneg {Ω : Type} [Fintype Ω] (m : ℕ)
    (initial : Weight (Ω × Ω)) (K : Fin m → Ω × Ω → Weight (Ω × Ω))
    (hi : Probability initial) (hK : ∀ j ω, Probability (K j ω))
    (t : AKLT.Blueprint.Gap.PairTrace Ω m) :
    0 ≤ traceLaw m initial K t := by
  classical
  unfold traceLaw
  apply mul_nonneg (hi.1 _)
  apply Finset.prod_nonneg
  intro j hj
  exact (hK j (t j.castSucc)).1 _

private lemma traceLaw_snoc {Ω : Type} [Fintype Ω] (m : ℕ)
    (initial : Weight (Ω × Ω))
    (K : Fin (m + 1) → Ω × Ω → Weight (Ω × Ω))
    (s : Fin (m + 1) → Ω × Ω) (x : Ω × Ω) :
    traceLaw (m + 1) initial K (snocPair s x) =
      traceLaw m initial (fun i => K i.castSucc) s *
        K (Fin.last m) (s (Fin.last m)) x := by
  classical
  unfold traceLaw
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.succ_castSucc, Fin.succ_last, snocPair_castSucc,
    snocPair_last, snocPair_zero]
  ring

private lemma snoc_event_iff {Ω : Type} [Fintype Ω] (m : ℕ)
    (J : Finset (Fin (m + 1))) (E : Fin (m + 1) → Ω × Ω → Prop)
    (s : Fin (m + 1) → Ω × Ω) (x : Ω × Ω) :
    (∀ j ∈ J, ¬ E j ((snocPair s x) j.succ)) ↔
      (∀ i ∈ (Finset.univ.filter fun i : Fin m => i.castSucc ∈ J),
        ¬ E i.castSucc (s i.succ)) ∧
      (Fin.last m ∈ J → ¬ E (Fin.last m) x) := by
  classical
  let Jpre : Finset (Fin m) := Finset.univ.filter fun i => i.castSucc ∈ J
  change (∀ j ∈ J, ¬ E j ((snocPair s x) j.succ)) ↔
      (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
      (Fin.last m ∈ J → ¬ E (Fin.last m) x)
  constructor
  · intro hall
    constructor
    · intro i hi
      have hiJ : i.castSucc ∈ J := (Finset.mem_filter.mp hi).2
      have h := hall i.castSucc hiJ
      have hidx : i.castSucc.succ = i.succ.castSucc := Fin.succ_castSucc i
      rw [hidx, snocPair_castSucc] at h
      exact h
    · intro hlast
      have h := hall (Fin.last m) hlast
      have hidx : (Fin.last m).succ = Fin.last (m + 1) := Fin.succ_last m
      rw [hidx, snocPair_last] at h
      exact h
  · rintro ⟨hpast, hlast⟩ j hj
    by_cases hlt : (j : ℕ) < m
    · let i : Fin m := ⟨j.val, hlt⟩
      have hij : i.castSucc = j := by
        apply Fin.ext
        rfl
      have hiJ : i ∈ Jpre := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [hij] using hj
      have h := hpast i hiJ
      rw [hij.symm, Fin.succ_castSucc, snocPair_castSucc]
      exact h
    · have hlastj : j = Fin.last m := Fin.eq_last_of_not_lt (by simpa using hlt)
      have hjJ : Fin.last m ∈ J := by rw [← hlastj]; exact hj
      rw [hlastj, Fin.succ_last, snocPair_last]
      exact hlast hjJ

private lemma card_snoc_trials {m : ℕ} (J : Finset (Fin (m + 1))) :
    J.card = (Finset.univ.filter fun i : Fin m => i.castSucc ∈ J).card +
      (if Fin.last m ∈ J then 1 else 0) := by
  classical
  let Jpre : Finset (Fin m) := Finset.univ.filter fun i => i.castSucc ∈ J
  have himage : Jpre.image Fin.castSucc = J.erase (Fin.last m) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Fin.castSucc_ne_last i, (Finset.mem_filter.mp hi).2⟩
    · rintro ⟨hne, hj⟩
      obtain ⟨i, heq⟩ := Fin.eq_castSucc_of_ne_last hne
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
      simpa [heq] using hj
  have hcardImage : (J.erase (Fin.last m)).card = Jpre.card := by
    rw [← himage]
    exact Finset.card_image_of_injective Jpre (Fin.castSucc_injective m)
  by_cases hlast : Fin.last m ∈ J
  · calc
      J.card = (J.erase (Fin.last m)).card + 1 := (Finset.card_erase_add_one hlast).symm
      _ = (Finset.univ.filter fun i : Fin m => i.castSucc ∈ J).card + 1 := by
            rw [hcardImage]
      _ = (Finset.univ.filter fun i : Fin m => i.castSucc ∈ J).card +
            (if Fin.last m ∈ J then 1 else 0) := by simp [hlast]
  · have herase : J.erase (Fin.last m) = J := by
      ext j
      simp [hlast]
    rw [herase] at hcardImage
    simpa [hlast] using hcardImage

private theorem finiteTrialFailureAux (Ω : Type) [Fintype Ω] :
    ∀ (m : ℕ) (initial : Weight (Ω × Ω)), Probability initial →
    ∀ K : Fin m → Ω × Ω → Weight (Ω × Ω), (∀ j ω, Probability (K j ω)) →
    ∀ (J : Finset (Fin m)) (E : Fin m → Ω × Ω → Prop) (δ : ℝ),
      0 ≤ δ → δ ≤ 1 → (∀ j ∈ J, ∀ ω, δ ≤ eventMass (K j ω) (E j)) →
      eventMass (traceLaw m initial K)
        (fun t => ∀ j ∈ J, ¬ E j (t j.succ)) ≤ (1 - δ) ^ J.card := by
  intro m
  induction m with
  | zero =>
      intro initial hi K hK J E δ hδ0 hδ1 hlocal
      have hJ : J = ∅ := by
        ext j
        exact Fin.elim0 j
      subst J
      classical
      have hsum : eventMass (traceLaw 0 initial K) (fun _ => True) = 1 := by
        have hraw : (∑ t : Fin 1 → Ω × Ω, traceLaw 0 initial K t) = 1 := by
          unfold traceLaw
          simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
          rw [Fintype.sum_equiv (finOneFunEquiv (Ω × Ω))
            (fun t => initial (t 0)) (fun x => initial x) (by intro t; rfl)]
          exact hi.2
        simpa [eventMass] using hraw
      calc
        eventMass (traceLaw 0 initial K) (fun t => ∀ j ∈ (∅ : Finset (Fin 0)), ¬ E j (t j.succ)) =
            1 := by simpa using hsum
        _ ≤ (1 - δ) ^ (∅ : Finset (Fin 0)).card := by simp
  | succ m ih =>
      intro initial hi K hK J E δ hδ0 hδ1 hlocal
      classical
      let Jpre : Finset (Fin m) := Finset.univ.filter fun i => i.castSucc ∈ J
      let Kpre : Fin m → Ω × Ω → Weight (Ω × Ω) := fun i => K i.castSucc
      let Epre : Fin m → Ω × Ω → Prop := fun i => E i.castSucc
      letI : DecidablePred (fun t : Fin (m + 2) → Ω × Ω =>
          ∀ j ∈ J, ¬ E j (t j.succ)) := Classical.decPred _
      letI : DecidablePred (fun s : Fin (m + 1) → Ω × Ω =>
          ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) := Classical.decPred _
      letI : DecidablePred (fun x : Ω × Ω => ¬ E (Fin.last m) x) := Classical.decPred _
      have hKpre : ∀ i ω, Probability (Kpre i ω) := by
        intro i ω
        exact hK i.castSucc ω
      have hlocalpre : ∀ i ∈ Jpre, ∀ ω, δ ≤ eventMass (Kpre i ω) (Epre i) := by
        intro i hiJ ω
        exact hlocal i.castSucc ((Finset.mem_filter.mp hiJ).2) ω
      have hprefix := ih initial hi Kpre hKpre Jpre Epre δ hδ0 hδ1 hlocalpre
      have hsum : eventMass (traceLaw (m + 1) initial K)
          (fun t => ∀ j ∈ J, ¬ E j (t j.succ)) =
          ∑ s : Fin (m + 1) → Ω × Ω, ∑ x : Ω × Ω,
            if (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                (Fin.last m ∈ J → ¬ E (Fin.last m) x)
            then traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x
            else 0 := by
        unfold eventMass
        change (∑ t : Fin (m + 2) → Ω × Ω,
            @ite ℝ (∀ j ∈ J, ¬ E j (t j.succ))
              (Classical.propDecidable (∀ j ∈ J, ¬ E j (t j.succ)))
              (traceLaw (m + 1) initial K t) 0) = _
        calc
          (∑ t : Fin (m + 2) → Ω × Ω,
              @ite ℝ (∀ j ∈ J, ¬ E j (t j.succ))
                (Classical.propDecidable (∀ j ∈ J, ¬ E j (t j.succ)))
                (traceLaw (m + 1) initial K t) 0) =
              ∑ z : (Ω × Ω) × (Fin (m + 1) → Ω × Ω),
                @ite ℝ ((∀ i ∈ Jpre, ¬ E i.castSucc (z.2 i.succ)) ∧
                    (Fin.last m ∈ J → ¬ E (Fin.last m) z.1))
                  (Classical.propDecidable ((∀ i ∈ Jpre, ¬ E i.castSucc (z.2 i.succ)) ∧
                    (Fin.last m ∈ J → ¬ E (Fin.last m) z.1)))
                  (traceLaw m initial Kpre z.2 * K (Fin.last m) (z.2 (Fin.last m)) z.1) 0 := by
            symm
            exact Fintype.sum_equiv
              (Fin.snocEquiv (fun _ : Fin (m + 2) => Ω × Ω))
              (fun z : (Ω × Ω) × (Fin (m + 1) → Ω × Ω) =>
                @ite ℝ ((∀ i ∈ Jpre, ¬ E i.castSucc (z.2 i.succ)) ∧
                    (Fin.last m ∈ J → ¬ E (Fin.last m) z.1))
                  (Classical.propDecidable ((∀ i ∈ Jpre, ¬ E i.castSucc (z.2 i.succ)) ∧
                    (Fin.last m ∈ J → ¬ E (Fin.last m) z.1)))
                  (traceLaw m initial Kpre z.2 * K (Fin.last m) (z.2 (Fin.last m)) z.1) 0)
              (fun t => @ite ℝ (∀ j ∈ J, ¬ E j (t j.succ))
                (Classical.propDecidable (∀ j ∈ J, ¬ E j (t j.succ)))
                (traceLaw (m + 1) initial K t) 0)
              (by
                intro z
                let t := Fin.snocEquiv (fun _ : Fin (m + 2) => Ω × Ω) z
                have ht : traceLaw (m + 1) initial K t =
                    traceLaw m initial Kpre z.2 * K (Fin.last m) (z.2 (Fin.last m)) z.1 := by
                  change traceLaw (m + 1) initial K (snocPair z.2 z.1) = _
                  exact traceLaw_snoc m initial K z.2 z.1
                have he :
                    (∀ j ∈ J, ¬ E j (t j.succ)) ↔
                      (∀ i ∈ Jpre, ¬ E i.castSucc (z.2 i.succ)) ∧
                        (Fin.last m ∈ J → ¬ E (Fin.last m) z.1) := by
                  change (∀ j ∈ J, ¬ E j ((snocPair z.2 z.1) j.succ)) ↔ _
                  exact snoc_event_iff m J E z.2 z.1
                by_cases hf : ∀ j ∈ J, ¬ E j (t j.succ)
                · have hp := he.mp hf
                  rw [if_pos hf, if_pos hp, ht]
                · have hp : ¬ ((∀ i ∈ Jpre, ¬ E i.castSucc (z.2 i.succ)) ∧
                      (Fin.last m ∈ J → ¬ E (Fin.last m) z.1)) := by
                    intro h
                    exact hf (he.mpr h)
                  rw [if_neg hf, if_neg hp])
          _ = _ := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hp : (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                (Fin.last m ∈ J → ¬ E (Fin.last m) x)
            · simp [hp]
            · simp [hp]
      have hinner (s : Fin (m + 1) → Ω × Ω) :
          (∑ x : Ω × Ω,
            if (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                (Fin.last m ∈ J → ¬ E (Fin.last m) x)
            then traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x
            else 0) =
          if (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) then
            traceLaw m initial Kpre s *
              (if Fin.last m ∈ J then
                eventMass (K (Fin.last m) (s (Fin.last m))) (fun x => ¬ E (Fin.last m) x)
               else 1)
          else 0 := by
        by_cases hpast : ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
        · by_cases hlast : Fin.last m ∈ J
          ·
            calc
              (∑ x : Ω × Ω,
                if (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                    (Fin.last m ∈ J → ¬ E (Fin.last m) x)
                then traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x else 0) =
                  ∑ x : Ω × Ω,
                    if ¬ E (Fin.last m) x then
                      traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x else 0 := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    by_cases hE : E (Fin.last m) x
                    · have hleft : ¬ ((∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                          (Fin.last m ∈ J → ¬ E (Fin.last m) x)) := by
                        rintro ⟨_, hbad⟩
                        exact (hbad hlast) hE
                      have hright : ¬ ¬ E (Fin.last m) x := by
                        intro hn
                        exact hn hE
                      rw [if_neg hleft, if_neg hright]
                    · have hleft : (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                          (Fin.last m ∈ J → ¬ E (Fin.last m) x) :=
                        ⟨hpast, fun _ => hE⟩
                      rw [if_pos hleft, if_pos hE]
              _ = traceLaw m initial Kpre s *
                    eventMass (K (Fin.last m) (s (Fin.last m)))
                      (fun x => ¬ E (Fin.last m) x) :=
                    sum_mul_event (traceLaw m initial Kpre s)
                      (K (Fin.last m) (s (Fin.last m))) (fun x => ¬ E (Fin.last m) x)
              _ = _ := by
                rw [if_pos hlast]
                rw [if_pos hpast]
          · have htotal := (hK (Fin.last m) (s (Fin.last m))).2
            have hsum : (∑ x : Ω × Ω,
                traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x) =
                traceLaw m initial Kpre s := by
              rw [← Finset.mul_sum, htotal, mul_one]
            calc
              (∑ x : Ω × Ω,
                if (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                    (Fin.last m ∈ J → ¬ E (Fin.last m) x)
                then traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x else 0) =
                  ∑ x : Ω × Ω, traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    have hleft : (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                        (Fin.last m ∈ J → ¬ E (Fin.last m) x) :=
                      ⟨hpast, fun h => False.elim (hlast h)⟩
                    rw [if_pos hleft]
              _ = traceLaw m initial Kpre s := hsum
              _ = _ := by
                rw [if_neg hlast]
                rw [if_pos hpast]
                simp [mul_one]
        · simp [hpast]
      letI : DecidablePred
          (fun s : Fin (m + 1) → Ω × Ω => ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) :=
        Classical.decPred _
      have hprefixMass : eventMass (traceLaw m initial Kpre)
          (fun s => ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) =
          ∑ s : Fin (m + 1) → Ω × Ω,
            @ite ℝ (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ))
              (Classical.propDecidable (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)))
              (traceLaw m initial Kpre s) 0 := by
        unfold eventMass
        rfl
      have hcard := card_snoc_trials J
      by_cases hlast : Fin.last m ∈ J
      · have hbad (s : Fin (m + 1) → Ω × Ω) :
            eventMass (K (Fin.last m) (s (Fin.last m)))
              (fun x => ¬ E (Fin.last m) x) ≤ 1 - δ :=
          eventMass_compl_le (K (Fin.last m) (s (Fin.last m)))
            (hK (Fin.last m) (s (Fin.last m))) (E (Fin.last m))
            δ (hlocal (Fin.last m) hlast (s (Fin.last m)))
        have hnonneg : 0 ≤ 1 - δ := by linarith
        rw [hsum]
        calc
          (∑ s : Fin (m + 1) → Ω × Ω, ∑ x : Ω × Ω,
              if (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                  (Fin.last m ∈ J → ¬ E (Fin.last m) x)
              then traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x
              else 0) =
              ∑ s : Fin (m + 1) → Ω × Ω,
                if ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
                then traceLaw m initial Kpre s *
                  eventMass (K (Fin.last m) (s (Fin.last m)))
                    (fun x => ¬ E (Fin.last m) x)
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [hinner s]
                  rw [if_pos hlast]
          _ ≤ ∑ s : Fin (m + 1) → Ω × Ω,
                if ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
                then traceLaw m initial Kpre s * (1 - δ)
                else 0 := by
                  apply Finset.sum_le_sum
                  intro s hs
                  by_cases hpast : ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
                  · simp only [if_pos hpast]
                    exact mul_le_mul_of_nonneg_left (hbad s)
                      (traceLaw_nonneg m initial Kpre hi hKpre s)
                  · simp [hpast]
          _ = (1 - δ) * eventMass (traceLaw m initial Kpre)
                (fun s => ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) := by
                  calc
                    _ = (1 - δ) * (∑ s : Fin (m + 1) → Ω × Ω,
                        if ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
                        then traceLaw m initial Kpre s else 0) := by
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro s hs
                          by_cases hpast : ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
                          · simp [hpast, mul_comm]
                          · simp [hpast]
                    _ = _ := by
                          congr 1
          _ ≤ (1 - δ) * ((1 - δ) ^ Jpre.card) :=
                mul_le_mul_of_nonneg_left hprefix hnonneg
          _ = (1 - δ) ^ J.card := by
                have hc : J.card = Jpre.card + 1 := by
                  simpa [Jpre, hlast] using hcard
                rw [hc, pow_succ]
                ring
      · have htotal (s : Fin (m + 1) → Ω × Ω) :
            eventMass (K (Fin.last m) (s (Fin.last m))) (fun _ : Ω × Ω => True) = 1 := by
          simpa [eventMass] using (hK (Fin.last m) (s (Fin.last m))).2
        rw [hsum]
        calc
          (∑ s : Fin (m + 1) → Ω × Ω, ∑ x : Ω × Ω,
              if (∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) ∧
                  (Fin.last m ∈ J → ¬ E (Fin.last m) x)
              then traceLaw m initial Kpre s * K (Fin.last m) (s (Fin.last m)) x
              else 0) =
              ∑ s : Fin (m + 1) → Ω × Ω,
                if ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
                then traceLaw m initial Kpre s else 0 := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [hinner s]
                  simp [hlast]
          _ = eventMass (traceLaw m initial Kpre)
                (fun s => ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)) := by
                  unfold eventMass
                  apply Finset.sum_congr rfl
                  intro s hs
                  by_cases hpast : ∀ i ∈ Jpre, ¬ E i.castSucc (s i.succ)
                  · simp [hpast]
                  · simp [hpast]
          _ ≤ (1 - δ) ^ Jpre.card := hprefix
          _ = (1 - δ) ^ J.card := by
                have hc : J.card = Jpre.card := by
                  simpa [Jpre, hlast] using hcard
                rw [hc]

/-- Finite adaptive trial failure estimate, with no independence assumption. -/
theorem main : AKLT.Blueprint.Gap.FiniteTrialFailureStatement := by
  intro Ω instΩ m initial hinitial K hK J E δ hδ0 hδ1 hlocal
  exact finiteTrialFailureAux Ω m initial hinitial K hK J E δ hδ0 hδ1 hlocal

#print axioms main
end AKLT.W.GAP049
