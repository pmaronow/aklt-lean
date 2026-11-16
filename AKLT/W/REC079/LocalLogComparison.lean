import AKLT.W.REC079.TrailComparison
import AKLT.W.REC079.LocalInputs
import AKLT.W.REC013.Main
import AKLT.W.REC014.Main
import AKLT.W.REC017.Main
import AKLT.W.REC022.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

open AKLT.W.REC096

theorem pair_kernel_mem (p : PairSetup) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U)
    {a b : Plane}
    (ha : (prefixNetwork p.normalized p.u w i.val).Present (wordVertex p.u w i.val) a)
    (hb : (prefixNetwork p.normalized p.u w i.val).Present (wordVertex p.u w i.val) b)
    (hab : a ≠ b) :
    {(canonicalChart p.toPairData).point a, (canonicalChart p.toPairData).point b} ∈
      responsePairs (canonicalWord p.toPairData w) i := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, Finset.card_pair (fun he => hab ((canonicalChart p.toPairData).point.injective he))⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact ⟨present_kernel_mem p w hw i hU ha, present_kernel_mem p w hw i hU hb⟩

theorem kernel_pair_signal (p : PairData) {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (a b : Plane) (hab : a ≠ b) :
    pairSignal (removeSite (prefixNetwork p.normalized p.u w i.val) (wordVertex p.u w i.val)) p.τ
      (({(canonicalChart p).point a, (canonicalChart p).point b} : Finset Plane).image
        (canonicalChart p).point.symm) =
    |pairResponse (prefixNetwork p.normalized p.u w i.val) p.τ (wordVertex p.u w i.val) a b| := by
  simp only [Finset.image_insert, Finset.image_singleton, Equiv.symm_apply_apply]
  exact pairSignal_pair _ _ _ _ hab

theorem pair_sets_ne {α : Type*} [DecidableEq α] {a b c : α}
    (hba : b ≠ a) (hbc : b ≠ c) : ({a, b} : Finset α) ≠ {a, c} := by
  intro he
  have hb : b ∈ ({a, b} : Finset α) := by simp
  rw [he] at hb
  simpa only [Finset.mem_insert, Finset.mem_singleton, hba, hbc, or_self] using hb

theorem reward_single_le (p : PairData) {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U)
    (q : Finset Plane) (hq : q ∈ responsePairs (canonicalWord p w) i) :
    (pairCoefficient (canonicalWord p w) i q : ℝ) *
      pairSignal (removeSite (prefixNetwork p.normalized p.u w i.val) (wordVertex p.u w i.val)) p.τ
        (q.image (canonicalChart p).point.symm) ≤ localResponseReward p w i := by
  unfold localResponseReward
  dsimp only
  rw [if_pos hU]
  apply Finset.single_le_sum (s := responsePairs (canonicalWord p w) i)
    (f := fun q : Finset Plane => (pairCoefficient (canonicalWord p w) i q : ℝ) *
      pairSignal (removeSite (prefixNetwork p.normalized p.u w i.val) (wordVertex p.u w i.val)) p.τ
        (q.image (canonicalChart p).point.symm))
  · intro q _
    exact mul_nonneg (Rat.cast_nonneg.mpr (pairCoefficient_nonneg (canonicalWord p w) i q))
      (pairSignal_nonneg (removeSite (prefixNetwork p.normalized p.u w i.val)
        (wordVertex p.u w i.val)) p.τ (q.image (canonicalChart p).point.symm))
  · exact hq

theorem reward_three_le (p : PairData) {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U)
    (q₁ q₂ q₃ : Finset Plane) (h₁ : q₁ ∈ responsePairs (canonicalWord p w) i)
    (h₂ : q₂ ∈ responsePairs (canonicalWord p w) i) (h₃ : q₃ ∈ responsePairs (canonicalWord p w) i)
    (h₁₂ : q₁ ≠ q₂) (h₁₃ : q₁ ≠ q₃) (h₂₃ : q₂ ≠ q₃) :
    let term := fun q => (pairCoefficient (canonicalWord p w) i q : ℝ) *
      pairSignal (removeSite (prefixNetwork p.normalized p.u w i.val) (wordVertex p.u w i.val)) p.τ
        (q.image (canonicalChart p).point.symm)
    term q₁ + term q₂ + term q₃ ≤ localResponseReward p w i := by
  classical
  dsimp only
  unfold localResponseReward
  dsimp only
  rw [if_pos hU]
  have hsub : ({q₁, q₂, q₃} : Finset (Finset Plane)) ⊆ responsePairs (canonicalWord p w) i := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => mul_nonneg (Rat.cast_nonneg.mpr (pairCoefficient_nonneg (canonicalWord p w) i q))
      (pairSignal_nonneg (removeSite (prefixNetwork p.normalized p.u w i.val)
        (wordVertex p.u w i.val)) p.τ (q.image (canonicalChart p).point.symm)))
  simpa [h₁₂, h₁₃, h₂₃, add_assoc] using hh

theorem present_neighbour_cases (a : Departure) (hU : a.D.status a.y = .U) :
    (a.D.presentNeighbours a.y).card = 1 ∨
    (∃ f, a.D.presentNeighbours a.y = {a.o, f} ∧ a.o ≠ f) ∨
    (∃ f g, a.D.presentNeighbours a.y = {a.o, f, g} ∧ a.o ≠ f ∧ a.o ≠ g ∧ f ≠ g) := by
  classical
  have hle : (a.D.presentNeighbours a.y).card ≤ 3 := by
    rcases a.start.2.2 with h | h
    · exact h.2
    · simp [hU] at h
  have he := Finset.insert_erase a.present
  have hc : ((a.D.presentNeighbours a.y).erase a.o).card ≤ 2 := by
    rw [Finset.card_erase_of_mem a.present]
    omega
  interval_cases hcard : ((a.D.presentNeighbours a.y).erase a.o).card
  · left
    have hempty := Finset.card_eq_zero.mp hcard
    rw [hempty] at he
    rw [← he]
    simp
  · right; left
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard
    have hfo : f ≠ a.o := (Finset.mem_erase.mp (hf ▸ (by simp : f ∈ ({f} : Finset Plane)))).1
    exact ⟨f, by rw [← he, hf], hfo.symm⟩
  · right; right
    obtain ⟨f, g, hfg, hfgset⟩ := Finset.card_eq_two.mp hcard
    have hfo : f ≠ a.o := (Finset.mem_erase.mp (hfgset ▸ (by simp : f ∈ ({f, g} : Finset Plane)))).1
    have hgo : g ≠ a.o := (Finset.mem_erase.mp (hfgset ▸ (by simp : g ∈ ({f, g} : Finset Plane)))).1
    exact ⟨f, g, by rw [← he, hfgset], hfo.symm, hgo.symm, hfg⟩

theorem coefficient_outgoing_lower {n : ℕ} (w : DirectionWord n) (i : Fin n) (q : Finset Plane)
    (hq : wordVertex kernelStart w (i.val + 1) ∈ q) :
    betaPrimeBound (wordStraight kernelIncoming w i) ≤ pairCoefficient w i q := by
  simp only [pairCoefficient, hq, ite_true]
  split_ifs
  · exact le_rfl
  · cases hs : wordStraight kernelIncoming w i <;> norm_num [betaPrimeBound, betaBound]

theorem prefix_coefficients (hH1 : AKLT.Blueprint.Top.H1Statement)
    (p : PairSetup) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U) :
    let a := prefixDeparture p (insert p.v (protectedSites p.G)) w hw i
    let straight := wordStraight kernelIncoming (canonicalWord p.toPairData w) i
    (∀ f, a.D.presentNeighbours a.y = {a.o, f} → a.o ≠ f →
      0 < responseBetaPrime a.D a.τ a.y a.o f ∧
      responseBetaPrime a.D a.τ a.y a.o f ≤ (betaPrimeBound straight : ℝ)) ∧
    ∀ f g, a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
      0 < responseAlpha a.D a.τ a.y a.o f g ∧
      responseAlpha a.D a.τ a.y a.o f g ≤ (alphaBound straight : ℝ) ∧
      0 < responseBeta a.D a.τ a.y a.o f g ∧
      responseBeta a.D a.τ a.y a.o f g ≤ (betaBound straight : ℝ) := by
  classical
  let a := prefixDeparture p (insert p.v (protectedSites p.G)) w hw i
  have hcov := AKLT.W.REC096.main p _ n w hw i hU
  have ht := (response_typed hH1).2 a.G a.τ a.D a.auxiliary a.y a.start hU
    (wordIncoming p.incoming w i) (w i) hcov
  have ho : a.o = a.y + (w i).step := vertex_succ p.u w i.val i.isLt
  dsimp only at ht ⊢
  simp only [canonical_word_straight]
  rw [← ho] at ht
  constructor
  · intro f hs hof
    have hh := ht.1 f hs hof
    exact ⟨hh.1, by simpa only [a, wordStraight] using hh.2.1⟩
  · intro f g hs hof hog hfg
    have hh := ht.2 f g hs hof hog hfg
    exact ⟨hh.1, by simpa only [a, wordStraight] using hh.2.1,
      hh.2.2.1, by simpa only [a, wordStraight] using hh.2.2.2.1⟩

/-- The true logarithmic response is bounded by the fixed kernel's reward,
including the beta-prime versus beta comparison for a missing neighbour. -/
theorem local_log_bound (hH1 : AKLT.Blueprint.Top.H1Statement)
    (p : PairSetup) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (i : Fin n) :
    |Real.log (stepRatio (prefixNetwork p.normalized p.u w i.val) p.τ false
        (wordVertex p.u w i.val) (wordVertex p.u w (i.val + 1))) -
      Real.log (stepRatio (prefixNetwork p.normalized p.u w i.val) p.τ true
        (wordVertex p.u w i.val) (wordVertex p.u w (i.val + 1)))| ≤
      localResponseReward p.toPairData w i := by
  classical
  let a := prefixDeparture p (insert p.v (protectedSites p.G)) w hw i
  let F := canonicalChart p.toPairData
  let cw := canonicalWord p.toPairData w
  let straight := wordStraight kernelIncoming cw i
  have ho : wordVertex kernelStart cw (i.val + 1) = F.point a.o :=
    canonicalWord_vertex p.toPairData w (i.val + 1) (by omega)
  have hmapne {x z : Plane} (h : x ≠ z) : F.point x ≠ F.point z :=
    fun he => h (F.point.injective he)
  have hpresent {z : Plane} (hz : z ∈ a.D.presentNeighbours a.y) : a.D.Present a.y z :=
    (Finset.mem_filter.mp hz).2
  change |Real.log (stepRatio a.D a.τ false a.y a.o) -
    Real.log (stepRatio a.D a.τ true a.y a.o)| ≤ _
  by_cases hU : a.D.status a.y = .U
  · have ht := prefix_coefficients hH1 p w hw i hU
    rcases present_neighbour_cases a hU with hOne | ⟨f, hs, hof⟩ | ⟨f, g, hs, hof, hog, hfg⟩
    · have hh := AKLT.W.REC014.main a hU hOne
      rw [hh.1, hh.2]
      simpa only [sub_self, abs_zero] using localResponseReward_nonneg p.toPairData w i
    · have hf : a.D.Present a.y f := hpresent (by rw [hs]; simp)
      have hoP : a.D.Present a.y a.o := hpresent a.present
      have hq := pair_kernel_mem p w hw i hU hf hoP hof.symm
      have hh := (ht.1 f hs hof)
      have hc := coefficient_outgoing_lower cw i {F.point f, F.point a.o} (by rw [ho]; simp)
      have hre := reward_single_le p.toPairData w i hU _ hq
      rw [kernel_pair_signal p.toPairData w i f a.o hof.symm] at hre
      rw [AKLT.W.REC017.main a hU f hs hof, abs_mul, abs_of_pos hh.1]
      calc
        responseBetaPrime a.D a.τ a.y a.o f * |pairResponse a.D a.τ a.y f a.o| ≤
            (betaPrimeBound straight : ℝ) * |pairResponse a.D a.τ a.y f a.o| :=
          mul_le_mul_of_nonneg_right hh.2 (abs_nonneg _)
        _ ≤ (pairCoefficient cw i {F.point f, F.point a.o} : ℝ) *
            |pairResponse a.D a.τ a.y f a.o| :=
          mul_le_mul_of_nonneg_right (Rat.cast_le.mpr hc) (abs_nonneg _)
        _ ≤ _ := hre
    · have hf : a.D.Present a.y f := hpresent (by rw [hs]; simp)
      have hg : a.D.Present a.y g := hpresent (by rw [hs]; simp)
      have hoP : a.D.Present a.y a.o := hpresent a.present
      have hq₁ := pair_kernel_mem p w hw i hU hf hg hfg
      have hq₂ := pair_kernel_mem p w hw i hU hf hoP hof.symm
      have hq₃ := pair_kernel_mem p w hw i hU hg hoP hog.symm
      have hfl : F.point f ∈ liveOtherNeighbours cw i :=
        (Finset.mem_insert.mp (present_kernel_mem p w hw i hU hf)).resolve_left (by
          rw [ho]; exact hmapne hof.symm)
      have hgl : F.point g ∈ liveOtherNeighbours cw i :=
        (Finset.mem_insert.mp (present_kernel_mem p w hw i hU hg)).resolve_left (by
          rw [ho]; exact hmapne hog.symm)
      have hcard : 2 ≤ (liveOtherNeighbours cw i).card := by
        have hsub : ({F.point f, F.point g} : Finset Plane) ⊆ liveOtherNeighbours cw i :=
          by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hfl, hgl⟩
        simpa only [Finset.card_pair (hmapne hfg)] using Finset.card_le_card hsub
      have hnotone : (liveOtherNeighbours cw i).card ≠ 1 := by omega
      have hc₁ : pairCoefficient cw i {F.point f, F.point g} = alphaBound straight := by
        simp only [pairCoefficient, ho, Finset.mem_insert, Finset.mem_singleton,
          hmapne hof, hmapne hog, or_self, ite_false]
        rfl
      have hc₂ : pairCoefficient cw i {F.point f, F.point a.o} = betaBound straight := by
        simp only [pairCoefficient, ho, Finset.mem_insert, Finset.mem_singleton,
          or_true, ite_true, hnotone, ite_false]
        rfl
      have hc₃ : pairCoefficient cw i {F.point g, F.point a.o} = betaBound straight := by
        simp only [pairCoefficient, ho, Finset.mem_insert, Finset.mem_singleton,
          or_true, ite_true, hnotone, ite_false]
        rfl
      have h₁₂ : ({F.point f, F.point g} : Finset Plane) ≠ {F.point f, F.point a.o} :=
        pair_sets_ne (hmapne hfg.symm) (hmapne hog.symm)
      have h₁₃ : ({F.point f, F.point g} : Finset Plane) ≠ {F.point g, F.point a.o} := by
        rw [Finset.pair_comm (F.point f) (F.point g)]
        exact pair_sets_ne (hmapne hfg) (hmapne hof.symm)
      have h₂₃ : ({F.point f, F.point a.o} : Finset Plane) ≠ {F.point g, F.point a.o} := by
        rw [Finset.pair_comm (F.point f) (F.point a.o), Finset.pair_comm (F.point g) (F.point a.o)]
        exact pair_sets_ne (hmapne hof.symm) (hmapne hfg)
      have hre := reward_three_le p.toPairData w i hU _ _ _ hq₁ hq₂ hq₃ h₁₂ h₁₃ h₂₃
      dsimp only at hre
      rw [kernel_pair_signal p.toPairData w i f g hfg,
        kernel_pair_signal p.toPairData w i f a.o hof.symm,
        kernel_pair_signal p.toPairData w i g a.o hog.symm] at hre
      change (pairCoefficient cw i {F.point f, F.point g} : ℝ) * _ +
        (pairCoefficient cw i {F.point f, F.point a.o} : ℝ) * _ +
        (pairCoefficient cw i {F.point g, F.point a.o} : ℝ) * _ ≤ _ at hre
      rw [hc₁, hc₂, hc₃] at hre
      have hh := ht.2 f g hs hof hog hfg
      rw [AKLT.W.REC022.main a hU f g hs hof hog hfg]
      calc
        |responseAlpha a.D a.τ a.y a.o f g * pairResponse a.D a.τ a.y f g +
            responseBeta a.D a.τ a.y a.o f g *
              (pairResponse a.D a.τ a.y f a.o + pairResponse a.D a.τ a.y g a.o)| ≤
            responseAlpha a.D a.τ a.y a.o f g * |pairResponse a.D a.τ a.y f g| +
            responseBeta a.D a.τ a.y a.o f g *
              (|pairResponse a.D a.τ a.y f a.o| + |pairResponse a.D a.τ a.y g a.o|) := by
          apply (abs_add_le _ _).trans
          rw [abs_mul, abs_of_pos hh.1, abs_mul, abs_of_pos hh.2.2.1]
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left (abs_add_le _ _) (le_of_lt hh.2.2.1))
        _ ≤ (alphaBound straight : ℝ) * |pairResponse a.D a.τ a.y f g| +
            (betaBound straight : ℝ) *
              (|pairResponse a.D a.τ a.y f a.o| + |pairResponse a.D a.τ a.y g a.o|) :=
          add_le_add (mul_le_mul_of_nonneg_right hh.2.1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hh.2.2.2 (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        _ = (alphaBound straight : ℝ) * |pairResponse a.D a.τ a.y f g| +
            (betaBound straight : ℝ) * |pairResponse a.D a.τ a.y f a.o| +
            (betaBound straight : ℝ) * |pairResponse a.D a.τ a.y g a.o| := by ring
        _ ≤ _ := hre
  · have hD : a.D.status a.y = .D := by
      rcases a.start.2.2 with h | h
      · exact False.elim (hU h.1)
      · exact h.1
    have hh := AKLT.W.REC013.main a hD
    rw [hh.1, hh.2]
    simpa only [sub_self, abs_zero] using localResponseReward_nonneg p.toPairData w i

end AKLT.W.REC079
