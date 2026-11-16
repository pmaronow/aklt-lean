import AKLT.W.REC079.LocalLogComparison
import AKLT.W.REC079.ExposureAlgebra
import AKLT.W.REC041.Main
import AKLT.W.REC010.Main
import AKLT.W.REC011.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

open AKLT.W.REC096

theorem prefix_ratio_le (hH1 : AKLT.Blueprint.Top.H1Statement)
    (p : PairSetup) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (i : Fin n) :
    stepRatio (prefixNetwork p.normalized p.u w i.val) p.τ true
      (wordVertex p.u w i.val) (wordVertex p.u w (i.val + 1)) ≤
        (passageFactor (wordStraight kernelIncoming (canonicalWord p.toPairData w) i) : ℝ) := by
  let a := prefixDeparture p (insert p.v (protectedSites p.G)) w hw i
  change stepRatio a.D a.τ true a.y a.o ≤ _
  by_cases hU : a.D.status a.y = .U
  · have hcov := AKLT.W.REC096.main p _ n w hw i hU
    have ho : a.o = a.y + (w i).step := vertex_succ p.u w i.val i.isLt
    rw [canonical_word_straight]
    exact covered_ratio hH1 a hU (wordIncoming p.incoming w i) (w i) ho hcov
  · have hD : a.D.status a.y = .D := by
      rcases a.start.2.2 with h | h
      · exact False.elim (hU h.1)
      · exact h.1
    rw [(AKLT.W.REC013.main a hD).1]
    exact passageFactor_one_le _

/-- Ordered exposure in the fixed short/long order. True U indices supply
the rewards; every appended revisit has reward zero. -/
theorem ordered_exposure : Residual_OrderedExposureV2 := by
  classical
  intro hH1 p n w hw hend
  by_cases hn : n = 0
  · subst n
    exact False.elim (responsePair_endpoints_ne p (by simpa only [vertex_zero] using hend))
  have hpos := Nat.pos_of_ne_zero hn
  have hu : p.u ∉ protectedSites p.G := by
    simpa only [vertex_zero] using (hw.2.2.1 0 hpos).2
  let ps := pairSetup p hu
  let cw := canonicalWord p w
  let r (b : Bool) (i : Fin n) : ℝ := stepRatio (prefixNetwork p.normalized p.u w i.val) p.τ b
    (wordVertex p.u w i.val) (wordVertex p.u w (i.val + 1))
  have hr (i : Fin n) : 0 < r true i ∧ 0 < r false i ∧ r false i ≤ 1 ∧
      r true i ≤ (passageFactor (wordStraight kernelIncoming cw i) : ℝ) ∧
      |Real.log (r false i) - Real.log (r true i)| ≤ localResponseReward p w i := by
    let a := prefixDeparture ps (insert p.v (protectedSites p.G)) w hw i
    exact ⟨AKLT.W.REC010.main a true, AKLT.W.REC010.main a false, AKLT.W.REC011.main a,
      prefix_ratio_le hH1 ps w hw i, local_log_bound hH1 ps w hw i⟩
  have he := products_le_realExposure cw (r true) (r false) (localResponseReward p w) hr
    (localResponseReward_nonneg p w) (fullOrdering cw)
  let a₀ := prefixDeparture ps (insert p.v (protectedSites p.G)) w hw ⟨0, hpos⟩
  have haux : p.normalized.Auxiliary := by
    have hh := a₀.auxiliary
    change (prefixNetwork p.normalized p.u w 0).Auxiliary at hh
    rwa [prefix_zero] at hh
  have hstart : p.normalized.AdmissibleStart p.u := by
    have hh := a₀.start
    change (prefixNetwork p.normalized p.u w 0).AdmissibleStart (wordVertex p.u w 0) at hh
    simpa only [prefix_zero, vertex_zero] using hh
  have hratio (b : Bool) : traceRatio p.normalized p.τ b (wordVertices p.u w) =
      ((fullOrdering cw).map (r b)).prod := by
    rw [AKLT.W.REC041.main p.G p.τ p.normalized haux p.u hstart _ n w hw b]
    change (∏ i, r b i) = _
    rw [Fin.prod_univ_def]
    exact ((fullOrdering_perm cw (kernelOrdering_perm cw)).map (r b)).prod_eq.symm
  rw [hratio true, hratio false]
  have ht : realExposure cw (localResponseReward p w)
      ((List.finRange n).filter (wordRevisit kernelStart cw)) = 0 := by
    apply realExposure_zero
    intro i hi
    have hrev := (List.mem_filter.mp hi).2
    have hnotU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) ≠ .U := by
      intro hU
      have hfirst := U_departure_canonical_first_visit p w i hU
      change wordRevisit kernelStart cw i = false at hfirst
      rw [hfirst] at hrev
      contradiction
    simp only [localResponseReward]
    rw [if_neg hnotU]
  simpa only [fullOrdering, realExposure_append cw _ _ _ ht] using he

end AKLT.W.REC079
