import AKLT.W.H1C020.RingFubini

/-! Proof of the first residual, `Residual_ringFubini`. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

variable {π : PatternData} {r : Representation}

lemma mem_centerIds {ss : List PackedSite} {i : Nat}
    (h : i ∈ ((List.range ss.length).zip ss).filterMap
      (fun (p : Nat × PackedSite) => if p.2.spec.center then some p.1 else none)) :
    ∃ hi : i < ss.length, (ss[i]).spec.center = true := by
  obtain ⟨p, hp, hpi⟩ := List.mem_filterMap.mp h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
  have hj' : j < ss.length := by simpa using hj
  simp only [List.getElem_zip, List.getElem_range] at hpi
  split at hpi
  · rename_i hc
    simp only [Option.some.injEq] at hpi
    subst hpi
    exact ⟨hj', hc⟩
  · simp at hpi

lemma mem_centerPairs {ss : List PackedSite} {x y : Nat} (h : (x,y) ∈ centerPairs ss) :
    (∃ hx : x < ss.length, (ss[x]).spec.center = true) ∧
      (∃ hy : y < ss.length, (ss[y]).spec.center = true) := by
  unfold centerPairs at h
  simp only at h
  obtain ⟨x', hx', hxy⟩ := List.mem_flatMap.mp h
  obtain ⟨y', hy', hxy'⟩ := List.mem_filterMap.mp hxy
  split at hxy'
  · simp only [Option.some.injEq, Prod.mk.injEq] at hxy'
    obtain ⟨rfl, rfl⟩ := hxy'
    exact ⟨mem_centerIds hx', mem_centerIds hy'⟩
  · simp at hxy'

lemma codesOK_of_centerCode {I : Finset (Fin 20)} {ss : List PackedSite}
    (hg : NetworkGeometry π r I ss) (codes : List Nat) (hc : CenterCode ss codes) :
    CodesOK π codes := by
  intro i hi
  rcases hc with rfl | ⟨⟨x, y⟩, hxy, k, hk, rfl⟩
  · simp
  · have hlen : ss.length = 8 := hg.1
    have hget : (centerCodes ss.length x y (k+1)).getD i 0 =
        if i == x || i == y then k+1 else 0 := by
      unfold centerCodes
      rw [getD_range_map _ _ _ _ (by omega)]
    rw [hget]
    refine ⟨by split <;> omega, ?_⟩
    intro hne
    have hixy : i = x ∨ i = y := by
      by_contra hn
      simp only [not_or] at hn
      apply hne
      simp [hn.1, hn.2]
    obtain ⟨⟨hx, hcx⟩, ⟨hy, hcy⟩⟩ := mem_centerPairs hxy
    rcases hixy with rfl | rfl
    · rw [← (siteFlags_of_geometry hg i hx).center]
      exact hcx
    · rw [← (siteFlags_of_geometry hg i hy).center]
      exact hcy

lemma status_moment_of_flag (x : Plane) (s : SiteSpec)
    (h : s.diluted = true ↔ π.statusAt x = .D) (m : Fin 3 → ℕ) :
    rationalStatusMoment (π.statusAt x) m =
      rationalStatusMoment (if s.diluted then .D else .U) m := by
  cases hst : π.statusAt x <;> cases hd : s.diluted <;> simp_all [rationalStatusMoment]

lemma ringV_subset_ringSet : ringV π r ⊆ ringSet 0 8 := by
  intro x hx
  have hxV := (Finset.mem_erase.mp hx).2
  have hx0 := (Finset.mem_erase.mp hx).1
  rw [mem_reducedSpinSites] at hxV
  have hts : x ∈ templateSites := (Finset.mem_filter.mp hxV.1).1
  rcases AKLT.W.H1C031.templateSite_cases hts with h | h | h
  · exact absurd h hx0
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
    rw [mem_ringSet]
    refine ⟨i, by simpa [ringSites] using hi, ?_⟩
    rw [zero_add]
    unfold ptOf
    rw [List.getD_eq_getElem _ _ hi]
  · exact absurd h hxV.2.1

/-- First residual: the ring Fubini identity. -/
theorem ringFubini_holds : Residual_ringFubini := by
  intro π _ r I _ ss hg codes hcc
  have hok := codesOK_of_centerCode hg codes hcc
  have hlen : (eraseNetworkInversion ss).length = 8 := by
    simp [eraseNetworkInversion, hg.1]
  have hloc : ∀ i (hi : i < (eraseNetworkInversion ss).length), ∀ l r' v,
      contractSpins {ptOf (0+i)} π.statusAt
          (gLoc (0+i) ((eraseNetworkInversion ss)[i]).spec l r' v) =
        rationalLocal (0+i) ((eraseNetworkInversion ss)[i]).spec l r' v := by
    intro i hi l r' v
    have hi' : i < ss.length := by simpa [eraseNetworkInversion] using hi
    have hspec : ((eraseNetworkInversion ss)[i]).spec = eraseInversion (ss[i]).spec := by
      simp [eraseNetworkInversion]
    rw [zero_add, hspec]
    apply contract_gLoc
    exact status_moment_of_flag _ _ (siteFlags_of_geometry hg i hi').diluted
  have hT : ∀ a, openTransfer rationalLocal 0 (eraseNetworkInversion ss) codes a a =
      contractSpins (ringSet 0 8) π.statusAt (openL gLoc 0 (eraseNetworkInversion ss) codes a a) := by
    intro a
    have h := contract_openL gLoc rationalLocal π.statusAt varsIn_gLoc
      (eraseNetworkInversion ss) 0 codes a a (by omega) hloc
    rw [hlen] at h
    exact h.symm
  unfold closedTransfer
  simp only [hT]
  have hsum : ((List.range 4).map fun a => contractSpins (ringSet 0 8) π.statusAt
      (openL gLoc 0 (eraseNetworkInversion ss) codes a a)).sum =
      contractSpins (ringSet 0 8) π.statusAt
        (((List.range 4).map fun a => openL gLoc 0 (eraseNetworkInversion ss) codes a a).sum) := by
    rw [contractSpins_listSum, List.map_map]
    rfl
  rw [hsum]
  change contractSpins (ringSet 0 8) π.statusAt (closedL gLoc (eraseNetworkInversion ss) codes) = _
  rw [closedL_eq hg codes hok]
  unfold ringPolynomial insertedRingIntegrand
  rw [ringIntegrand_eq, contractSpins_superset ringV_subset_ringSet _ _
    (varsIn_ringPart.mul (varsIn_insertion codes hok)).supported]
  rfl

end AKLT.W.H1C020
