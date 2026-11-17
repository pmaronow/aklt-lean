module
public import AKLT.W.REC099.LocalCover

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
namespace AKLT.W.REC099

open AKLT.Blueprint.Rec

def diamondOffsets : Finset Plane :=
  {(1, 0), (0, 1), (-1, 0), (0, -1),
    (2, 0), (0, 2), (-2, 0), (0, -2),
    (1, 1), (1, -1), (-1, 1), (-1, -1)}

lemma in_diamondOffsets {z e : Plane}
    (hpos : 0 < latticeDist z e) (hle : latticeDist z e ≤ 2) :
    ∃ d ∈ diamondOffsets, z = e + d := by
  rcases z with ⟨x, y⟩
  rcases e with ⟨a, b⟩
  set dx : ℤ := x - a with hdxDef
  set dy : ℤ := y - b with hdyDef
  have hsum : dx.natAbs + dy.natAbs ≤ 2 := by
    simpa [hdxDef, hdyDef, latticeDist] using hle
  have hdxNat : dx.natAbs ≤ 2 := by omega
  have hdyNat : dy.natAbs ≤ 2 := by omega
  have hdxSq : dx ^ 2 ≤ (2 : ℤ) ^ 2 := by
    have hh : dx.natAbs ≤ (2 : ℤ).natAbs := by simpa using hdxNat
    exact (Int.natAbs_le_iff_sq_le).mp hh
  have hdySq : dy ^ 2 ≤ (2 : ℤ) ^ 2 := by
    have hh : dy.natAbs ≤ (2 : ℤ).natAbs := by simpa using hdyNat
    exact (Int.natAbs_le_iff_sq_le).mp hh
  have hdxLo : -2 ≤ dx := by nlinarith [sq_nonneg (dx - 3)]
  have hdxHi : dx ≤ 2 := by nlinarith [sq_nonneg (dx + 3)]
  have hdyLo : -2 ≤ dy := by nlinarith [sq_nonneg (dy - 3)]
  have hdyHi : dy ≤ 2 := by nlinarith [sq_nonneg (dy + 3)]
  have hdist : 0 < dx.natAbs + dy.natAbs ∧ dx.natAbs + dy.natAbs ≤ 2 := by
    simpa [hdxDef, hdyDef, latticeDist] using And.intro hpos hle
  have hz : (x, y) = (a, b) + (dx, dy) := by
    simp [hdxDef, hdyDef]
  interval_cases dx <;> interval_cases dy
  all_goals norm_num [latticeDist, dx, dy] at hdist
  all_goals
    refine ⟨(dx, dy), ?_, ?_⟩
    · simp [diamondOffsets]
      omega
    · simpa [dx, dy, ← hdxDef, ← hdyDef] using hz

private lemma traceNetwork_take_succ {G : Finset Plane} (D : Network G) (xs : List Plane) :
    ∀ k, k + 1 < xs.length →
      traceNetwork D (xs.take (k + 2)) =
        traceStep (traceNetwork D (xs.take (k + 1))) xs[k]! xs[k + 1]! := by
  intro k
  induction k generalizing xs D with
  | zero =>
      intro hk
      cases xs with
      | nil => simp at hk
      | cons a xs =>
        cases xs with
        | nil => simp at hk
        | cons b rest => simp [traceNetwork]
  | succ k ih =>
      intro hk
      cases xs with
      | nil => simp at hk
      | cons a xs =>
        cases xs with
        | nil => simp at hk
        | cons b rest =>
          have hk' : k + 1 < (b :: rest).length := by simp at hk ⊢; omega
          have hh := ih (traceStep D a b) (b :: rest) hk'
          simpa [traceNetwork] using hh

private lemma prefixNetwork_succ {G : Finset Plane} (D : Network G) (u : Plane)
    {n : ℕ} (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  have hlen : j + 1 < (wordVertices u w).length := by
    simp [wordVertices]
    omega
  have hh := traceNetwork_take_succ D (wordVertices u w) j hlen
  have h0 : (wordVertices u w)[j]! = wordVertex u w j := by
    simp only [wordVertices, List.getElem!_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_range (by omega)]
    rfl
  have h1 : (wordVertices u w)[j + 1]! = wordVertex u w (j + 1) := by
    simp only [wordVertices, List.getElem!_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_range (by omega)]
    rfl
  simpa [prefixNetwork, h0, h1, Nat.add_assoc] using hh

private lemma traceStep_preserves_notU {G : Finset Plane} (D : Network G) (x y o : Plane)
    (h : D.status x ≠ .U) : (traceStep D y o).status x ≠ .U := by
  by_cases hxy : x = y
  · subst x
    simp [traceStep, h]
  · simp [traceStep, hxy, h]

private lemma traceStep_departure_notU {G : Finset Plane} (D : Network G) (y o : Plane)
    (h : D.status y = .U) : (traceStep D y o).status y ≠ .U := by
  simp [traceStep, h]

private lemma prefix_status_nonU_of_le {G : Finset Plane} (D : Network G) (u : Plane)
    {n : ℕ} (w : DirectionWord n) (x : Plane) :
    ∀ {i j : ℕ}, i ≤ j → j < n →
      (prefixNetwork D u w i).status x ≠ .U →
      (prefixNetwork D u w j).status x ≠ .U := by
  intro i j
  induction j generalizing i with
  | zero =>
      intro hij hj hstart
      have hi : i = 0 := by omega
      simpa [hi] using hstart
  | succ j ih =>
      intro hij hj hstart
      by_cases heq : i = j + 1
      · simpa [heq] using hstart
      · have hij' : i ≤ j := by omega
        have hj' : j < n := by omega
        have hprev := ih hij' hj' hstart
        rw [show j + 1 = j.succ by omega]
        rw [prefixNetwork_succ D u w j hj']
        exact traceStep_preserves_notU _ _ _ _ hprev

theorem uDepartureInjective :
    ∀ G : Finset Plane, ∀ D : Network G, ∀ u : Plane, ∀ T : Finset Plane,
      ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u T w → ∀ i j : Fin n,
        (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U →
        (prefixNetwork D u w j.val).status (wordVertex u w j.val) = .U →
        wordVertex u w i.val = wordVertex u w j.val → i = j := by
  intro G D u T n w _ i j hi hj hvertex
  by_cases hEq : i = j
  · exact hEq
  · have hvals : i.val ≠ j.val := by
      intro h
      exact hEq (Fin.ext h)
    have horder : i.val < j.val ∨ j.val < i.val := by omega
    rcases horder with hij | hji
    · have hstart : (prefixNetwork D u w (i.val + 1)).status
          (wordVertex u w i.val) ≠ .U := by
        rw [prefixNetwork_succ D u w i.val i.isLt]
        exact traceStep_departure_notU _ _ _ hi
      have hlater := prefix_status_nonU_of_le D u w (wordVertex u w i.val)
        (i := i.val + 1) (j := j.val) (by omega) j.isLt hstart
      rw [hvertex] at hlater
      exact False.elim (hlater hj)
    · have hstart : (prefixNetwork D u w (j.val + 1)).status
          (wordVertex u w j.val) ≠ .U := by
        rw [prefixNetwork_succ D u w j.val j.isLt]
        exact traceStep_departure_notU _ _ _ hj
      have hlater := prefix_status_nonU_of_le D u w (wordVertex u w j.val)
        (i := j.val + 1) (j := i.val) (by omega) i.isLt hstart
      rw [← hvertex] at hlater
      exact False.elim (hlater hi)

/-- Uncovered U departures inject into the twelve sites at positive distance
at most two from the first protected terminal. -/
theorem main : AKLT.Blueprint.Rec.TerminalExceptionCountStatementV2 := by
  intro p hv n w hw he
  dsimp
  intro incoming hincoming m w' hw'
  classical
  let e := wordVertex p.u w n
  let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
  let bad : Finset (Fin m) := Finset.univ.filter fun i =>
    (prefixNetwork E p.v w' i.val).status (wordVertex p.v w' i.val) = .U ∧
      ¬ AKLT.Defs.CoveredDepartureV2 (prefixNetwork E p.v w' i.val) (wordVertex p.v w' i.val)
        (wordIncoming incoming w' i) (w' i)
  let diamondSites : Finset Plane := diamondOffsets.image (fun d => e + d)
  have hsub : bad.image (fun i => wordVertex p.v w' i.val) ⊆ diamondSites := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hmem := Finset.mem_filter.mp hi
    have hfar : ¬ 2 < latticeDist (wordVertex p.v w' i.val) e := by
      intro hfar
      have hcov := terminalLocalCover p hv n w hw he incoming hincoming m w' hw' i
        hmem.2.1 hfar
      exact hmem.2.2 hcov
    have hle : latticeDist (wordVertex p.v w' i.val) e ≤ 2 := by omega
    have havoid := hw'.2.2.1 i.val i.isLt
    have hne : wordVertex p.v w' i.val ≠ e := by
      intro heq
      rw [heq] at havoid
      exact havoid.2 he
    have hpos : 0 < latticeDist (wordVertex p.v w' i.val) e := by
      by_contra hnot
      have hzero : latticeDist (wordVertex p.v w' i.val) e = 0 := by omega
      have hcoords : wordVertex p.v w' i.val = e := by
        have hzero' : ((wordVertex p.v w' i.val).1 - e.1).natAbs +
            ((wordVertex p.v w' i.val).2 - e.2).natAbs = 0 := by
          simpa [latticeDist] using hzero
        have hxy : (wordVertex p.v w' i.val).1 - e.1 = 0 ∧
            (wordVertex p.v w' i.val).2 - e.2 = 0 := by
          simpa using hzero'
        exact Prod.ext (by omega) (by omega)
      exact hne hcoords
    rcases in_diamondOffsets hpos hle with ⟨d, hd, heq⟩
    exact Finset.mem_image.mpr ⟨d, hd, heq.symm⟩
  have hinj : Set.InjOn (fun i : Fin m => wordVertex p.v w' i.val) bad := by
    intro i hi j hj hij
    exact uDepartureInjective p.G E p.v (protectedSites p.G) m w' hw' i j
      (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hj).2.1 hij
  have hcardImage : bad.card ≤ (bad.image (fun i => wordVertex p.v w' i.val)).card := by
    rw [Finset.card_image_iff.mpr]
    intro i hi j hj hij
    exact hinj hi hj hij
  have hcardDiamond : diamondSites.card = 12 := by
    dsimp [diamondSites]
    rw [Finset.card_image_iff.mpr]
    · norm_num [diamondOffsets]
    · intro d hd d' hd' heq
      exact add_left_cancel heq
  have hcard := hcardImage.trans (Finset.card_le_card hsub)
  have hfinal : bad.card ≤ 12 := by omega
  simpa [uncoveredCountV2, bad, E] using hfinal

end AKLT.W.REC099

#print axioms AKLT.W.REC099.in_diamondOffsets
#print axioms AKLT.W.REC099.uDepartureInjective
#print axioms AKLT.W.REC099.main
