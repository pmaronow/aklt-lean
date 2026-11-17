module
public import AKLT.Blueprint.Rec.NodesWalk

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC045

lemma traceStep_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  intro x hx
  simp only [Network.active, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxG, hxst⟩
  refine ⟨hxG, ?_⟩
  by_cases hxy : x = y
  · subst x
    cases hs : D.status y <;> simp [traceStep, hs] at hxst ⊢
  · simpa [traceStep, hxy] using hxst

lemma traceStep_present_imp {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (h : (traceStep D y o).Present x z) : D.Present x z := by
  rcases h with ⟨hx, hz, hadj, hxk, hzk⟩
  refine ⟨traceStep_active_subset D y o hx, traceStep_active_subset D y o hz, hadj, ?_, ?_⟩
  · by_cases hxy : x = y
    · subst x
      simp only [traceStep] at hxk
      exact Finset.mem_of_mem_erase hxk
    · by_cases hxo : x = o
      · subst x
        simp only [traceStep, if_neg hxy] at hxk
        exact Finset.mem_of_mem_erase hxk
      · simpa [traceStep, hxy, hxo] using hxk
  · by_cases hzy : z = y
    · subst z
      simp only [traceStep] at hzk
      exact Finset.mem_of_mem_erase hzk
    · by_cases hzo : z = o
      · subst z
        simp only [traceStep, if_neg hzy] at hzk
        exact Finset.mem_of_mem_erase hzk
      · simpa [traceStep, hzy, hzo] using hzk

lemma traceStep_neighbours_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x := by
  intro z hz
  simp only [Network.presentNeighbours, Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, traceStep_present_imp D y o x z hz.2⟩

lemma traceStep_factorDegree_le {G : Finset Plane} (D : Network G) (y o x : Plane) :
    AKLT.Blueprint.Rec.factorDegree (traceStep D y o) x ≤ AKLT.Blueprint.Rec.factorDegree D x := by
  unfold AKLT.Blueprint.Rec.factorDegree
  exact Nat.add_le_add_right (Finset.card_le_card (traceStep_neighbours_subset D y o x)) _

lemma traceNetwork_active_subset {G : Finset Plane} (D : Network G) (xs : List Plane) :
    (traceNetwork D xs).active ⊆ D.active := by
  induction xs generalizing D with
  | nil => simp [traceNetwork]
  | cons y xs ih =>
      cases xs with
      | nil => simp [traceNetwork]
      | cons o rest =>
          simp only [traceNetwork]
          exact (ih (traceStep D y o)).trans (traceStep_active_subset D y o)

lemma traceNetwork_factorDegree_le {G : Finset Plane} (D : Network G) (xs : List Plane) (x : Plane) :
    AKLT.Blueprint.Rec.factorDegree (traceNetwork D xs) x ≤ AKLT.Blueprint.Rec.factorDegree D x := by
  induction xs generalizing D with
  | nil => simp [traceNetwork]
  | cons y xs ih =>
      cases xs with
      | nil => simp [traceNetwork]
      | cons o rest =>
          simp only [traceNetwork]
          exact (ih (traceStep D y o)).trans (traceStep_factorDegree_le D y o x)

lemma traceNetwork_neighbours_subset {G : Finset Plane} (D : Network G) (xs : List Plane)
    (x : Plane) :
    (traceNetwork D xs).presentNeighbours x ⊆ D.presentNeighbours x := by
  induction xs generalizing D with
  | nil => simp [traceNetwork]
  | cons y xs ih =>
      cases xs with
      | nil => simp [traceNetwork]
      | cons o rest =>
          simp only [traceNetwork]
          exact (ih (traceStep D y o)).trans (traceStep_neighbours_subset D y o x)

lemma traceNetwork_append_pair {G : Finset Plane} (D : Network G) (xs : List Plane)
    (y x : Plane) :
    traceNetwork D (xs ++ [y, x]) = traceStep (traceNetwork D (xs ++ [y])) y x := by
  induction xs generalizing D with
  | nil => simp [traceNetwork]
  | cons a xs ih =>
      cases xs with
      | nil => simp [traceNetwork]
      | cons b rest =>
          simp only [List.cons_append, traceNetwork]
          exact ih (traceStep D a b)

lemma traceStep_notPresent_arrival {G : Finset Plane} (D : Network G) (y o : Plane) :
    ¬ (traceStep D y o).Present o y := by
  simp [Network.Present, traceStep]

lemma wordVertices_getElem {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ)
    (hj : j ≤ n) :
    (wordVertices u w)[j]'(by simp [wordVertices]; omega) = wordVertex u w j := by
  simp [wordVertices]

lemma prefixNetwork_arrival_absent {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    ¬ (prefixNetwork D u w j).Present (wordVertex u w j) (wordVertex u w (j - 1)) := by
  cases j with
  | zero => omega
  | succ k =>
      let vs := wordVertices u w
      have hlen : k + 1 < vs.length := by simp [vs, wordVertices]; omega
      have hlenPrev : k < vs.length := by omega
      have htakePrev : vs.take k ++ [vs[k]] = vs.take (k + 1) :=
        List.take_append_getElem (i := k) hlenPrev
      have hsuffix : vs.take (k + 1 + 1) = vs.take k ++ [vs[k], vs[k + 1]] := by
        calc
          vs.take (k + 1 + 1) = vs.take (k + 1) ++ [vs[k + 1]] := by
            exact List.take_succ_eq_append_getElem (i := k + 1) hlen
          _ = vs.take k ++ [vs[k], vs[k + 1]] := by
            rw [← htakePrev]
            rw [List.append_assoc]
            rfl
      have hvertsPrev : vs[k] = wordVertex u w k := wordVertices_getElem u w k (by omega)
      have hvertsj : vs[k + 1] = wordVertex u w (k + 1) :=
        wordVertices_getElem u w (k + 1) (by omega)
      rw [show prefixNetwork D u w (k + 1) = traceNetwork D (vs.take (k + 1 + 1)) by rfl,
        hsuffix, hvertsPrev, hvertsj, traceNetwork_append_pair]
      exact traceStep_notPresent_arrival _ _ _

lemma adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  change latticeDist x y = 1 at h
  change latticeDist y x = 1
  unfold latticeDist at h ⊢
  rw [show y.1 - x.1 = -(x.1 - y.1) by ring,
    show y.2 - x.2 = -(x.2 - y.2) by ring,
    Int.natAbs_neg, Int.natAbs_neg]
  exact h

lemma present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  rcases h with ⟨hx, hy, hadj, hyx, hxy⟩
  exact ⟨hy, hx, adjacent_symm hadj, hxy, hyx⟩

lemma adjacent_of_mem_neighbours {x z : Plane} (h : z ∈ neighbours x) : Adjacent x z := by
  rcases Finset.mem_image.mp h with ⟨d, hd, hdz⟩
  subst z
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

lemma protected_of_originalLeg {G : Finset Plane} {x : Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) (hfirst : e.1 = x) : x ∈ protectedSites G := by
  rcases Finset.mem_biUnion.mp he with ⟨a, ha, hea⟩
  rcases Finset.mem_image.mp hea with ⟨z, hz, heq⟩
  have hax : a = x := (congrArg Prod.fst heq).trans hfirst
  subst a
  have hzout : z ∉ G := (Finset.mem_sdiff.mp hz).2
  have hadj : Adjacent x z := adjacent_of_mem_neighbours (Finset.mem_sdiff.mp hz).1
  have hbd : boundaryDepth G x ≤ 2 := by
    calc
      boundaryDepth G x ≤ (latticeDist x z : ℕ∞) := by
        unfold boundaryDepth setDistance
        exact iInf_le (fun q : {q : Plane // q ∉ G} => (latticeDist x q.val : ℕ∞)) ⟨z, hzout⟩
      _ = 1 := by exact_mod_cast hadj
      _ ≤ 2 := by norm_num
  simp only [protectedSites, Finset.mem_filter]
  exact ⟨ha, hbd⟩

lemma originalLegs_card_eq_zero_of_not_protected {G : Finset Plane} {x : Plane}
    (hx : x ∉ protectedSites G) :
    ((originalLegs G).filter fun e => e.1 = x).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro e he hfirst
  exact hx (protected_of_originalLeg he hfirst)

lemma aux_factorDegree_le_four {G : Finset Plane} {D : Network G} (hD : D.Auxiliary)
    {x : Plane} (hx : x ∈ D.active) : AKLT.Blueprint.Rec.factorDegree D x ≤ 4 := by
  unfold AKLT.Blueprint.Rec.factorDegree
  exact hD.1.2.2.2 x hx

lemma target_factorDegree_le_three {G : Finset Plane} {D : Network G} (hD : D.Auxiliary)
    {v : Plane} (hv : AdmissibleTarget D v) :
    AKLT.Blueprint.Rec.factorDegree D v ≤ 3 := by
  rcases hv.2 with ⟨hstatus, hdeg⟩ | ⟨hstatus, hdeg⟩
  · unfold AKLT.Blueprint.Rec.factorDegree
    exact hdeg
  · have hvnot : v ∉ protectedSites G := by
      intro hp
      have hs := hD.2 v hp
      rw [hstatus] at hs
      contradiction
    have hlegs := originalLegs_card_eq_zero_of_not_protected hvnot
    unfold AKLT.Blueprint.Rec.factorDegree
    rw [hlegs]
    omega

lemma start_factorDegree_le_three {G : Finset Plane} {D : Network G}
    {u : Plane} (hu : D.AdmissibleStart u) :
    AKLT.Blueprint.Rec.factorDegree D u ≤ 3 := by
  have hlegs := originalLegs_card_eq_zero_of_not_protected hu.2.1
  unfold AKLT.Blueprint.Rec.factorDegree
  rw [hlegs]
  rcases hu.2.2 with ⟨_, hdeg⟩ | ⟨_, hdeg⟩ <;> omega

lemma factorDegree_drop_neighbor {G : Finset Plane} (D E : Network G) (x z : Plane)
    (hsub : E.presentNeighbours x ⊆ D.presentNeighbours x)
    (hzD : z ∈ D.presentNeighbours x) (hzE : z ∉ E.presentNeighbours x) :
    AKLT.Blueprint.Rec.factorDegree E x + 1 ≤ AKLT.Blueprint.Rec.factorDegree D x := by
  have hnotSub : ¬ D.presentNeighbours x ⊆ E.presentNeighbours x := by
    intro hrev
    exact hzE (hrev hzD)
  have hcardlt : (E.presentNeighbours x).card < (D.presentNeighbours x).card :=
    Finset.card_lt_card ⟨hsub, hnotSub⟩
  have hcard' : (E.presentNeighbours x).card + 1 ≤ (D.presentNeighbours x).card :=
    Nat.succ_le_iff.mpr hcardlt
  unfold AKLT.Blueprint.Rec.factorDegree
  calc
    (E.presentNeighbours x).card +
        ((originalLegs G).filter fun e => e.1 = x).card + 1 =
      ((E.presentNeighbours x).card + 1) +
        ((originalLegs G).filter fun e => e.1 = x).card := by omega
    _ ≤ (D.presentNeighbours x).card +
        ((originalLegs G).filter fun e => e.1 = x).card :=
      Nat.add_le_add_right hcard' _

lemma prefixNetwork_zero {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) : prefixNetwork D u w 0 = D := by
  have hrange : (List.range (n + 1)).take 1 = [0] := by
    rw [List.range_succ_eq_map]
    simp
  have hvertices : (wordVertices u w).take 1 = [u] := by
    unfold wordVertices
    rw [← List.map_take, hrange]
    simp [wordVertex]
  simp [prefixNetwork, hvertices, traceNetwork]

theorem main : AKLT.Blueprint.Rec.PairDegreeStatement := by
  intro G D hD u v hu hv huv n w htrail j hj x hx
  let E : Network G := prefixNetwork D u w j
  let live : Plane := wordVertex u w j
  change AKLT.Blueprint.Rec.factorDegree E x +
    (if x = live then 1 else 0) + (if x = v then 1 else 0) ≤ 4
  have hbase : AKLT.Blueprint.Rec.factorDegree E x ≤ 4 := by
    have hxE : x ∈ E.active := hx
    have hxD : x ∈ D.active := by
      change x ∈ (traceNetwork D ((wordVertices u w).take (j + 1))).active at hxE
      exact traceNetwork_active_subset D ((wordVertices u w).take (j + 1)) hxE
    calc
      AKLT.Blueprint.Rec.factorDegree E x ≤ AKLT.Blueprint.Rec.factorDegree D x := by
        change AKLT.Blueprint.Rec.factorDegree
          (traceNetwork D ((wordVertices u w).take (j + 1))) x ≤ _
        exact traceNetwork_factorDegree_le D ((wordVertices u w).take (j + 1)) x
      _ ≤ 4 := aux_factorDegree_le_four hD hxD
  have htargetBase : AKLT.Blueprint.Rec.factorDegree E v ≤ 3 := by
    calc
      AKLT.Blueprint.Rec.factorDegree E v ≤ AKLT.Blueprint.Rec.factorDegree D v := by
        change AKLT.Blueprint.Rec.factorDegree
          (traceNetwork D ((wordVertices u w).take (j + 1))) v ≤ _
        exact traceNetwork_factorDegree_le D ((wordVertices u w).take (j + 1)) v
      _ ≤ 3 := target_factorDegree_le_three hD hv
  have hdrop : 0 < j →
      AKLT.Blueprint.Rec.factorDegree E live + 1 ≤ AKLT.Blueprint.Rec.factorDegree D live := by
    intro hjpos
    let prev := wordVertex u w (j - 1)
    let i : Fin n := ⟨j - 1, by omega⟩
    have hstep : D.Present prev live := by
      have hp := htrail.2.1 i
      simpa [prev, live, i, Nat.sub_add_cancel (by omega : 1 ≤ j)] using hp
    have hrev := present_symm D hstep
    rcases hrev with ⟨_, _, _, hprevKept, _⟩
    have hprevNbr : prev ∈ neighbours live :=
      (Finset.mem_inter.mp (hD.1.2.1 live hprevKept)).1
    have hprevD : prev ∈ D.presentNeighbours live := by
      exact Finset.mem_filter.mpr ⟨hprevNbr, present_symm D hstep⟩
    have hnot : ¬ E.Present live prev := by
      have h := prefixNetwork_arrival_absent D u w hjpos hj
      simpa [E, live, prev] using h
    have hprevE : prev ∉ E.presentNeighbours live := by
      intro he
      exact hnot (Finset.mem_filter.mp he).2
    have hsub : E.presentNeighbours live ⊆ D.presentNeighbours live := by
      change (traceNetwork D ((wordVertices u w).take (j + 1))).presentNeighbours live ⊆ _
      exact traceNetwork_neighbours_subset D ((wordVertices u w).take (j + 1)) live
    exact factorDegree_drop_neighbor D E live prev hsub hprevD hprevE
  by_cases hend : x = live
  · subst x
    by_cases htarget : live = v
    · by_cases hjzero : j = 0
      · have hlive : live = u := by simp [live, hjzero, wordVertex]
        exact (huv (hlive.symm.trans htarget)).elim
      · have hdrop' := hdrop (by omega)
        have htargetD : AKLT.Blueprint.Rec.factorDegree D live ≤ 3 := by
          simpa [htarget] using target_factorDegree_le_three hD hv
        have hb : AKLT.Blueprint.Rec.factorDegree E live + 1 ≤ 3 := le_trans hdrop' htargetD
        rw [if_pos (show live = live from rfl), if_pos htarget]
        omega
    · by_cases hjzero : j = 0
      · have hlive : live = u := by simp [live, hjzero, wordVertex]
        have hE : E = D := by simp [E, hjzero, prefixNetwork_zero]
        have hb : AKLT.Blueprint.Rec.factorDegree E live ≤ 3 := by
          rw [hE, hlive]
          exact start_factorDegree_le_three hu
        simp [htarget]
        omega
      · have hdrop' := hdrop (by omega)
        have hliveD : live ∈ D.active := by
          have : live ∈ E.active := by simpa [E, live] using hx
          change live ∈ (traceNetwork D ((wordVertices u w).take (j + 1))).active at this
          exact traceNetwork_active_subset D ((wordVertices u w).take (j + 1)) this
        have hDfour := aux_factorDegree_le_four hD hliveD
        have hb : AKLT.Blueprint.Rec.factorDegree E live + 1 ≤ 4 := le_trans hdrop' hDfour
        simp [htarget]
        omega
  · by_cases hxv : x = v
    · have hb : AKLT.Blueprint.Rec.factorDegree E x ≤ 3 := by
        rw [hxv]
        exact htargetBase
      simp only [if_neg hend, if_pos hxv]
      omega
    · simp [hend, hxv]
      exact hbase

end AKLT.W.REC045
