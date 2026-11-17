module
public import AKLT.Blueprint.Rec.NodesClosure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC051

private theorem traceNetwork_append_pair {G : Finset Plane} (D : Network G) (xs : List Plane)
    (y z : Plane) :
    traceNetwork D (xs ++ [y, z]) =
      traceStep (traceNetwork D (xs ++ [y])) y z := by
  induction xs generalizing D with
  | nil => rfl
  | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b xs =>
          simp only [List.cons_append, traceNetwork]
          simpa only [List.cons_append, traceNetwork] using
            ih (D := traceStep D a b)

private theorem wordVertices_length {n : ℕ} (u : Plane) (w : DirectionWord n) :
    (wordVertices u w).length = n + 1 := by
  simp [wordVertices]

private theorem wordVertices_getElem {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j ≤ n) :
    (wordVertices u w)[j]'(by simp [wordVertices]; omega) = wordVertex u w j := by
  simp [wordVertices]

private theorem wordVertices_take_succ {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j ≤ n) :
    (wordVertices u w).take (j + 1) =
      (wordVertices u w).take j ++ [wordVertex u w j] := by
  have hlt : j < (wordVertices u w).length := by
    rw [wordVertices_length]
    omega
  rw [List.take_succ_eq_append_getElem hlt, wordVertices_getElem u w j hj]

private theorem prefixNetwork_succ {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j + 1 ≤ n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  have hj' : j ≤ n := by omega
  have hj1 : j + 1 ≤ n := hj
  rw [prefixNetwork, prefixNetwork]
  rw [wordVertices_take_succ u w (j + 1) hj1,
    wordVertices_take_succ u w j hj']
  rw [List.append_assoc]
  change traceNetwork D ((wordVertices u w).take j ++
      [wordVertex u w j, wordVertex u w (j + 1)]) = _
  exact traceNetwork_append_pair D ((wordVertices u w).take j)
    (wordVertex u w j) (wordVertex u w (j + 1))
  

private theorem prefixNetwork_zero {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n) :
    prefixNetwork D u w 0 = D := by
  simp [prefixNetwork, wordVertices, List.range_succ_eq_map, wordVertex, traceNetwork]

private theorem adjacent_mem_neighbors {x y : Plane} (h : Adjacent x y) :
    y ∈ neighbors x := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  change (x₁ - y₁).natAbs + (x₂ - y₂).natAbs = 1 at h
  have h₁ : (x₁ - y₁).natAbs = 1 ∨ (x₂ - y₂).natAbs = 1 := by omega
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and]
  rcases h₁ with h₁ | h₂
  · have h₂' : (x₂ - y₂).natAbs = 0 := by omega
    have heq₂ : x₂ = y₂ := by
      have := Int.natAbs_eq_zero.mp h₂'
      omega
    have hdiff := (Int.natAbs_eq_iff.mp h₁)
    rcases hdiff with hdiff | hdiff
    · refine ⟨.west, ?_⟩
      simp [Compass.step, heq₂]
      omega
    · refine ⟨.east, ?_⟩
      simp [Compass.step, heq₂]
      omega
  · have h₁' : (x₁ - y₁).natAbs = 0 := by omega
    have heq₁ : x₁ = y₁ := by
      have := Int.natAbs_eq_zero.mp h₁'
      omega
    have hdiff := (Int.natAbs_eq_iff.mp h₂)
    rcases hdiff with hdiff | hdiff
    · refine ⟨.south, ?_⟩
      simp [Compass.step, heq₁]
      omega
    · refine ⟨.north, ?_⟩
      simp [Compass.step, heq₁]
      omega

private theorem card_neighbors (x : Plane) : (neighbors x).card = 4 := by
  have hinj : Function.Injective (Compass.step) := by
    intro a b h
    cases a <;> cases b <;> simp [Compass.step] at h ⊢
  rw [neighbors, Finset.card_image_iff.mpr (by
    intro a ha b hb hab
    exact hinj (add_left_cancel hab))]
  decide

private theorem interior_neighbors_subset {G : Finset Plane} {x : Plane}
    (hxG : x ∈ G) (hxS : x ∉ protectedSites G) : neighbors x ⊆ G := by
  intro z hz
  by_contra hzG
  have hnot : ¬ boundaryDepth G x ≤ 2 := by
    intro hle
    exact hxS (Finset.mem_filter.mpr ⟨hxG, hle⟩)
  have hdist : boundaryDepth G x ≤ (latticeDist x z : ℕ∞) := by
    rw [boundaryDepth, setDistance]
    exact iInf_le (fun y : {z // z ∉ G} => (latticeDist x y.val : ℕ∞)) ⟨z, hzG⟩
  have hadj : Adjacent x z := by
    rcases Finset.mem_image.mp hz with ⟨d, hd, rfl⟩
    cases d <;> simp [Adjacent, latticeDist, Compass.step]
  have hle : (latticeDist x z : ℕ∞) ≤ 2 := by
    rw [Adjacent] at hadj
    simp [hadj]
  exact (not_le_of_gt (not_le.mp hnot)) (hdist.trans hle)

private theorem traceStep_kept_mem {G : Finset Plane} (E : Network G)
    (a b x t : Plane) (hedge : ({a, b} : Finset Plane) ≠ {x, t}) :
    (t ∈ (traceStep E a b).kept x ↔ t ∈ E.kept x) := by
  by_cases hxa : x = a
  · subst x
    have htb : t ≠ b := by
      intro h
      subst t
      apply hedge
      simp
    simp [traceStep, htb]
  · by_cases hxb : x = b
    · subst x
      have hta : t ≠ a := by
        intro h
        subst t
        apply hedge
        simp [Finset.pair_comm]
      simp [traceStep, hxa, hta]
    · simp [traceStep, hxa, hxb]

private theorem traceStep_kept_mem_iff {G : Finset Plane} (E : Network G)
    (a b x t : Plane) :
    (t ∈ (traceStep E a b).kept x ↔
      t ∈ E.kept x ∧ ¬ (x = a ∧ t = b) ∧ ¬ (x = b ∧ t = a)) := by
  by_cases hxa : x = a
  · subst x
    by_cases hab : a = b
    · subst b
      simp [traceStep, Finset.mem_erase, and_comm]
    · simp [traceStep, hab, Finset.mem_erase, and_comm]
  · by_cases hxb : x = b
    · subst x
      simp [traceStep, hxa, Finset.mem_erase, and_comm]
    · simp [traceStep, hxa, hxb]

private theorem traceStep_kept_subset {G : Finset Plane} (E : Network G)
    (a b x t : Plane) (h : t ∈ (traceStep E a b).kept x) : t ∈ E.kept x := by
  exact (traceStep_kept_mem_iff E a b x t).mp h |>.1

private theorem traceStep_active_subset {G : Finset Plane} (E : Network G)
    (a b : Plane) : (traceStep E a b).active ⊆ E.active := by
  intro x hx
  simp only [Network.active, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxG, hstatus⟩
  refine ⟨hxG, ?_⟩
  by_cases hxa : x = a
  · subst x
    by_cases haU : E.status a = .U
    · simp [haU]
    · simp [traceStep, haU] at hstatus
  · simpa [traceStep, hxa] using hstatus

private theorem traceStep_presentNeighbors_subset {G : Finset Plane} (E : Network G)
    (a b x : Plane) :
    (traceStep E a b).presentNeighbors x ⊆ E.presentNeighbors x := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzN, hzP⟩
  refine Finset.mem_filter.mpr ⟨hzN, ?_⟩
  rcases hzP with ⟨hx, hzA, hAdj, hzk, hxk⟩
  exact ⟨traceStep_active_subset E a b hx,
    traceStep_active_subset E a b hzA, hAdj,
    traceStep_kept_subset E a b x z hzk,
    traceStep_kept_subset E a b z x hxk⟩

private theorem traceStep_mutual {G : Finset Plane} (E : Network G)
    (a b : Plane)
    (hmut : ∀ x ∈ E.active, ∀ z ∈ E.active, Adjacent x z →
      (z ∈ E.kept x ↔ x ∈ E.kept z)) :
    ∀ x ∈ (traceStep E a b).active, ∀ z ∈ (traceStep E a b).active,
      Adjacent x z →
      (z ∈ (traceStep E a b).kept x ↔ x ∈ (traceStep E a b).kept z) := by
  intro x hx z hz hAdj
  have hxE := traceStep_active_subset E a b hx
  have hzE := traceStep_active_subset E a b hz
  have h0 := hmut x hxE z hzE hAdj
  rw [traceStep_kept_mem_iff, traceStep_kept_mem_iff]
  constructor
  · rintro ⟨hflag, hnot₁, hnot₂⟩
    refine ⟨h0.mp hflag, ?_, ?_⟩
    · intro h
      exact hnot₂ ⟨h.2, h.1⟩
    · intro h
      exact hnot₁ ⟨h.2, h.1⟩
  · rintro ⟨hflag, hnot₁, hnot₂⟩
    refine ⟨h0.mpr hflag, ?_, ?_⟩
    · intro h
      exact hnot₂ ⟨h.2, h.1⟩
    · intro h
      exact hnot₁ ⟨h.2, h.1⟩

private theorem traceStep_auxiliary {G : Finset Plane} (E : Network G)
    (y z : Plane) (hE : E.Auxiliary) (hyG : y ∈ G)
    (hyS : y ∉ protectedSites G)
    (hUcard : E.status y = .U → (E.kept y).card = 3)
    (hzy : z ∈ E.kept y) : (traceStep E y z).Auxiliary := by
  rcases hE with ⟨⟨hOff, hKeep, hDdeg, hFactor⟩, hProtected⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hxG
    by_cases hxy : x = y
    · subst x
      exact False.elim (by exact hxG hyG)
    · simpa [traceStep, Function.update_apply, hxy] using hOff x hxG
  · intro x t ht
    have htE := traceStep_kept_subset E y z x t ht
    exact hKeep x htE
  · intro x hxG hxD
    by_cases hxy : x = y
    · subst x
      have hyU : E.status y = .U := by
        by_contra h
        simp [traceStep, h] at hxD
      have hcard : ((traceStep E y z).kept y).card = 2 := by
        simp only [traceStep, ite_true]
        rw [Finset.card_erase_of_mem hzy, hUcard hyU]
      have hsub : (traceStep E y z).presentNeighbors y ⊆
          (traceStep E y z).kept y := by
        intro t ht
        exact (Finset.mem_filter.mp ht).2.2.2.2.1
      calc
        ((traceStep E y z).presentNeighbors y).card ≤
            ((traceStep E y z).kept y).card := Finset.card_le_card hsub
        _ = 2 := hcard
    · have hxD' : E.status x = .D := by
        simpa [traceStep, Function.update_apply, hxy] using hxD
      calc
        ((traceStep E y z).presentNeighbors x).card ≤
            (E.presentNeighbors x).card :=
          Finset.card_le_card (traceStep_presentNeighbors_subset E y z x)
        _ ≤ 2 := hDdeg x hxG hxD'
  · intro x hx
    have hxE := traceStep_active_subset E y z hx
    have hFactor' := hFactor x hxE
    have hCard := Finset.card_le_card (traceStep_presentNeighbors_subset E y z x)
    change ((traceStep E y z).presentNeighbors x).card +
      ((originalLegs G).filter fun e => e.1 = x).card ≤ 4
    change (E.presentNeighbors x).card +
      ((originalLegs G).filter fun e => e.1 = x).card ≤ 4 at hFactor'
    omega
  · intro x hxS
    have hxy : x ≠ y := by
      intro h
      subst x
      exact hyS hxS
    simpa [traceStep, Function.update_apply, hxy] using hProtected x hxS

private theorem normalizeStart_present_flags {G : Finset Plane} (D : Network G)
    {u c a b : Plane} (hc : D.status c = .X) (h : D.Present a b) :
    b ∈ (normalizeStart D u c).kept a ∧ a ∈ (normalizeStart D u c).kept b := by
  have ha : a ∈ D.active := h.1
  have hb : b ∈ D.active := h.2.1
  have hac : a ≠ c := by
    intro heq
    subst a
    simp [Network.active, hc] at ha
  have hbc : b ≠ c := by
    intro heq
    subst b
    simp [Network.active, hc] at hb
  have hab : a ≠ b := by
    intro heq
    subst b
    have := h.2.2.1
    simp [Adjacent, latticeDist] at this
  constructor
  · by_cases hau : a = u
    · subst a
      by_cases huU : D.status u = .U
      · simp [normalizeStart, huU, Finset.mem_erase, hbc, h.2.2.2.1]
      · simp [normalizeStart, huU, h.2.2.2.1]
    · simp [normalizeStart, hau, h.2.2.2.1]
  · by_cases hbu : b = u
    · subst b
      by_cases huU : D.status u = .U
      · simp [normalizeStart, huU, Finset.mem_erase, hac, h.2.2.2.2]
      · simp [normalizeStart, huU, h.2.2.2.2]
    · simp [normalizeStart, hbu, h.2.2.2.2]

private theorem normalizeStart_kept_mem_iff {G : Finset Plane} (D : Network G)
    (u c x t : Plane) :
    (t ∈ (normalizeStart D u c).kept x ↔
      t ∈ D.kept x ∧ ¬ (x = u ∧ D.status u = .U ∧ t = c)) := by
  by_cases h : x = u ∧ D.status u = .U
  · simp [normalizeStart, h, Finset.mem_erase, and_comm]
  · simp [normalizeStart, h]
    intro ht hxu hU
    exact False.elim (h ⟨hxu, hU⟩)

private theorem normalizeStart_kept_subset {G : Finset Plane} (D : Network G)
    (u c x t : Plane) (h : t ∈ (normalizeStart D u c).kept x) : t ∈ D.kept x :=
  (normalizeStart_kept_mem_iff D u c x t).mp h |>.1

private theorem normalizeStart_presentNeighbors_subset {G : Finset Plane}
    (D : Network G) (u c x : Plane) :
    (normalizeStart D u c).presentNeighbors x ⊆ D.presentNeighbors x := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzN, hzP⟩
  refine Finset.mem_filter.mpr ⟨hzN, ?_⟩
  rcases hzP with ⟨hx, hzA, hAdj, hzk, hxk⟩
  have hxD : x ∈ D.active := by
    rcases Finset.mem_filter.mp hx with ⟨hxG, hxstatus⟩
    exact Finset.mem_filter.mpr ⟨hxG, by simpa [normalizeStart] using hxstatus⟩
  have hzD : z ∈ D.active := by
    rcases Finset.mem_filter.mp hzA with ⟨hzG, hzstatus⟩
    exact Finset.mem_filter.mpr ⟨hzG, by simpa [normalizeStart] using hzstatus⟩
  refine ⟨hxD, hzD, hAdj,
    normalizeStart_kept_subset D u c x z hzk,
    normalizeStart_kept_subset D u c z x hxk⟩

private theorem normalizeStart_mutual {G : Finset Plane} (D : Network G)
    (u c : Plane) (hcX : D.status c = .X)
    (hmut : ∀ x ∈ D.active, ∀ z ∈ D.active, Adjacent x z →
      (z ∈ D.kept x ↔ x ∈ D.kept z)) :
    ∀ x ∈ (normalizeStart D u c).active, ∀ z ∈ (normalizeStart D u c).active,
      Adjacent x z →
      (z ∈ (normalizeStart D u c).kept x ↔ x ∈ (normalizeStart D u c).kept z) := by
  intro x hx z hz hAdj
  have hxD : x ∈ D.active := by
    rcases Finset.mem_filter.mp hx with ⟨hxG, hxstatus⟩
    exact Finset.mem_filter.mpr ⟨hxG, by simpa [normalizeStart] using hxstatus⟩
  have hzD : z ∈ D.active := by
    rcases Finset.mem_filter.mp hz with ⟨hzG, hzstatus⟩
    exact Finset.mem_filter.mpr ⟨hzG, by simpa [normalizeStart] using hzstatus⟩
  have hxC : x ≠ c := by
    intro h
    subst x
    simp [Network.active, hcX] at hxD
  have hzC : z ≠ c := by
    intro h
    subst z
    simp [Network.active, hcX] at hzD
  have hxFlag : (z ∈ (normalizeStart D u c).kept x ↔ z ∈ D.kept x) := by
    rw [normalizeStart_kept_mem_iff]
    simp [hzC]
  have hzFlag : (x ∈ (normalizeStart D u c).kept z ↔ x ∈ D.kept z) := by
    rw [normalizeStart_kept_mem_iff]
    simp [hxC]
  rw [hxFlag, hzFlag]
  exact hmut x hxD z hzD hAdj

private theorem normalizeStart_auxiliary {G : Finset Plane} (D : Network G)
    (u c : Plane) (hD : D.Consistent) :
    (normalizeStart D u c).Auxiliary := by
  rcases hD.1.1 with ⟨hOff, hKeep, hDdeg, hFactor⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hxG
    simpa [normalizeStart] using hOff x hxG
  · intro x t ht
    exact hKeep x (normalizeStart_kept_subset D u c x t ht)
  · intro x hxG hxD
    have hxD' : D.status x = .D := by simpa [normalizeStart] using hxD
    calc
      ((normalizeStart D u c).presentNeighbors x).card ≤
          (D.presentNeighbors x).card :=
        Finset.card_le_card (normalizeStart_presentNeighbors_subset D u c x)
      _ ≤ 2 := hDdeg x hxG hxD'
  · intro x hx
    have hxD : x ∈ D.active := by
      rcases Finset.mem_filter.mp hx with ⟨hxG, hxstatus⟩
      exact Finset.mem_filter.mpr ⟨hxG, by simpa [normalizeStart] using hxstatus⟩
    have hFactor' := hFactor x hxD
    have hCard := Finset.card_le_card (normalizeStart_presentNeighbors_subset D u c x)
    change ((normalizeStart D u c).presentNeighbors x).card +
      ((originalLegs G).filter fun e => e.1 = x).card ≤ 4
    change (D.presentNeighbors x).card +
      ((originalLegs G).filter fun e => e.1 = x).card ≤ 4 at hFactor'
    omega
  · intro x hxS
    simpa [normalizeStart] using (hD.1.2 x hxS).1

private def PrefixInvariant (G : Finset Plane) (E : Network G) (y : Plane) : Prop :=
  E.Auxiliary ∧
  (∀ x ∈ G, x ≠ y → E.status x = .U → E.kept x = neighbors x ∩ G) ∧
  (∀ x ∈ G, x ≠ y → E.status x = .D → (E.kept x).card = 2) ∧
  (∀ x ∈ E.active, ∀ z ∈ E.active, Adjacent x z →
    (z ∈ E.kept x ↔ x ∈ E.kept z)) ∧
  (E.status y = .U → (E.kept y).card = 3)

private theorem normalizeStart_prefixInvariant {G : Finset Plane} (D : Network G)
    (u c : Plane) (hD : D.Consistent) (huG : u ∈ G)
    (huS : u ∉ protectedSites G) (hcG : c ∈ G) (huc : Adjacent u c)
    (hcX : D.status c = .X) : PrefixInvariant G (normalizeStart D u c) u := by
  have hAux := normalizeStart_auxiliary D u c hD
  refine ⟨hAux, ?_, ?_, ?_, ?_⟩
  · intro x hxG hxu hxU
    have hxU' : D.status x = .U := by simpa [normalizeStart] using hxU
    have hfull := hD.2.1 x hxG hxU'
    simpa [normalizeStart, hxu] using hfull
  · intro x hxG hxu hxD'
    have hxD : D.status x = .D := by simpa [normalizeStart] using hxD'
    have hcard := hD.2.2.1 x hxG hxD
    simpa [normalizeStart, hxu] using hcard
  · exact normalizeStart_mutual D u c hcX hD.2.2.2
  · intro huU
    have huU' : D.status u = .U := by simpa [normalizeStart] using huU
    have hfull := hD.2.1 u huG huU'
    have hInterior := interior_neighbors_subset huG huS
    have hEq : neighbors u ∩ G = neighbors u := Finset.inter_eq_left.mpr hInterior
    have hfullCard : (D.kept u).card = 4 := by rw [hfull, hEq, card_neighbors]
    have hcin : c ∈ D.kept u := by
      rw [hfull]
      exact Finset.mem_inter.mpr ⟨adjacent_mem_neighbors huc, hcG⟩
    have hcard := Finset.card_erase_of_mem hcin
    have hN : (normalizeStart D u c).kept u = (D.kept u).erase c := by
      simp [normalizeStart, huU']
    rw [hN, hcard, hfullCard]

private theorem prefixInvariant_step {G : Finset Plane} (E : Network G)
    (y z : Plane) (hInv : PrefixInvariant G E y)
    (hyG : y ∈ G) (hzG : z ∈ G)
    (hyS : y ∉ protectedSites G) (hzS : z ∉ protectedSites G)
    (hyz : y ≠ z) (hflags : z ∈ E.kept y ∧ y ∈ E.kept z) :
    PrefixInvariant G (traceStep E y z) z := by
  have hAux := traceStep_auxiliary E y z hInv.1 hyG hyS hInv.2.2.2.2 hflags.1
  have hInterior := interior_neighbors_subset hzG hzS
  refine ⟨hAux, ?_, ?_, ?_, ?_⟩
  · intro x hxG hxz hxU
    by_cases hxy : x = y
    · subst x
      by_cases hyU : E.status y = .U
      · simp [traceStep, hyU] at hxU
      · simp [traceStep, hyU] at hxU
    · have hxU' : E.status x = .U := by
        simpa [traceStep, hxy] using hxU
      have hxKeep : (traceStep E y z).kept x = E.kept x := by
        simp [traceStep, hxy, hxz]
      rw [hxKeep]
      exact hInv.2.1 x hxG hxy hxU'
  · intro x hxG hxz hxD
    by_cases hxy : x = y
    · subst x
      have hyU : E.status y = .U := by
        by_contra h
        simp [traceStep, h] at hxD
      have hcard := hInv.2.2.2.2 hyU
      simp only [traceStep, ite_true]
      rw [Finset.card_erase_of_mem hflags.1, hcard]
    · have hxD' : E.status x = .D := by
        simpa [traceStep, hxy] using hxD
      have hxKeep : (traceStep E y z).kept x = E.kept x := by
        simp [traceStep, hxy, hxz]
      rw [hxKeep]
      exact hInv.2.2.1 x hxG hxy hxD'
  · exact traceStep_mutual E y z hInv.2.2.2.1
  · intro hzU
    have hzU' : E.status z = .U := by
      simpa [traceStep, hyz.symm] using hzU
    have hzfull := hInv.2.1 z hzG (Ne.symm hyz) hzU'
    have hEq : neighbors z ∩ G = neighbors z := Finset.inter_eq_left.mpr hInterior
    have hzcard : (E.kept z).card = 4 := by
      rw [hzfull, hEq, card_neighbors]
    have hKeep : (traceStep E y z).kept z = (E.kept z).erase y := by
      simp [traceStep, hyz.symm]
    rw [hKeep, Finset.card_erase_of_mem hflags.2, hzcard]

private theorem removeSite_active_subset {G : Finset Plane} (E : Network G)
    (y : Plane) : (removeSite E y).active ⊆ E.active := by
  intro x hx
  simp only [Network.active, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxG, hxstatus⟩
  refine ⟨hxG, ?_⟩
  by_cases hxy : x = y
  · subst x
    simp [removeSite] at hxstatus
  · simpa [removeSite, hxy] using hxstatus

private theorem removeSite_presentNeighbors_subset {G : Finset Plane} (E : Network G)
    (y x : Plane) :
    (removeSite E y).presentNeighbors x ⊆ E.presentNeighbors x := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzN, hzP⟩
  refine Finset.mem_filter.mpr ⟨hzN, ?_⟩
  rcases hzP with ⟨hx, hzA, hAdj, hzk, hxk⟩
  exact ⟨removeSite_active_subset E y hx,
    removeSite_active_subset E y hzA, hAdj, hzk, hxk⟩

private theorem removeSite_consistent_of_prefixInvariant {G : Finset Plane}
    (E : Network G) (y : Plane) (hyS : y ∉ protectedSites G)
    (hInv : PrefixInvariant G E y) : (removeSite E y).Consistent := by
  rcases hInv with ⟨hAux, hU, hD, hMut, _⟩
  rcases hAux with ⟨⟨hOff, hKeep, hDdeg, hFactor⟩, hProtected⟩
  have hOrdLocal : (removeSite E y).LocalRules := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hxG
      by_cases hxy : x = y
      · subst x
        simp [removeSite]
      · simpa [removeSite, hxy] using hOff x hxG
    · exact hKeep
    · intro x hxG hxD'
      by_cases hxy : x = y
      · subst x
        simp [removeSite] at hxD'
      · have hxD : E.status x = .D := by
          simpa [removeSite, hxy] using hxD'
        calc
          ((removeSite E y).presentNeighbors x).card ≤ (E.presentNeighbors x).card :=
            Finset.card_le_card (removeSite_presentNeighbors_subset E y x)
          _ ≤ 2 := hDdeg x hxG hxD
    · intro x hx
      have hxE : x ∈ E.active := removeSite_active_subset E y hx
      have hF := hFactor x hxE
      have hCard := Finset.card_le_card (removeSite_presentNeighbors_subset E y x)
      change ((removeSite E y).presentNeighbors x).card +
        ((originalLegs G).filter fun e => e.1 = x).card ≤ 4
      change (E.presentNeighbors x).card +
        ((originalLegs G).filter fun e => e.1 = x).card ≤ 4 at hF
      omega
  have hOrd : (removeSite E y).Ordinary := by
    refine ⟨hOrdLocal, ?_⟩
    intro x hxS
    have hxy : x ≠ y := by
      intro heq
      subst x
      exact hyS hxS
    have hxU := hProtected x hxS
    have hxKept := hU x (Finset.mem_filter.mp hxS).1 hxy hxU
    exact ⟨by simpa [removeSite, Function.update_apply, hxy] using hxU,
      by simpa [removeSite] using hxKept⟩
  refine ⟨hOrd, ?_, ?_, ?_⟩
  · intro x hxG hxU'
    have hxy : x ≠ y := by
      intro h
      subst x
      simp [removeSite] at hxU'
    have hxU : E.status x = .U := by
      simpa [removeSite, hxy] using hxU'
    exact hU x hxG hxy hxU
  · intro x hxG hxD'
    have hxy : x ≠ y := by
      intro h
      subst x
      simp [removeSite] at hxD'
    have hxD : E.status x = .D := by
      simpa [removeSite, hxy] using hxD'
    simpa [removeSite] using hD x hxG hxy hxD
  · intro x hx z hz hAdj
    have hxE := removeSite_active_subset E y hx
    have hzE := removeSite_active_subset E y hz
    simpa [removeSite] using hMut x hxE z hzE hAdj

private theorem prefix_kept_unchanged {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n) (j : ℕ) (x t : Plane)
    (hj : j ≤ n)
    (hno : ∀ i : Fin n, i.val < j → wordBond u w i ≠ {x, t}) :
    (t ∈ (prefixNetwork D u w j).kept x ↔ t ∈ D.kept x) := by
  induction j with
  | zero => rw [prefixNetwork_zero]
  | succ j ih =>
      have hj' : j ≤ n := by omega
      have hstep := prefixNetwork_succ D u w j (by omega)
      rw [hstep, traceStep_kept_mem]
      · exact ih hj' (fun i hi => hno i (by omega))
      · have hcurr := hno ⟨j, by omega⟩ (by simp)
        intro heq
        apply hcurr
        simpa [wordBond] using heq

theorem main : AKLT.Blueprint.Rec.RemovedClosureStatement := by
  intro p T n w hTrail j hj hLive
  rcases p.pair with
    ⟨hCons, huActive, _hvActive, hcG, hcX, huc, _hvc, _hpair, _hdegree⟩
  have huG : p.u ∈ p.G := (Finset.mem_filter.mp huActive).1
  have hInit := normalizeStart_prefixInvariant p.D p.u p.c hCons huG p.interior
    hcG huc hcX
  have hvertexG : ∀ k ≤ j, wordVertex p.u w k ∈ p.G := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa [wordVertex] using huG
    · let i : Fin n := ⟨k - 1, by omega⟩
      have hPres := hTrail.2.1 i
      have hAct := hPres.2.1
      have hidx : i.val + 1 = k := by dsimp [i]; omega
      rw [hidx] at hAct
      exact (Finset.mem_filter.mp hAct).1
  have hinterior : ∀ k ≤ j, wordVertex p.u w k ∉ protectedSites p.G := by
    intro k hk
    by_cases hkj : k < j
    · have hkn : k < n := by omega
      exact (hTrail.2.2.1 k hkn).2
    · have hEq : k = j := by omega
      simpa [hEq] using hLive
  have hInvAll : ∀ k ≤ j,
      PrefixInvariant p.G (prefixNetwork p.normalized p.u w k) (wordVertex p.u w k) := by
    intro k hk
    induction k with
    | zero =>
        simpa [PairData.normalized, prefixNetwork_zero, wordVertex] using hInit
    | succ k ih =>
        have hkPrev : k ≤ j := by omega
        have hPrev := ih hkPrev
        have hi : k < n := by omega
        let i : Fin n := ⟨k, hi⟩
        have hPres := hTrail.2.1 i
        let hy : Plane := wordVertex p.u w k
        let hz : Plane := wordVertex p.u w (k + 1)
        have hyG := hvertexG k (by omega)
        have hzG := hvertexG (k + 1) (by omega)
        have hyS := hinterior k (by omega)
        have hzS := hinterior (k + 1) (by omega)
        have hAdj : Adjacent hy hz := by simpa [i] using hPres.2.2.1
        have hyz : hy ≠ hz := by
          intro heq
          rw [heq] at hAdj
          simp [Adjacent, latticeDist] at hAdj
        have hno : ∀ q : Fin n, q.val < k →
            wordBond p.u w q ≠ {hy, hz} := by
          intro q hq heq
          have hsame : wordBond p.u w q = wordBond p.u w i := by
            simpa [wordBond, hy, hz, i] using heq
          have hqi : q = i := hTrail.1 hsame
          have hval : q.val = k := congrArg Fin.val hqi
          omega
        have hflags : hz ∈ (prefixNetwork p.normalized p.u w k).kept hy ∧
            hy ∈ (prefixNetwork p.normalized p.u w k).kept hz := by
          constructor
          · exact (prefix_kept_unchanged p.normalized p.u w k hy hz (by omega)
              hno).mpr hPres.2.2.2.1
          · exact (prefix_kept_unchanged p.normalized p.u w k hz hy (by omega)
              (by
                intro q hq heq
                have hsame : wordBond p.u w q = wordBond p.u w i := by
                  simpa [wordBond, hy, hz, i, Finset.pair_comm] using heq
                have hqi : q = i := hTrail.1 hsame
                have hval : q.val = k := congrArg Fin.val hqi
                omega)).mpr hPres.2.2.2.2
        have hPrev' : PrefixInvariant p.G (prefixNetwork p.normalized p.u w k) hy := by
          simpa [hy] using hPrev
        have hNext := prefixInvariant_step (prefixNetwork p.normalized p.u w k)
          hy hz hPrev' hyG hzG hyS hzS hyz hflags
        simpa [hy, hz, prefixNetwork_succ p.normalized p.u w k (by omega)] using hNext
  have hInv := hInvAll j le_rfl
  exact removeSite_consistent_of_prefixInvariant
    (prefixNetwork p.normalized p.u w j) (wordVertex p.u w j) hLive hInv

end AKLT.W.REC051

end
