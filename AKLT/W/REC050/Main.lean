module
public import AKLT.Blueprint.Rec.NodesClosure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC050

def MutualKept {G : Finset Plane} (D : Network G) : Prop :=
  ∀ x ∈ D.active, ∀ z ∈ D.active, Adjacent x z →
    (z ∈ D.kept x ↔ x ∈ D.kept z)

private theorem normalizeStart_mutual {G : Finset Plane} (D : Network G)
    (u c : Plane) (hc : D.status c = .X) (hmut : MutualKept D) :
    MutualKept (normalizeStart D u c) := by
  intro x hx z hz hadj
  have hxD : x ∈ D.active := by
    change x ∈ D.active at hx
    exact hx
  have hzD : z ∈ D.active := by
    change z ∈ D.active at hz
    exact hz
  have hcInactive : c ∉ D.active := by
    change ¬ c ∈ G.filter (fun q => D.status q ≠ .X)
    intro h
    exact (Finset.mem_filter.mp h).2 hc
  have hne : x ≠ z := by
    intro heq
    subst z
    simp [Adjacent, latticeDist] at hadj
  by_cases hxU : x = u ∧ D.status u = .U
  · have hzu : z ≠ u := by
      intro h
      subst z
      exact hne hxU.1
    have hzc : z ≠ c := by
      intro h
      subst z
      exact hcInactive hzD
    have hzNoUpdate : ¬ (z = u ∧ D.status u = .U) := fun h => hzu h.1
    simp only [normalizeStart, ite_eq_left hxU, ite_eq_right hzNoUpdate]
    have hmem : z ∈ (D.kept x).erase c ↔ z ∈ D.kept x := by
      simp [Finset.mem_erase, hzc]
    rw [hmem]
    exact hmut x hxD z hzD hadj
  · by_cases hzU : z = u ∧ D.status u = .U
    · have hxu : x ≠ u := by
        intro h
        subst x
        exact hne hzU.1.symm
      have hxc : x ≠ c := by
        intro h
        subst x
        exact hcInactive hxD
      have hxNoUpdate : ¬ (x = u ∧ D.status u = .U) := fun h => hxu h.1
      simp only [normalizeStart, ite_eq_right hxNoUpdate, ite_eq_left hzU]
      have hmem : x ∈ (D.kept z).erase c ↔ x ∈ D.kept z := by
        simp [Finset.mem_erase, hxc]
      rw [hmem]
      exact hmut x hxD z hzD hadj
    · simpa [normalizeStart, hxU, hzU] using hmut x hxD z hzD hadj

private theorem active_traceStep_subset {G : Finset Plane} (D : Network G)
    (y o : Plane) : (traceStep D y o).active ⊆ D.active := by
  intro x hx
  by_cases hxy : x = y
  · subst x
    have hx' : y ∈ G.filter (fun q => (traceStep D y o).status q ≠ .X) := by
      change y ∈ (traceStep D y o).active at hx
      exact hx
    have hyG : y ∈ G := (Finset.mem_filter.mp hx').1
    have hyU : D.status y = .U := by
      by_cases h : D.status y = .U
      · exact h
      · have hstatus := (Finset.mem_filter.mp hx').2
        have hstep : (traceStep D y o).status y = .X := by simp [traceStep, h]
        exact (hstatus hstep).elim
    exact Finset.mem_filter.mpr ⟨hyG, by simp [hyU]⟩
  · have hx' : x ∈ G.filter (fun q => (traceStep D y o).status q ≠ .X) := by
      change x ∈ (traceStep D y o).active at hx
      exact hx
    have hxG := (Finset.mem_filter.mp hx').1
    have hxStatus := (Finset.mem_filter.mp hx').2
    have hxStatus' : D.status x ≠ .X := by simpa [traceStep, hxy] using hxStatus
    exact Finset.mem_filter.mpr ⟨hxG, hxStatus'⟩

private theorem traceStep_mutual {G : Finset Plane} (D : Network G)
    (y o : Plane) (hmut : MutualKept D) : MutualKept (traceStep D y o) := by
  intro x hx z hz hadj
  have hxD := active_traceStep_subset D y o hx
  have hzD := active_traceStep_subset D y o hz
  have hne : x ≠ z := by
    intro heq
    subst z
    simp [Adjacent, latticeDist] at hadj
  by_cases hxy : x = y
  · subst x
    have hzy : z ≠ y := by
      intro h
      subst z
      exact hne rfl
    by_cases hzo : z = o
    · subst z
      have hoy : o ≠ y := by intro h; subst o; exact hzy rfl
      simp [traceStep, hoy]
    · simpa [traceStep, hzy, hzo] using hmut y hxD z hzD hadj
  · by_cases hzy : z = y
    · subst z
      have hxy' : x ≠ y := hxy
      by_cases hxo : x = o
      · subst x
        have hoy : o ≠ y := by intro h; subst o; exact hxy' rfl
        simp [traceStep, hoy]
      · simpa [traceStep, hxy', hxo] using hmut x hxD y hzD hadj
    · by_cases hxo : x = o
      · subst x
        by_cases hzo : z = o
        · subst z
          exact (hne rfl).elim
        · simpa [traceStep, hxy, hzy, hzo, Finset.mem_erase] using
            hmut o hxD z hzD hadj
      · by_cases hzo : z = o
        · subst z
          simpa [traceStep, hxy, hzy, hxo, Finset.mem_erase] using
            hmut x hxD o hzD hadj
        · simpa [traceStep, hxy, hzy, hxo, hzo] using
            hmut x hxD z hzD hadj

private theorem traceNetwork_mutual {G : Finset Plane} (D : Network G)
    (xs : List Plane) (hmut : MutualKept D) :
    MutualKept (traceNetwork D xs) := by
  induction xs generalizing D with
  | nil => simpa [traceNetwork] using hmut
  | cons a xs ih =>
      cases xs with
      | nil => simpa [traceNetwork] using hmut
      | cons b rest =>
          exact ih (traceStep D a b) (traceStep_mutual D a b hmut)

private theorem traceStep_status_U_imp {G : Finset Plane} (D : Network G)
    (y o x : Plane) (h : (traceStep D y o).status x = .U) :
    D.status x = .U := by
  by_cases hxy : x = y
  · subst x
    cases hs : D.status y <;> simp [traceStep, hs] at h
  · simpa [traceStep, hxy] using h

private theorem traceNetwork_status_U_imp {G : Finset Plane} (D : Network G)
    (xs : List Plane) (x : Plane)
    (h : (traceNetwork D xs).status x = .U) : D.status x = .U := by
  induction xs generalizing D with
  | nil => simpa [traceNetwork] using h
  | cons a xs ih =>
      cases xs with
      | nil => simpa [traceNetwork] using h
      | cons b rest =>
          exact traceStep_status_U_imp D a b x (ih (traceStep D a b) h)

private theorem traceNetwork_departure_head_not_U {G : Finset Plane}
    (D : Network G) (a b : Plane) (rest : List Plane) :
    (traceNetwork D (a :: b :: rest)).status a ≠ .U := by
  intro h
  have hstep : (traceStep D a b).status a = .U :=
    traceNetwork_status_U_imp (traceStep D a b) (b :: rest) a h
  cases hs : D.status a <;> simp [traceStep, hs] at hstep

private theorem traceNetwork_departed_not_U {G : Finset Plane} (D : Network G) :
    ∀ (xs : List Plane) (i : ℕ) (x : Plane),
      xs[i]? = some x → i + 1 < xs.length →
        (traceNetwork D xs).status x ≠ .U := by
  intro xs
  induction xs generalizing D with
  | nil => intro i x hget hbound; simp at hbound
  | cons a xs ih =>
      cases xs with
      | nil => intro i x hget hbound; simp at hbound
      | cons b rest =>
          intro i x hget hbound
          cases i with
          | zero =>
              have hxa : a = x := by simpa using hget
              have hx : x = a := hxa.symm
              subst x
              exact traceNetwork_departure_head_not_U D a b rest
          | succ k =>
              have hget' : (b :: rest)[k]? = some x := by simpa using hget
              have hbound' : k + 1 < (b :: rest).length := by
                simp at hbound ⊢
                omega
              exact ih (traceStep D a b) k x hget' hbound'

private theorem prefix_mutual :
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ j ≤ n,
    ∀ x ∈ (prefixNetwork p.normalized p.u w j).active,
    ∀ z ∈ (prefixNetwork p.normalized p.u w j).active,
      Adjacent x z →
        (z ∈ (prefixNetwork p.normalized p.u w j).kept x ↔
          x ∈ (prefixNetwork p.normalized p.u w j).kept z)
  := by
  intro p T n w hTrail j hj x hx z hz hadj
  have hcons : p.D.Consistent := p.pair.1
  have hcX : p.D.status p.c = .X := p.pair.2.2.2.2.1
  have hmut : MutualKept p.D := hcons.2.2.2
  have hmutStart : MutualKept p.normalized :=
    normalizeStart_mutual p.D p.u p.c hcX hmut
  exact traceNetwork_mutual p.normalized
    ((wordVertices p.u w).take (j + 1)) hmutStart x hx z hz hadj

private theorem prefix_no_return :
  ∀ p : PairSetup, ∀ T : Finset Plane, ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail p.normalized p.u T w → ∀ j ≤ n,
    ∀ i < j,
      (prefixNetwork p.normalized p.u w j).status (wordVertex p.u w i) ≠ .U
  := by
  intro p T n w hTrail j hj i hij
  have hVerticesLength : (wordVertices p.u w).length = n + 1 := by
    simp [wordVertices]
  have hGet : ((wordVertices p.u w).take (j + 1))[i]? =
      some (wordVertex p.u w i) := by
    rw [List.getElem?_take]
    have hij' : i < j + 1 := by omega
    simp [hij']
    change ((List.range (n + 1)).map (wordVertex p.u w))[i]? =
      some (wordVertex p.u w i)
    rw [List.getElem?_map]
    rw [List.getElem?_range (by omega : i < n + 1)]
    rfl
  have hBound : i + 1 < ((wordVertices p.u w).take (j + 1)).length := by
    rw [List.length_take]
    have hlen : j + 1 ≤ (wordVertices p.u w).length := by
      rw [hVerticesLength]
      omega
    rw [Nat.min_eq_left hlen]
    omega
  exact traceNetwork_departed_not_U p.normalized
    ((wordVertices p.u w).take (j + 1)) i (wordVertex p.u w i) hGet hBound


private theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  have hinj : Function.Injective (fun d : Compass => x + d.step) := by
    intro a b h
    have hstep : a.step = b.step := add_left_cancel h
    cases a <;> cases b <;> simp_all [Compass.step]
  rw [neighbours, Finset.card_image_of_injective _ hinj]
  decide

private theorem neighbour_distance {x z : Plane} (hz : z ∈ neighbours x) :
    Adjacent x z := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

private theorem neighbours_symm {x z : Plane} (hz : z ∈ neighbours x) :
    x ∈ neighbours z := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz
  refine Finset.mem_image.mpr ⟨d.reverse, Finset.mem_univ _, ?_⟩
  cases d <;> simp [Compass.step, Compass.reverse, Prod.ext_iff]

private theorem interior_neighbours {G : Finset Plane} {x : Plane}
    (hx : x ∈ G) (hinterior : x ∉ protectedSites G) : neighbours x ⊆ G := by
  classical
  intro z hz
  by_contra hzg
  apply hinterior
  refine Finset.mem_filter.mpr ⟨hx, ?_⟩
  change (⨅ a : {a : Plane // a ∉ G}, (latticeDist x a.val : ℕ∞)) ≤ 2
  exact (iInf_le _ ⟨z, hzg⟩).trans (by
    have hd := neighbour_distance hz
    change latticeDist x z = 1 at hd
    simp [hd])

private theorem step_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  classical
  simp only [traceStep]
  split_ifs
  · exact Finset.erase_subset _ _
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

private theorem present_symm {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : D.Present z x := by
  refine ⟨h.2.1, h.1, ?_, h.2.2.2.2, h.2.2.2.1⟩
  have hdist : latticeDist z x = latticeDist x z := by
    simp only [latticeDist]
    rw [show z.1 - x.1 = -(x.1 - z.1) by omega,
      show z.2 - x.2 = -(x.2 - z.2) by omega, Int.natAbs_neg, Int.natAbs_neg]
  exact hdist.trans h.2.2.1

private theorem present_mem {G : Finset Plane} {D : Network G} (hlocal : D.LocalRules)
    {x z : Plane} (h : D.Present x z) : z ∈ D.presentNeighbours x := by
  exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hlocal.2.1 x h.2.2.2.1)).1, h⟩

private theorem step_present_subset {G : Finset Plane} (D : Network G) (y o : Plane)
    {x z : Plane} (h : (traceStep D y o).Present x z) : D.Present x z := by
  exact ⟨active_traceStep_subset D y o h.1,
    active_traceStep_subset D y o h.2.1, h.2.2.1,
    step_kept_subset D y o x h.2.2.2.1, step_kept_subset D y o z h.2.2.2.2⟩

private theorem step_neighbours_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x := by
  intro z hz
  obtain ⟨hzn, hp⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzn, step_present_subset D y o hp⟩

private theorem normalize_present_subset {G : Finset Plane} (D : Network G) (u c : Plane)
    {x z : Plane} (h : (normalizeStart D u c).Present x z) : D.Present x z := by
  have hk (a : Plane) : (normalizeStart D u c).kept a ⊆ D.kept a := by
    simp only [normalizeStart]
    split_ifs
    · exact Finset.erase_subset ..
    · exact Finset.Subset.refl _
  exact ⟨h.1, h.2.1, h.2.2.1, hk x h.2.2.2.1, hk z h.2.2.2.2⟩

private theorem normalize_neighbours_subset {G : Finset Plane} (D : Network G)
    (u c x : Plane) : (normalizeStart D u c).presentNeighbours x ⊆ D.presentNeighbours x := by
  intro z hz
  obtain ⟨hzn, hp⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzn, normalize_present_subset D u c hp⟩

private theorem normalize_auxiliary {G : Finset Plane} (D : Network G) (u c : Plane)
    (haux : D.Auxiliary) : (normalizeStart D u c).Auxiliary := by
  refine ⟨⟨haux.1.1, ?_, ?_, ?_⟩, haux.2⟩
  · intro x
    simp only [normalizeStart]
    split_ifs
    · exact (Finset.erase_subset ..).trans (haux.1.2.1 x)
    · exact haux.1.2.1 x
  · intro x hx hs
    exact (Finset.card_le_card (normalize_neighbours_subset D u c x)).trans
      (haux.1.2.2.1 x hx hs)
  · intro x hx
    exact (Nat.add_le_add_right
      (Finset.card_le_card (normalize_neighbours_subset D u c x)) _).trans
      (haux.1.2.2.2 x hx)

private theorem traceNetwork_snoc {G : Finset Plane} (D : Network G)
    (xs : List Plane) (y o : Plane) :
    traceNetwork D (xs ++ [y, o]) = traceStep (traceNetwork D (xs ++ [y])) y o := by
  induction xs generalizing D with
  | nil => rfl
  | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b rest => exact ih (traceStep D a b)

private theorem prefix_eq {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    prefixNetwork D u w j = traceNetwork D ((List.range (j + 1)).map (wordVertex u w)) := by
  unfold prefixNetwork wordVertices
  rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega : j + 1 ≤ n + 1)]

private theorem prefix_zero {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) : prefixNetwork D u w 0 = D := by
  rw [prefix_eq D u w 0 (Nat.zero_le n)]
  rfl

private theorem prefix_succ {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  rw [prefix_eq D u w (j + 1) (by omega), prefix_eq D u w j (by omega)]
  rw [List.range_succ, List.map_append, List.map_singleton]
  rw [List.range_succ, List.map_append, List.map_singleton]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    traceNetwork_snoc D ((List.range j).map (wordVertex u w))
      (wordVertex u w j) (wordVertex u w (j + 1))

private theorem present_ne {G : Finset Plane} {D : Network G} {y o : Plane}
    (hp : D.Present y o) : y ≠ o := by
  intro h
  have ha := hp.2.2.1
  subst o
  simp [Adjacent, latticeDist] at ha

private theorem presentNeighbours_subset_kept {G : Finset Plane} (D : Network G)
    (x : Plane) : D.presentNeighbours x ⊆ D.kept x := by
  intro z hz
  exact (Finset.mem_filter.mp hz).2.2.2.2.1

private theorem step_auxiliary {G : Finset Plane} {D : Network G} {y o : Plane}
    (haux : D.Auxiliary) (hp : D.Present y o) (hyS : y ∉ protectedSites G)
    (hU : D.status y = .U → ((traceStep D y o).kept y).card ≤ 2) :
    (traceStep D y o).Auxiliary := by
  have hyG : y ∈ G := (Finset.mem_filter.mp hp.1).1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    have hxy : x ≠ y := by intro h; subst x; exact hx hyG
    simpa [traceStep, hxy] using haux.1.1 x hx
  · intro x
    exact (step_kept_subset D y o x).trans (haux.1.2.1 x)
  · intro x hx hs
    by_cases hxy : x = y
    · subst x
      have hyU : D.status y = .U := by
        by_cases h : D.status y = .U
        · exact h
        · simp [traceStep, h] at hs
      exact (Finset.card_le_card (presentNeighbours_subset_kept (traceStep D y o) y)).trans
        (hU hyU)
    · have hsD : D.status x = .D := by simpa [traceStep, hxy] using hs
      exact (Finset.card_le_card (step_neighbours_subset D y o x)).trans
        (haux.1.2.2.1 x hx hsD)
  · intro x hx
    exact (Nat.add_le_add_right
      (Finset.card_le_card (step_neighbours_subset D y o x)) _).trans
      (haux.1.2.2.2 x (active_traceStep_subset D y o hx))
  · intro x hx
    have hxy : x ≠ y := by intro h; subst x; exact hyS hx
    simpa [traceStep, hxy] using haux.2 x hx

/-- The two live-site facts needed in addition to the nonlive rules. -/
private def PrefixInvariant {G : Finset Plane} (E : Network G) (y : Plane) : Prop :=
  E.Auxiliary ∧
  (∀ x ∈ G, x ≠ y → E.status x = .U → E.kept x = neighbours x ∩ G) ∧
  (∀ x ∈ G, x ≠ y → E.status x = .D → (E.kept x).card = 2) ∧
  (E.status y = .U → ∃ a ∈ neighbours y ∩ G,
    E.kept y = (neighbours y ∩ G).erase a) ∧
  (E.status y = .D → (E.presentNeighbours y).card ≤ 1)

private theorem invariant_step {G : Finset Plane} {D : Network G} {y o : Plane}
    (h : PrefixInvariant D y) (hp : D.Present y o) (hyS : y ∉ protectedSites G) :
    PrefixInvariant (traceStep D y o) o := by
  classical
  have hyo : y ≠ o := present_ne hp
  have hoy : o ≠ y := hyo.symm
  have hyG : y ∈ G := (Finset.mem_filter.mp hp.1).1
  have hoG : o ∈ G := (Finset.mem_filter.mp hp.2.1).1
  have hout : o ∈ D.kept y := hp.2.2.2.1
  have hin : y ∈ D.kept o := hp.2.2.2.2
  have hnewU (hs : D.status y = .U) : ((traceStep D y o).kept y).card = 2 := by
    obtain ⟨a, ha, hka⟩ := h.2.2.2.1 hs
    have hfull : neighbours y ∩ G = neighbours y :=
      Finset.inter_eq_left.mpr (interior_neighbours hyG hyS)
    have hcard : (D.kept y).card = 3 := by
      rw [hka, Finset.card_erase_of_mem ha, hfull, neighbours_card]
    simp only [traceStep, ite_true, Finset.card_erase_of_mem hout, hcard]
  refine ⟨step_auxiliary h.1 hp hyS (fun hs => (hnewU hs).le), ?_, ?_, ?_, ?_⟩
  · intro x hx hxo hs
    by_cases hxy : x = y
    · subst x
      cases hsy : D.status y <;> simp [traceStep, hsy] at hs
    · have hsU : D.status x = .U := by simpa [traceStep, hxy] using hs
      simpa [traceStep, hxy, hxo] using h.2.1 x hx hxy hsU
  · intro x hx hxo hs
    by_cases hxy : x = y
    · subst x
      by_cases hsy : D.status y = .U
      · exact hnewU hsy
      · simp [traceStep, hsy] at hs
    · have hsD : D.status x = .D := by simpa [traceStep, hxy] using hs
      simpa [traceStep, hxy, hxo] using h.2.2.1 x hx hxy hsD
  · intro hs
    have hsU : D.status o = .U := by simpa [traceStep, hoy] using hs
    refine ⟨y, h.1.1.2.1 o hin, ?_⟩
    simp only [traceStep, ite_eq_right hoy, ite_true]
    rw [h.2.1 o hoG hoy hsU]
  · intro hs
    have hsD : D.status o = .D := by simpa [traceStep, hoy] using hs
    have hcard : ((traceStep D y o).kept o).card = 1 := by
      simp only [traceStep, ite_eq_right hoy, ite_true]
      rw [Finset.card_erase_of_mem hin, h.2.2.1 o hoG hoy hsD]
    exact (Finset.card_le_card (presentNeighbours_subset_kept (traceStep D y o) o)).trans
      hcard.le

private theorem step_preserves_unused {G : Finset Plane} {D : Network G}
    {y o x z : Plane} (hlocal : D.LocalRules) (hp : D.Present y o)
    (hD : D.status y = .D → (D.presentNeighbours y).card ≤ 1)
    (hxz : D.Present x z) (hne : ({x, z} : Finset Plane) ≠ {y, o}) :
    (traceStep D y o).Present x z := by
  classical
  have hactive (a b : Plane) (hab : D.Present a b)
      (hdiff : ({a, b} : Finset Plane) ≠ {y, o}) : a ∈ (traceStep D y o).active := by
    have haG : a ∈ G := (Finset.mem_filter.mp hab.1).1
    by_cases hay : a = y
    · subst a
      by_cases hsU : D.status y = .U
      · exact Finset.mem_filter.mpr ⟨haG, by simp [traceStep, hsU]⟩
      · have hsD : D.status y = .D := by
          have hsX := (Finset.mem_filter.mp hab.1).2
          cases hs : D.status y <;> simp_all
        have hbo : b = o := Finset.card_le_one.mp (hD hsD)
          b (present_mem hlocal hab) o (present_mem hlocal hp)
        exact (hdiff (by simp [hbo])).elim
    · exact Finset.mem_filter.mpr ⟨haG, by
        simpa [traceStep, hay] using (Finset.mem_filter.mp hab.1).2⟩
  have hkept (a b : Plane) (hab : D.Present a b)
      (hdiff : ({a, b} : Finset Plane) ≠ {y, o}) : b ∈ (traceStep D y o).kept a := by
    by_cases hay : a = y
    · have hbo : b ≠ o := by intro h; exact hdiff (by simp [hay, h])
      simpa [traceStep, hay, hbo] using hab.2.2.2.1
    · by_cases hao : a = o
      · have hby : b ≠ y := by
          intro h
          exact hdiff (by simp [hao, h, Finset.pair_comm])
        have hoy : o ≠ y := by simpa [hao] using hay
        simpa [traceStep, hay, hao, hoy, hby] using hab.2.2.2.1
      · simpa [traceStep, hay, hao] using hab.2.2.2.1
  have hne' : ({z, x} : Finset Plane) ≠ {y, o} := by
    simpa only [Finset.pair_comm z x] using hne
  exact ⟨hactive x z hxz hne, hactive z x (present_symm hxz) hne', hxz.2.2.1,
    hkept x z hxz hne, hkept z x (present_symm hxz) hne'⟩

private theorem initial_invariant (p : PairSetup) : PrefixInvariant p.normalized p.u := by
  classical
  obtain ⟨hcons, hu, hv, hcG, hcX, huc, hvc, htype, hustart, hvstart⟩ := p.pair
  have haux : p.D.Auxiliary := ⟨hcons.1.1, fun x hx => (hcons.1.2 x hx).1⟩
  have huG : p.u ∈ p.G := (Finset.mem_filter.mp hu).1
  refine ⟨normalize_auxiliary p.D p.u p.c haux, ?_, ?_, ?_, ?_⟩
  · intro x hx hxu hs
    have hsU : p.D.status x = .U := hs
    simpa [PairData.normalized, normalizeStart, hxu] using hcons.2.1 x hx hsU
  · intro x hx hxu hs
    have hsD : p.D.status x = .D := hs
    simpa [PairData.normalized, normalizeStart, hxu] using hcons.2.2.1 x hx hsD
  · intro hs
    have hsU : p.D.status p.u = .U := hs
    have hun : p.u ∈ neighbours p.c :=
      Finset.mem_image.mpr ⟨p.incoming, Finset.mem_univ _, p.incoming_eq.symm⟩
    refine ⟨p.c, Finset.mem_inter.mpr ⟨neighbours_symm hun, hcG⟩, ?_⟩
    simp only [PairData.normalized, normalizeStart, hsU, and_self, ite_true]
    rw [hcons.2.1 p.u huG hsU]
  · intro hs
    have hsD : p.D.status p.u = .D := hs
    have hdeg : (p.D.presentNeighbours p.u).card ≤ 1 := by
      rcases hustart with hsU | ⟨_, hd⟩
      · simp [hsD] at hsU
      · exact hd
    exact (Finset.card_le_card (normalize_neighbours_subset p.D p.u p.c p.u)).trans hdeg

/-- Simultaneously track the kept-set invariant and the bonds still to be used.
Removing a D site cannot destroy another future bond: its current degree is at
most one, and that bond is the one just traversed. -/
private theorem prefix_invariant (p : PairSetup) (T : Finset Plane) (n : ℕ)
    (w : DirectionWord n) (ht : StoppedNetworkTrail p.normalized p.u T w) :
    ∀ j ≤ n,
      PrefixInvariant (prefixNetwork p.normalized p.u w j) (wordVertex p.u w j) ∧
      ∀ i : Fin n, j ≤ i.val →
        (prefixNetwork p.normalized p.u w j).Present
          (wordVertex p.u w i.val) (wordVertex p.u w (i.val + 1)) := by
  intro j
  induction j with
  | zero =>
      intro hj
      constructor
      · simpa [prefix_zero, wordVertex] using initial_invariant p
      · intro i hi
        rw [prefix_zero]
        exact ht.2.1 i
  | succ j ih =>
      intro hj
      have hjn : j < n := by omega
      obtain ⟨hinv, hfuture⟩ := ih (by omega)
      have hp := hfuture ⟨j, hjn⟩ (Nat.le_refl j)
      have hyS := (ht.2.2.1 j hjn).2
      rw [prefix_succ p.normalized p.u w j hjn]
      constructor
      · exact invariant_step hinv hp hyS
      · intro i hi
        apply step_preserves_unused hinv.1.1 hp hinv.2.2.2.2 (hfuture i (by omega))
        change wordBond p.u w i ≠ wordBond p.u w ⟨j, hjn⟩
        apply ht.1.ne
        intro heq
        have hval := congrArg Fin.val heq
        simp only at hval
        omega

/-- The strengthened kept-set invariant at every stopped-trail prefix. -/
theorem main : AKLT.Blueprint.Rec.KeptInvariantStatement := by
  intro p T n w ht j hj
  have h := (prefix_invariant p T n w ht j hj).1
  exact ⟨h.1, h.2.1, h.2.2.1,
    prefix_mutual p T n w ht j hj, prefix_no_return p T n w ht j hj⟩

end AKLT.W.REC050
