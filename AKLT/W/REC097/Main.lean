module
public import AKLT.Blueprint.Rec.NodesV2Closure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC097

private theorem traceNetwork_append_singleton {G : Finset Plane} (D : Network G) :
    ∀ (L : List Plane) (x : Plane),
      traceNetwork D (L ++ [x]) =
        match L.getLast? with
        | none => D
        | some y => traceStep (traceNetwork D L) y x := by
  intro L
  induction L generalizing D with
  | nil => intro x; simp [traceNetwork]
  | cons y L ih =>
    intro x
    cases L with
    | nil => simp [traceNetwork]
    | cons z zs =>
      simp only [List.cons_append, traceNetwork]
      have hl : (y :: z :: zs).getLast? = (z :: zs).getLast? := by simp
      rw [hl]
      change traceNetwork (traceStep D y z) ((z :: zs) ++ [x]) = _
      rw [ih (D := traceStep D y z)]
      simp [List.getLast?_cons]

private theorem wordVertices_lastPrefix {n : ℕ}
    (u : Plane) (w : DirectionWord n) {j : ℕ} (hj : j ≤ n) :
    ((wordVertices u w).take (j + 1)).getLast? = some (wordVertex u w j) := by
  unfold wordVertices
  rw [← List.map_take]
  simp [List.take_range, Nat.min_eq_left (Nat.succ_le_succ hj), List.getLast?_map,
    List.getLast?_range]

private theorem wordVertices_index {n : ℕ}
    (u : Plane) (w : DirectionWord n) {j : ℕ} (hj : j ≤ n) :
    (wordVertices u w)[j]? = some (wordVertex u w j) := by
  unfold wordVertices
  rw [List.getElem?_map]
  have hr : j < (List.range (n + 1)).length := by simp; omega
  rw [List.getElem?_eq_getElem hr]
  simp [List.getElem_range]

private theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n)
    {j : ℕ} (hj : j < n) :
    wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step := by
  unfold wordVertex
  have hsum :
      (∑ i : Fin n, if i.val < j + 1 then (w i).step else 0) =
        (∑ i : Fin n, if i.val < j then (w i).step else 0) +
          (∑ i : Fin n, if i.val = j then (w i).step else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hlt : i.val < j <;> by_cases heq : i.val = j <;>
      simp [hlt, heq] <;> omega
  have hsingle :
      (∑ i : Fin n, if i.val = j then (w i).step else 0) = (w ⟨j, hj⟩).step := by
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro i hi hne
      have hval : i.val ≠ j := by
        intro h
        apply hne
        exact Fin.ext h
      simp [hval]
    · simp
  rw [hsum, hsingle]
  abel

private def prefixArrival {n : ℕ} (u c : Plane) (w : DirectionWord n) : ℕ → Plane
  | 0 => c
  | j + 1 => wordVertex u w j

private theorem prefixNetwork_succ {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n) {j : ℕ} (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  have hsplit : (wordVertices u w).take (j + 2) =
      (wordVertices u w).take (j + 1) ++ [wordVertex u w (j + 1)] := by
    rw [List.take_succ]
    have hi := wordVertices_index u w (j := j + 1) (by omega)
    simp [hi]
  unfold prefixNetwork
  rw [hsplit, traceNetwork_append_singleton, wordVertices_lastPrefix u w (by omega)]

private theorem neighbors_card (x : Plane) : (neighbors x).card = 4 := by
  unfold neighbors
  rw [Finset.card_image_of_injective]
  · simpa using (show Fintype.card Compass = 4 by decide)
  · intro a b hab
    cases a <;> cases b <;> simp [Compass.step] at hab ⊢

private theorem adjacent_of_mem_neighbors {x z : Plane} (hz : z ∈ neighbors x) : Adjacent x z := by
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and] at hz
  rcases hz with ⟨d, rfl⟩
  cases d <;> norm_num [Adjacent, latticeDist, Compass.step]

private theorem mem_neighbors_of_adjacent {x z : Plane} (h : Adjacent x z) :
    z ∈ neighbors x := by
  have hdist : (x.1 - z.1).natAbs + (x.2 - z.2).natAbs = 1 := h
  have hzero : (x.1 - z.1).natAbs = 0 ∨ (x.2 - z.2).natAbs = 0 := by omega
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and]
  rcases hzero with hfirst | hsecond
  · have heq : x.1 - z.1 = 0 := Int.natAbs_eq_zero.mp hfirst
    have hval : (x.2 - z.2).natAbs = 1 := by omega
    rcases Int.natAbs_eq_iff.mp hval with hval | hval
    · refine ⟨.south, ?_⟩
      simp [Compass.step, Prod.ext_iff, heq, hval] <;> omega
    · refine ⟨.north, ?_⟩
      simp [Compass.step, Prod.ext_iff, heq, hval] <;> omega
  · have heq : x.2 - z.2 = 0 := Int.natAbs_eq_zero.mp hsecond
    have hval : (x.1 - z.1).natAbs = 1 := by omega
    rcases Int.natAbs_eq_iff.mp hval with hval | hval
    · refine ⟨.west, ?_⟩
      simp [Compass.step, Prod.ext_iff, heq, hval] <;> omega
    · refine ⟨.east, ?_⟩
      simp [Compass.step, Prod.ext_iff, heq, hval] <;> omega

private theorem ne_of_adjacent {x z : Plane} (h : Adjacent x z) : x ≠ z := by
  intro he
  subst z
  simp [Adjacent, latticeDist] at h

private theorem adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x := by
  unfold Adjacent latticeDist at h ⊢
  calc
    (z.1 - x.1).natAbs + (z.2 - x.2).natAbs =
        (x.1 - z.1).natAbs + (x.2 - z.2).natAbs := by
          rw [show z.1 - x.1 = -(x.1 - z.1) by omega,
            show z.2 - x.2 = -(x.2 - z.2) by omega,
            Int.natAbs_neg, Int.natAbs_neg]
    _ = 1 := h

private theorem active_mem_G {G : Finset Plane} {D : Network G} {x : Plane}
    (h : x ∈ D.active) : x ∈ G := Finset.mem_filter.mp h |>.1

private theorem present_kept_right {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : z ∈ D.kept x := h.2.2.2.1

private theorem present_kept_left {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : x ∈ D.kept z := h.2.2.2.2

private def NoUsedBond : List Plane → Plane → Plane → Prop
  | y :: z :: rest, x, t => ({x, t} : Finset Plane) ≠ {y, z} ∧ NoUsedBond (z :: rest) x t
  | _, _, _ => True

private theorem traceNetwork_kept_mem_of_unused {G : Finset Plane} (D : Network G)
    (L : List Plane) (x z : Plane) (hxz : x ≠ z) (hz : z ∈ D.kept x)
    (hno : NoUsedBond L x z) : z ∈ (traceNetwork D L).kept x := by
  induction L generalizing D with
  | nil => simpa [traceNetwork] using hz
  | cons y L ih =>
    cases L with
    | nil => simpa [traceNetwork] using hz
    | cons o rest =>
      rcases hno with ⟨hneq, htail⟩
      have hz' : z ∈ (traceStep D y o).kept x := by
        by_cases hxy : x = y
        · subst x
          have hzo : z ≠ o := by
            intro h; apply hneq; subst z; simp
          simp [traceStep, hzo, hz]
        · by_cases hxo : x = o
          · subst x
            have hzy : z ≠ y := by
              intro h; apply hneq; subst z; simpa [Finset.pair_comm]
            simp only [traceStep, if_neg hxy]
            exact Finset.mem_erase.mpr ⟨hzy, hz⟩
          · simp [traceStep, hxy, hxo, hz]
      exact ih (D := traceStep D y o) hz' htail

private theorem traceStep_kept_mem_of_bond_ne {G : Finset Plane} (D : Network G)
    {x z y o : Plane} (hxz : x ≠ z) (hz : z ∈ D.kept x)
    (hbond : ({x, z} : Finset Plane) ≠ {y, o}) : z ∈ (traceStep D y o).kept x := by
  by_cases hxy : x = y
  · subst x
    have hzo : z ≠ o := by
      intro h
      apply hbond
      subst z
      simp
    simp [traceStep, hzo, hz]
  · by_cases hxo : x = o
    · subst x
      have hzy : z ≠ y := by
        intro h
        apply hbond
        subst z
        simpa [Finset.pair_comm]
      simp only [traceStep, if_neg hxy]
      exact Finset.mem_erase.mpr ⟨hzy, hz⟩
    · simp [traceStep, hxy, hxo, hz]

private theorem prefix_kept_of_noEarlierBond {G : Finset Plane} {n : ℕ}
    (D : Network G) (u : Plane) (w : DirectionWord n) {j : ℕ} (hj : j ≤ n)
    (x z : Plane) (hxz : x ≠ z) (hz : z ∈ D.kept x)
    (hno : ∀ k (hk : k < j),
      wordBond u w ⟨k, by omega⟩ ≠ ({x, z} : Finset Plane)) :
    z ∈ (prefixNetwork D u w j).kept x := by
  induction j with
  | zero =>
    change z ∈ (traceNetwork D (((List.range (n + 1)).map (wordVertex u w)).take 1)).kept x
    rw [← List.map_take]
    simpa [List.take_range, traceNetwork, wordVertex] using hz
  | succ j ih =>
    have hjlt : j < n := by omega
    have hprev : ∀ k (hk : k < j),
        wordBond u w ⟨k, by omega⟩ ≠ ({x, z} : Finset Plane) := by
      intro k hk
      exact hno k (by omega)
    have hzprev := ih (by omega) hprev
    have hstepneq : ({x, z} : Finset Plane) ≠
        {wordVertex u w j, wordVertex u w (j + 1)} := by
      intro he
      have hedge : wordBond u w ⟨j, hjlt⟩ = ({x, z} : Finset Plane) := by
        simpa [wordBond] using he.symm
      exact hno j (by omega) hedge
    rw [prefixNetwork_succ D u w hjlt]
    exact traceStep_kept_mem_of_bond_ne (prefixNetwork D u w j) hxz hzprev hstepneq

private theorem prefix_edge_kept {G : Finset Plane} {n : ℕ} {T : Finset Plane}
    {D : Network G} {u : Plane} {w : DirectionWord n} {j : ℕ}
    (htrail : StoppedNetworkTrail D u T w) (hj : j < n) :
    wordVertex u w (j + 1) ∈ (prefixNetwork D u w j).kept (wordVertex u w j) := by
  have hbondD : D.Present (wordVertex u w j) (wordVertex u w (j + 1)) := htrail.2.1 ⟨j, hj⟩
  have hdistinct : wordVertex u w j ≠ wordVertex u w (j + 1) :=
    ne_of_adjacent hbondD.2.2.1
  apply prefix_kept_of_noEarlierBond D u w (j := j) (by omega)
    (wordVertex u w j) (wordVertex u w (j + 1)) hdistinct (present_kept_right hbondD)
  intro k hk
  intro he
  have hklt : k < n := by omega
  have he' : wordBond u w ⟨k, hklt⟩ = wordBond u w ⟨j, hj⟩ := by
    simpa [wordBond] using he
  have hEq := htrail.1 he'
  have : k = j := congrArg Fin.val hEq
  omega

private def CoreInvariant {G : Finset Plane} (D : Network G) (y arrival : Plane) : Prop :=
  D.LocalRules ∧
  (∀ x ∈ D.active, x ≠ y → D.status x = .U → D.kept x = neighbors x ∩ G) ∧
  (∀ x ∈ D.active, x ≠ y → D.status x = .D → (D.kept x).card = 2) ∧
  (∀ x ∈ D.active, ∀ z ∈ D.active, Adjacent x z → (z ∈ D.kept x ↔ x ∈ D.kept z)) ∧
  (∀ x ∈ protectedSites G, D.status x = .U ∧ D.kept x = neighbors x ∩ G) ∧
  (D.status y = .U → D.kept y = (neighbors y ∩ G).erase arrival)

private theorem notProtected_neighbors_in_G {G : Finset Plane} {y : Plane}
    (hyG : y ∈ G) (hyS : y ∉ protectedSites G) : neighbors y ⊆ G := by
  intro z hz
  by_contra hzg
  have hbd : boundaryDepth G y ≤ (1 : ℕ∞) := by
    unfold boundaryDepth
    exact le_trans (iInf_le (fun q : {z : Plane // z ∉ G} =>
      (latticeDist y q.val : ℕ∞)) ⟨z, hzg⟩)
      (by rw [adjacent_of_mem_neighbors hz]; norm_num)
  have hmem : y ∈ protectedSites G := by
    unfold protectedSites
    rw [Finset.mem_filter]
    exact ⟨hyG, le_trans hbd (by norm_num)⟩
  exact hyS hmem

private theorem normalize_kept_mem_iff {G : Finset Plane} (D : Network G)
    (u c x y : Plane) (hcX : D.status c = .X) (hx : x ∈ D.active) :
    x ∈ (normalizeStart D u c).kept y ↔ x ∈ D.kept y := by
  have hxc : x ≠ c := by
    intro h
    subst x
    exact (Finset.mem_filter.mp hx).2 hcX
  by_cases hy : y = u <;> by_cases hu : D.status u = .U <;>
    simp [normalizeStart, hy, hu, hxc]

private theorem normalize_present_iff {G : Finset Plane} (D : Network G)
    (u c x y : Plane) (hcX : D.status c = .X) :
    (normalizeStart D u c).Present x y ↔ D.Present x y := by
  constructor
  · intro h
    rcases h with ⟨hx, hy, hadj, hyx, hxy⟩
    have hx' : x ∈ D.active := hx
    have hy' : y ∈ D.active := hy
    exact ⟨hx', hy', hadj,
      (normalize_kept_mem_iff D u c y x hcX hy').mp hyx,
      (normalize_kept_mem_iff D u c x y hcX hx').mp hxy⟩
  · intro h
    rcases h with ⟨hx, hy, hadj, hyx, hxy⟩
    exact ⟨hx, hy, hadj,
      (normalize_kept_mem_iff D u c y x hcX hy).mpr hyx,
      (normalize_kept_mem_iff D u c x y hcX hx).mpr hxy⟩

private theorem normalize_presentNeighbors_eq {G : Finset Plane} (D : Network G)
    (u c x : Plane) (hcX : D.status c = .X) :
    (normalizeStart D u c).presentNeighbors x = D.presentNeighbors x := by
  ext z
  simp only [Network.presentNeighbors, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hp⟩
    exact ⟨hz, (normalize_present_iff D u c x z hcX).mp hp⟩
  · rintro ⟨hz, hp⟩
    exact ⟨hz, (normalize_present_iff D u c x z hcX).mpr hp⟩

private theorem normalize_core_of_consistent {G : Finset Plane} (D : Network G)
    (u c : Plane) (hD : D.Consistent) (huActive : u ∈ D.active)
    (huS : u ∉ protectedSites G) (hcX : D.status c = .X) :
    CoreInvariant (normalizeStart D u c) u c := by
  rcases hD with ⟨⟨hLocal, hProtected⟩, hU, hDcard, hmut⟩
  have huG : u ∈ G := active_mem_G huActive
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Network.LocalRules
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      simpa [normalizeStart] using hLocal.1 x hx
    · intro x z hz
      have hzD : z ∈ D.kept x := by
        by_cases hxu : x = u ∧ D.status u = .U
        · exact (Finset.mem_erase.mp (by simpa [normalizeStart, hxu] using hz)).2
        · simpa [normalizeStart, hxu] using hz
      exact (hLocal.2.1 x hzD)
    · intro x hxG hxD
      rw [normalize_presentNeighbors_eq D u c x hcX]
      exact hLocal.2.2.1 x hxG (by simpa [normalizeStart] using hxD)
    · intro x hxActive
      have hxD : x ∈ D.active := hxActive
      rw [normalize_presentNeighbors_eq D u c x hcX]
      exact hLocal.2.2.2 x hxD
  · intro x hxActive hxu hxU
    have hxD : x ∈ D.active := hxActive
    have hxG : x ∈ G := active_mem_G hxD
    have hxkept : (normalizeStart D u c).kept x = D.kept x := by
      simp [normalizeStart, hxu]
    rw [hxkept]
    exact hU x hxG (by simpa [normalizeStart] using hxU)
  · intro x hxActive hxu hxD
    have hxG : x ∈ G := active_mem_G hxActive
    have hxkept : (normalizeStart D u c).kept x = D.kept x := by
      simp [normalizeStart, hxu]
    rw [hxkept]
    exact hDcard x hxG (by simpa [normalizeStart] using hxD)
  · intro x hx z hz hadj
    have hxD : x ∈ D.active := hx
    have hzD : z ∈ D.active := hz
    rw [normalize_kept_mem_iff D u c z x hcX hzD,
      normalize_kept_mem_iff D u c x z hcX hxD]
    exact hmut x hxD z hzD hadj
  · intro x hxS
    have hxu : x ≠ u := by
      intro h
      subst x
      exact huS hxS
    have hstatus : (normalizeStart D u c).status x = D.status x := rfl
    have hkept : (normalizeStart D u c).kept x = D.kept x := by simp [normalizeStart, hxu]
    rw [hstatus, hkept]
    exact hProtected x hxS
  · intro huU
    have huStatus : D.status u = .U := by simpa [normalizeStart] using huU
    have hkept : (normalizeStart D u c).kept u = (D.kept u).erase c := by
      simp [normalizeStart, huStatus]
    rw [hkept, hU u huG huStatus]

private theorem traceStep_active_backward {G : Finset Plane} (D : Network G)
    (y o x : Plane) (hx : x ∈ (traceStep D y o).active) : x ∈ D.active := by
  by_cases hxy : x = y
  · subst x
    simp only [Network.active, Finset.mem_filter, traceStep, Function.update] at hx
    rcases hx with ⟨hyG, hyStatus⟩
    by_cases hs : D.status y = .U
    · change y ∈ G.filter (fun x => D.status x ≠ .X)
      exact Finset.mem_filter.mpr ⟨hyG, by simpa [hs]⟩
    · simp [hs] at hyStatus
  · simpa [Network.active, Finset.mem_filter, traceStep, Function.update, hxy] using hx

private theorem traceStep_kept_mem_backward {G : Finset Plane} (D : Network G)
    (y o x z : Plane) (hz : z ∈ (traceStep D y o).kept x) : z ∈ D.kept x := by
  by_cases hxy : x = y
  · subst x
    have : z ∈ (D.kept y).erase o := by simpa [traceStep] using hz
    exact (Finset.mem_erase.mp this).2
  · by_cases hxo : x = o
    · subst x
      have : z ∈ (D.kept o).erase y := by simpa [traceStep, hxy] using hz
      exact (Finset.mem_erase.mp this).2
    · simpa [traceStep, hxy, hxo] using hz

private theorem traceStep_presentNeighbors_subset {G : Finset Plane} (D : Network G)
    (y o x : Plane) : (traceStep D y o).presentNeighbors x ⊆ D.presentNeighbors x := by
  intro z hz
  have hz' : z ∈ (traceStep D y o).presentNeighbors x := hz
  simp only [Network.presentNeighbors, Finset.mem_filter] at hz' ⊢
  rcases hz' with ⟨hzNbr, hp⟩
  rcases hp with ⟨hxA, hzA, hadj, hzx, hxz⟩
  have hxOld := traceStep_active_backward D y o x hxA
  have hzOld := traceStep_active_backward D y o z hzA
  exact ⟨hzNbr, ⟨hxOld, hzOld, hadj,
    traceStep_kept_mem_backward D y o x z hzx,
    traceStep_kept_mem_backward D y o z x hxz⟩⟩

private theorem traceStep_kept_mem_iff {G : Finset Plane} (D : Network G)
    (y o x z : Plane) (hyo : y ≠ o) :
    z ∈ (traceStep D y o).kept x ↔
      z ∈ D.kept x ∧ (x = y → z ≠ o) ∧ (x = o → z ≠ y) := by
  by_cases hxy : x = y
  · subst x
    simp [traceStep, hyo, and_comm, and_left_comm, and_assoc]
  · by_cases hxo : x = o
    · subst x
      simp [traceStep, hxy, hyo, and_comm, and_left_comm, and_assoc]
    · simp [traceStep, hxy, hxo]

private theorem traceStep_core {G : Finset Plane} (E : Network G) (y arrival o : Plane)
    (hCore : CoreInvariant E y arrival) (hyG : y ∈ G) (hoG : o ∈ G)
    (harrivalNbr : arrival ∈ neighbors y) (hyS : y ∉ protectedSites G) (hoS : o ∉ protectedSites G)
    (hyo : Adjacent y o) (hkeptYO : o ∈ E.kept y) :
    CoreInvariant (traceStep E y o) o y := by
  rcases hCore with ⟨hLocal, hUfull, hDcard, hmut, hProt, hLive⟩
  let E' := traceStep E y o
  have hyne : y ≠ o := ne_of_adjacent hyo
  have hcardY : E.status y = .U → (E'.kept y).card = 2 := by
    intro hs
    have hkept : E'.kept y = (E.kept y).erase o := by simp [E', traceStep]
    have hinter : neighbors y ∩ G = neighbors y :=
      Finset.inter_eq_left.mpr (notProtected_neighbors_in_G hyG hyS)
    have hsource : E.kept y = (neighbors y).erase arrival := by
      rw [hLive hs, hinter]
    have hoBase : o ∈ (neighbors y).erase arrival := by
      rw [← hsource]
      exact hkeptYO
    have hor : o ≠ arrival := (Finset.mem_erase.mp hoBase).1
    have hoNbr : o ∈ neighbors y := (Finset.mem_erase.mp hoBase).2
    have hmem : o ∈ (neighbors y).erase arrival := Finset.mem_erase.mpr ⟨hor, hoNbr⟩
    rw [hkept, hsource, Finset.card_erase_of_mem hmem,
      Finset.card_erase_of_mem harrivalNbr, neighbors_card]
  have hpnKept : E'.presentNeighbors y ⊆ E'.kept y := by
    intro z hz
    simp only [Network.presentNeighbors, Finset.mem_filter] at hz
    simp only [Network.Present] at hz
    exact hz.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Network.LocalRules
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hxG
      have hxy : x ≠ y := by
        intro h
        subst x
        exact hxG hyG
      simpa [E', traceStep, hxy] using hLocal.1 x hxG
    · intro x z hz
      have hzE : z ∈ E.kept x := by
        by_cases hxy : x = y
        · subst x
          exact (Finset.mem_erase.mp (by simpa [E', traceStep] using hz)).2
        · by_cases hxo : x = o
          · subst x
            exact (Finset.mem_erase.mp (by simpa [E', traceStep, hxy] using hz)).2
          · simpa [E', traceStep, hxy, hxo] using hz
      exact hLocal.2.1 x hzE
    · intro x hxG hxD
      by_cases hxy : x = y
      · subst x
        have hs : E.status y = .U := by simpa [E', traceStep] using hxD
        have hcard : (E'.presentNeighbors y).card ≤ (E'.kept y).card :=
          Finset.card_le_card hpnKept
        rw [hcardY hs] at hcard
        exact hcard
      · have hsD : E.status x = .D := by simpa [E', traceStep, hxy] using hxD
        exact (Finset.card_le_card (traceStep_presentNeighbors_subset E y o x)).trans
          (hLocal.2.2.1 x hxG hsD)
    · intro x hxActive
      have hxOld : x ∈ E.active := traceStep_active_backward E y o x hxActive
      have hcard : (E'.presentNeighbors x).card ≤ (E.presentNeighbors x).card :=
        Finset.card_le_card (traceStep_presentNeighbors_subset E y o x)
      have hfactor := hLocal.2.2.2 x hxOld
      exact (Nat.add_le_add_right hcard _).trans hfactor
  · intro x hxActive hxy hxU
    by_cases hxyLive : x = y
    · subst x
      cases hs : E.status y <;> simp [E', traceStep, hs] at hxU
    · have hxOld : x ∈ E.active := traceStep_active_backward E y o x hxActive
      have hxUold : E.status x = .U := by simpa [E', traceStep, hxyLive] using hxU
      have hxkept : E'.kept x = E.kept x := by simp [E', traceStep, hxyLive, hxy]
      rw [hxkept]
      exact hUfull x hxOld hxyLive hxUold
  · intro x hxActive hxy hxD
    by_cases hxyLive : x = y
    · subst x
      have hs : E.status y = .U := by simpa [E', traceStep] using hxD
      exact hcardY hs
    · have hxOld : x ∈ E.active := traceStep_active_backward E y o x hxActive
      have hxDold : E.status x = .D := by simpa [E', traceStep, hxyLive] using hxD
      have hxkept : E'.kept x = E.kept x := by simp [E', traceStep, hxyLive, hxy]
      rw [hxkept]
      exact hDcard x hxOld hxyLive hxDold
  · intro x hxActive z hzActive hadj
    have hxOld : x ∈ E.active := traceStep_active_backward E y o x hxActive
    have hzOld : z ∈ E.active := traceStep_active_backward E y o z hzActive
    by_cases hxy : x = y
    · subst x
      by_cases hzo : z = o
      · subst z
        have hmem₁ := traceStep_kept_mem_iff E y o y o hyne
        have hmem₂ := traceStep_kept_mem_iff E y o o y hyne
        simp [E'] at hmem₁ hmem₂
        simp [E', hmem₁, hmem₂]
      · have hmutOld := hmut y hxOld z hzOld hadj
        have hzy : z ≠ y := ne_of_adjacent (adjacent_symm hadj)
        have hmem₁ : z ∈ E'.kept y ↔ z ∈ E.kept y := by
          simpa [E', hzo, hzy] using (traceStep_kept_mem_iff E y o y z hyne)
        have hmem₂ : y ∈ E'.kept z ↔ y ∈ E.kept z := by
          simpa [E', hzo, hzy] using (traceStep_kept_mem_iff E y o z y hyne)
        rw [hmem₁, hmem₂]
        exact hmutOld
    · by_cases hzy : z = y
      · subst z
        by_cases hxo : x = o
        · subst x
          have hmem₁ := traceStep_kept_mem_iff E y o o y hyne
          have hmem₂ := traceStep_kept_mem_iff E y o y o hyne
          simp [E'] at hmem₁ hmem₂
          simp [E', hmem₁, hmem₂]
        · have hmutOld := hmut x hxOld y hzOld hadj
          have hxy' : x ≠ y := hxy
          have hmem₁ : y ∈ E'.kept x ↔ y ∈ E.kept x := by
            simpa [E', hxy', hxo] using (traceStep_kept_mem_iff E y o x y hyne)
          have hmem₂ : x ∈ E'.kept y ↔ x ∈ E.kept y := by
            simpa [E', hxy', hxo] using (traceStep_kept_mem_iff E y o y x hyne)
          rw [hmem₁, hmem₂]
          exact hmutOld
      · have hmem₁ : z ∈ E'.kept x ↔ z ∈ E.kept x := by
          by_cases hxo : x = o
          · subst x
            simpa [E', hzy, (Ne.symm hyne)] using
              (traceStep_kept_mem_iff E y o o z hyne)
          · simpa [E', hxy, hxo] using (traceStep_kept_mem_iff E y o x z hyne)
        have hmem₂ : x ∈ E'.kept z ↔ x ∈ E.kept z := by
          by_cases hzo : z = o
          · subst z
            simpa [E', hxy, (Ne.symm hyne)] using
              (traceStep_kept_mem_iff E y o o x hyne)
          · simpa [E', hzy, hzo] using (traceStep_kept_mem_iff E y o z x hyne)
        rw [hmem₁, hmem₂]
        exact hmut x hxOld z hzOld hadj
  · intro x hxS
    have hxy : x ≠ y := by intro h; subst x; exact hyS hxS
    have hxo : x ≠ o := by intro h; subst x; exact hoS hxS
    have hxstat : E'.status x = E.status x := by simp [E', traceStep, hxy]
    have hxkeep : E'.kept x = E.kept x := by simp [E', traceStep, hxy, hxo]
    rw [hxstat, hxkeep]
    exact hProt x hxS
  · intro hoU
    have hoyne : o ≠ y := Ne.symm hyne
    have hoUold : E.status o = .U := by simpa [E', traceStep, hyne, hoyne] using hoU
    have hoActive : o ∈ E.active := by
      change o ∈ G.filter (fun x => E.status x ≠ .X)
      exact Finset.mem_filter.mpr ⟨hoG, by simpa [hoUold]⟩
    have hFull := hUfull o hoActive hoyne hoUold
    have hkept : E'.kept o = (E.kept o).erase y := by simp [E', traceStep, hyne, hoyne]
    rw [hkept, hFull]

private theorem prefix_core (p : PairSetup) (T : Finset Plane)
    {n : ℕ} (w : DirectionWord n)
    (htrail : StoppedNetworkTrail p.normalized p.u T w) (i : Fin n) :
    CoreInvariant (prefixNetwork p.normalized p.u w i.val)
      (wordVertex p.u w i.val) (prefixArrival p.u p.c w i.val) := by
  let D := p.normalized
  have htrailD : StoppedNetworkTrail D p.u T w := htrail
  rcases p.pair with ⟨hCons, huActive, _, hcG, hcX, huc, _, _, _, _⟩
  have hInv : ∀ j ≤ i.val, CoreInvariant (prefixNetwork D p.u w j)
      (wordVertex p.u w j) (prefixArrival p.u p.c w j) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hbase := normalize_core_of_consistent p.D p.u p.c hCons huActive p.interior hcX
      have hprefix0 : prefixNetwork D p.u w 0 = D := by
        unfold prefixNetwork wordVertices
        rw [← List.map_take]
        simp [List.take_range, wordVertex, traceNetwork]
      rw [hprefix0]
      simp only [prefixArrival]
      simpa [wordVertex, PairData.normalized, D] using hbase
    | succ j ih =>
      intro hj
      have hjlt : j < n := by omega
      have hj1lt : j + 1 < n := by omega
      have hprev := ih (by omega)
      let y := wordVertex p.u w j
      let o := wordVertex p.u w (j + 1)
      have hbond : D.Present y o := htrailD.2.1 ⟨j, hjlt⟩
      have hyG : y ∈ p.G := active_mem_G hbond.1
      have hoG : o ∈ p.G := active_mem_G hbond.2.1
      have hyo : Adjacent y o := hbond.2.2.1
      have hyS : y ∉ protectedSites p.G := (htrailD.2.2.1 j hjlt).2
      have hoS : o ∉ protectedSites p.G := (htrailD.2.2.1 (j + 1) hj1lt).2
      have hArrivalNbr : prefixArrival p.u p.c w j ∈ neighbors y := by
        cases j with
        | zero => simpa [y, prefixArrival, wordVertex] using mem_neighbors_of_adjacent huc
        | succ k =>
          have hklt : k < n := by omega
          have hprevBond : D.Present (wordVertex p.u w k)
              (wordVertex p.u w (k + 1)) := htrailD.2.1 ⟨k, hklt⟩
          simpa [y, prefixArrival] using
            (mem_neighbors_of_adjacent (adjacent_symm hprevBond.2.2.1))
      have hkept := prefix_edge_kept htrailD hjlt
      have hnext := traceStep_core (prefixNetwork D p.u w j) y
        (prefixArrival p.u p.c w j) o hprev hyG hoG hArrivalNbr hyS hoS hyo hkept
      rw [prefixNetwork_succ D p.u w hjlt]
      simpa [y, o, prefixArrival] using hnext
  exact hInv i.val (by omega)

private theorem removeSite_active_backward {G : Finset Plane} (E : Network G)
    (y x : Plane) (hx : x ∈ (removeSite E y).active) : x ∈ E.active := by
  simp only [Network.active, Finset.mem_filter] at hx
  by_cases hxy : x = y
  · subst x
    simp [removeSite] at hx
  · rcases hx with ⟨hxG, hxStatus⟩
    have hxStatusOld : E.status x ≠ .X := by
      simpa [removeSite, hxy] using hxStatus
    exact Finset.mem_filter.mpr ⟨hxG, hxStatusOld⟩

private theorem removeSite_presentNeighbors_subset {G : Finset Plane} (E : Network G)
    (y x : Plane) : (removeSite E y).presentNeighbors x ⊆ E.presentNeighbors x := by
  intro z hz
  simp only [Network.presentNeighbors, Finset.mem_filter] at hz ⊢
  rcases hz with ⟨hzNbr, ⟨hxActive, hzActive, hadj, hzx, hxz⟩⟩
  have hxOld := removeSite_active_backward E y x hxActive
  have hzOld := removeSite_active_backward E y z hzActive
  exact ⟨hzNbr, ⟨hxOld, hzOld, hadj, hzx, hxz⟩⟩

private theorem removeSite_consistent_of_core {G : Finset Plane} (E : Network G)
    (y arrival : Plane) (hCore : CoreInvariant E y arrival)
    (hyG : y ∈ G) (hyS : y ∉ protectedSites G) :
    (removeSite E y).Consistent := by
  rcases hCore with ⟨hLocal, hUfull, hDcard, hmut, hProt, hLive⟩
  let E' := removeSite E y
  have hyInactive : y ∉ E'.active := by simp [E', Network.active, removeSite]
  have hKeep : ∀ x, E'.kept x = E.kept x := by intro x; rfl
  have hProt' : ∀ x ∈ protectedSites G,
      E'.status x = .U ∧ E'.kept x = neighbors x ∩ G := by
    intro x hxS
    have hxy : x ≠ y := by intro h; subst x; exact hyS hxS
    have hstatus : E'.status x = E.status x := by simp [E', removeSite, hxy]
    rw [hstatus, hKeep]
    exact hProt x hxS
  unfold Network.Consistent
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Network.Ordinary
    refine ⟨?_, hProt'⟩
    unfold Network.LocalRules
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hxG
      have hxy : x ≠ y := by intro h; subst x; exact hxG hyG
      simpa [E', removeSite, hxy] using hLocal.1 x hxG
    · intro x z hz
      change z ∈ E.kept x at hz
      exact hLocal.2.1 x hz
    · intro x hxG hxD
      by_cases hxy : x = y
      · subst x
        simp [E', removeSite] at hxD
      · have hxDold : E.status x = .D := by simpa [E', removeSite, hxy] using hxD
        exact (Finset.card_le_card (removeSite_presentNeighbors_subset E y x)).trans
          (hLocal.2.2.1 x hxG hxDold)
    · intro x hxActive
      have hxOld : x ∈ E.active := removeSite_active_backward E y x hxActive
      have hcard : (E'.presentNeighbors x).card ≤ (E.presentNeighbors x).card :=
        Finset.card_le_card (removeSite_presentNeighbors_subset E y x)
      have hfactor := hLocal.2.2.2 x hxOld
      exact (Nat.add_le_add_right hcard _).trans hfactor
  · intro x hxG hxU
    have hxy : x ≠ y := by
      intro h
      subst x
      simp [E', removeSite] at hxU
    have hxUold : E.status x = .U := by simpa [E', removeSite, hxy] using hxU
    have hxActive : x ∈ E.active := Finset.mem_filter.mpr ⟨hxG, by simp [hxUold]⟩
    exact hUfull x hxActive hxy hxUold
  · intro x hxG hxD
    have hxy : x ≠ y := by
      intro h
      subst x
      simp [E', removeSite] at hxD
    have hxDold : E.status x = .D := by simpa [E', removeSite, hxy] using hxD
    have hxActive : x ∈ E.active := Finset.mem_filter.mpr ⟨hxG, by simp [hxDold]⟩
    exact hDcard x hxActive hxy hxDold
  · intro x hxActive z hzActive hadj
    have hxOld : x ∈ E.active := removeSite_active_backward E y x hxActive
    have hzOld : z ∈ E.active := removeSite_active_backward E y z hzActive
    rw [hKeep, hKeep]
    exact hmut x hxOld z hzOld hadj

private theorem response_type_neighbors {a b y : Plane}
    (ha : a ∈ neighbors y) (hb : b ∈ neighbors y) (hab : a ≠ b) :
    HasPairType (responsePairType {a, b}) a b := by
  classical
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and] at ha hb
  rcases ha with ⟨d, rfl⟩
  rcases hb with ⟨e, he⟩
  subst b
  have hde : d ≠ e := by
    intro h
    subst e
    exact hab rfl
  cases d <;> cases e <;> simp_all [responsePairType, Compass.step, HasPairType,
    latticeDist, Finset.mem_insert, Finset.mem_singleton]

private theorem arrival_eq_prefix {n : ℕ} (p : PairSetup) (w : DirectionWord n)
    (i : Fin n) :
    wordVertex p.u w i.val - (wordIncoming p.incoming w i).step =
      prefixArrival p.u p.c w i.val := by
  by_cases hzero : i.val = 0
  · have hu0 : wordVertex p.u w 0 = p.u := by simp [wordVertex]
    rw [hzero, hu0]
    simp [wordIncoming, hzero]
    rw [p.incoming_eq]
    abel
  · let k := i.val - 1
    have hk : k < n := by dsimp [k]; omega
    have hi : i.val = k + 1 := by dsimp [k]; omega
    have hvertex := wordVertex_succ p.u w hk
    have hidx : (⟨i.val - 1, by omega⟩ : Fin n) = ⟨k, hk⟩ := by
      apply Fin.ext
      rfl
    have hin : wordIncoming p.incoming w i = w ⟨k, hk⟩ := by
      simp only [wordIncoming, dif_neg hzero]
      exact congrArg w hidx
    rw [hi, hvertex, hin]
    simp [prefixArrival, k]

private theorem present_from_nonarrival {G : Finset Plane} (E : Network G)
    (y arrival : Plane) (incoming : Compass) (a : Plane)
    (hCore : CoreInvariant E y arrival)
    (hArrival : y - incoming.step = arrival)
    (hyU : E.status y = .U) (hyG : y ∈ G)
    (ha : a ∈ nonarrivalNeighborsV2 E y incoming) : E.Present y a := by
  classical
  rcases hCore with ⟨_, hU, _, hmut, _, hLive⟩
  have haParts : a ∈ (neighbors y).erase arrival ∧ a ∈ E.active := by
    change a ∈ ((neighbors y).erase (y - incoming.step)) ∩ E.active at ha
    rw [hArrival] at ha
    exact Finset.mem_inter.mp ha
  rcases haParts with ⟨haErase, haActive⟩
  rcases Finset.mem_erase.mp haErase with ⟨hneArrival, haNbr⟩
  have hadj : Adjacent y a := adjacent_of_mem_neighbors haNbr
  have hya : y ≠ a := ne_of_adjacent hadj
  have haG : a ∈ G := active_mem_G haActive
  have haKept : a ∈ E.kept y := by
    rw [hLive hyU]
    exact Finset.mem_erase.mpr ⟨hneArrival, Finset.mem_inter.mpr ⟨haNbr, haG⟩⟩
  have hyActive : y ∈ E.active := Finset.mem_filter.mpr ⟨hyG, by simp [hyU]⟩
  have hyKept : y ∈ E.kept a :=
    (hmut y hyActive a haActive hadj).mp haKept
  exact ⟨hyActive, haActive, hadj, haKept, hyKept⟩

private theorem removed_endpoint_condition {G : Finset Plane} (E : Network G)
    (y x : Plane) (hCons : (removeSite E y).Consistent)
    (hPresent : E.Present y x) (hxy : x ≠ y) :
    (removeSite E y).status x = .U ∨
      ((removeSite E y).status x = .D ∧
        ((removeSite E y).presentNeighbors x).card ≤ 1) := by
  classical
  let E' := removeSite E y
  have hxG : x ∈ G := active_mem_G hPresent.2.1
  have hxActive' : x ∈ E'.active := by
    apply Finset.mem_filter.mpr
    refine ⟨hxG, ?_⟩
    have hstatus : E'.status x = E.status x := by simp [E', removeSite, hxy]
    rw [hstatus]
    exact (Finset.mem_filter.mp hPresent.2.1).2
  have hyInactive : y ∉ E'.active := by simp [E', Network.active, removeSite]
  have hyKept : y ∈ E'.kept x := by
    change y ∈ E.kept x
    exact present_kept_left hPresent
  have hSameKept : E'.kept x = E.kept x := by rfl
  have hsubset : E'.presentNeighbors x ⊆ (E'.kept x).erase y := by
    intro z hz
    simp only [Network.presentNeighbors, Finset.mem_filter] at hz
    rcases hz with ⟨_, hp⟩
    have hzy : z ≠ y := by
      intro h
      subst z
      exact hyInactive hp.2.1
    exact Finset.mem_erase.mpr ⟨hzy, hp.2.2.2.1⟩
  have hDcard : ∀ hD : E'.status x = .D, (E'.kept x).card = 2 := by
    intro hD
    exact hCons.2.2.1 x hxG hD
  cases hxStatus : E.status x with
  | U =>
      left
      simpa [E', removeSite, hxy] using hxStatus
  | D =>
      right
      constructor
      · simpa [E', removeSite, hxy] using hxStatus
      · have hcard := hDcard (by simpa [E', removeSite, hxy] using hxStatus)
        have herase : ((E'.kept x).erase y).card = 1 := by
          rw [Finset.card_erase_of_mem hyKept, hcard]
        calc
          (E'.presentNeighbors x).card ≤ ((E'.kept x).erase y).card :=
            Finset.card_le_card hsubset
          _ = 1 := herase
  | X =>
      have hnotX : E.status x ≠ .X := (Finset.mem_filter.mp hPresent.2.1).2
      exact False.elim (hnotX hxStatus)

theorem main : AKLT.Blueprint.Rec.PairClosureStatementV2 := by
  classical
  intro p T n w htrail i
  dsimp [AKLT.Blueprint.Rec.PairClosureStatementV2]
  let E := prefixNetwork p.normalized p.u w i.val
  let y := wordVertex p.u w i.val
  let incoming := wordIncoming p.incoming w i
  change E.status y = .U →
    ∀ a ∈ nonarrivalNeighborsV2 E y incoming,
      ∀ b ∈ nonarrivalNeighborsV2 E y incoming, a ≠ b →
        (removeSite E y).ResponsePair (responsePairType {a, b}) a b y
  intro hyU a ha b hb hab
  have hCore : CoreInvariant E y (prefixArrival p.u p.c w i.val) := by
    simpa [E, y] using prefix_core p T w htrail i
  have hArrival : y - incoming.step = prefixArrival p.u p.c w i.val := by
    exact arrival_eq_prefix p w i
  have hyBond : p.normalized.Present y (wordVertex p.u w (i.val + 1)) :=
    htrail.2.1 i
  have hyG : y ∈ p.G := active_mem_G hyBond.1
  have hyS : y ∉ protectedSites p.G := (htrail.2.2.1 i.val i.isLt).2
  have hRemoved : (removeSite E y).Consistent :=
    removeSite_consistent_of_core E y (prefixArrival p.u p.c w i.val)
      hCore hyG hyS
  have hpa : E.Present y a :=
    present_from_nonarrival E y (prefixArrival p.u p.c w i.val) incoming a
      hCore hArrival hyU hyG ha
  have hpb : E.Present y b :=
    present_from_nonarrival E y (prefixArrival p.u p.c w i.val) incoming b
      hCore hArrival hyU hyG hb
  have hya : y ≠ a := ne_of_adjacent hpa.2.2.1
  have hyb : y ≠ b := ne_of_adjacent hpb.2.2.1
  have haNe : a ≠ y := fun h => hya h.symm
  have hbNe : b ≠ y := fun h => hyb h.symm
  have haActive : a ∈ (removeSite E y).active := by
    apply Finset.mem_filter.mpr
    refine ⟨active_mem_G hpa.2.1, ?_⟩
    have hs : (removeSite E y).status a = E.status a := by simp [removeSite, haNe]
    rw [hs]
    exact (Finset.mem_filter.mp hpa.2.1).2
  have hbActive : b ∈ (removeSite E y).active := by
    apply Finset.mem_filter.mpr
    refine ⟨active_mem_G hpb.2.1, ?_⟩
    have hs : (removeSite E y).status b = E.status b := by simp [removeSite, hbNe]
    rw [hs]
    exact (Finset.mem_filter.mp hpb.2.1).2
  have hGeom : HasPairType (responsePairType {a, b}) a b :=
    response_type_neighbors (mem_neighbors_of_adjacent hpa.2.2.1)
      (mem_neighbors_of_adjacent hpb.2.2.1) hab
  refine ⟨hRemoved, haActive, hbActive, hyG, ?_, ?_, ?_, hGeom, ?_, ?_⟩
  · simp [removeSite]
  · exact adjacent_symm hpa.2.2.1
  · exact adjacent_symm hpb.2.2.1
  · exact removed_endpoint_condition E y a hRemoved hpa haNe
  · exact removed_endpoint_condition E y b hRemoved hpb hbNe

end AKLT.W.REC097
