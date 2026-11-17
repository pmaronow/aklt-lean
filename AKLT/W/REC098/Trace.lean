module
public import AKLT.W.REC098.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec (normalizeStart prefixNetwork)

namespace AKLT.W.REC098

/-- Local data during a trace. The set `bad` contains fixed protected defects. -/
structure TraceState {G : Finset Plane} (D : Network G) (bad : Finset Plane)
    (y a : Plane) : Prop where
  outside : ∀ x, x ∉ G → D.status x = .X
  subset : ∀ x, D.kept x ⊆ neighbors x ∩ G
  mutualKept : ∀ x ∈ D.active, ∀ z ∈ D.active, Adjacent x z →
    (z ∈ D.kept x ↔ x ∈ D.kept z)
  fullU : ∀ x, x ≠ y → x ∉ bad → D.status x = .U → D.kept x = neighbors x ∩ G
  twoD : ∀ x, x ≠ y → D.status x = .D → (D.kept x).card = 2
  liveU : D.status y = .U → D.kept y = (neighbors y ∩ G).erase a
  liveD : D.status y = .D → (D.presentNeighbors y).card ≤ 1
  arrival : D.status a = .X ∨
    (D.status a = .D ∧ (D.kept a).card = 2 ∧ y ∉ D.kept a)
  arrival_adj : Adjacent y a
  protectedU : ∀ x ∈ protectedSites G, D.status x = .U

theorem present_symm {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : D.Present z x := by
  exact ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem present_neighbor {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : z ∈ D.presentNeighbors x := by
  exact Finset.mem_filter.mpr ⟨(adjacent_iff x z).mp h.2.2.1, h⟩

theorem traceStep_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  intro x hx
  simp only [Network.active, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  by_cases hxy : x = y
  · subst x
    simp only [traceStep, Function.update_self] at hx
    split_ifs at hx with h
    · simp [h]
    · exact False.elim (hx.2 rfl)
  · simpa [traceStep, Function.update_of_ne hxy] using hx.2

theorem traceStep_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  simp only [traceStep]
  split_ifs <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.refl _

theorem traceStep_present_subset {G : Finset Plane} (D : Network G) (y o : Plane)
    {x z : Plane} (h : (traceStep D y o).Present x z) : D.Present x z := by
  exact ⟨traceStep_active_subset D y o h.1, traceStep_active_subset D y o h.2.1,
    h.2.2.1, traceStep_kept_subset D y o x h.2.2.2.1,
    traceStep_kept_subset D y o z h.2.2.2.2⟩

theorem preserve_present {G : Finset Plane} {D : Network G} {y o x z : Plane}
    (hyo : D.Present y o)
    (hD : D.status y = .D → (D.presentNeighbors y).card ≤ 1)
    (hxz : D.Present x z) (hne : ({x, z} : Finset Plane) ≠ {y, o}) :
    (traceStep D y o).Present x z := by
  have uniq : D.status y = .D → ∀ t, D.Present y t → t = o := by
    intro hs t ht
    exact Finset.card_le_one.mp (hD hs) t (present_neighbor ht) o (present_neighbor hyo)
  have xa : x ∈ (traceStep D y o).active := by
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxz.1).1, ?_⟩
    by_cases hxy : x = y
    · subst x
      have hnotD : D.status y ≠ .D := by
        intro hs
        exact hne (by rw [uniq hs z hxz])
      have hsX := (Finset.mem_filter.mp hyo.1).2
      have hsU : D.status y = .U := by cases h : D.status y <;> simp_all
      simp [traceStep, hsU]
    · simpa [traceStep, hxy] using (Finset.mem_filter.mp hxz.1).2
  have za : z ∈ (traceStep D y o).active := by
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxz.2.1).1, ?_⟩
    by_cases hzy : z = y
    · subst z
      have hnotD : D.status y ≠ .D := by
        intro hs
        have hx := uniq hs x (present_symm hxz)
        exact hne (by simp [hx, Finset.pair_comm])
      have hsX := (Finset.mem_filter.mp hyo.1).2
      have hsU : D.status y = .U := by cases h : D.status y <;> simp_all
      simp [traceStep, hsU]
    · simpa [traceStep, hzy] using (Finset.mem_filter.mp hxz.2.1).2
  refine ⟨xa, za, hxz.2.2.1, ?_, ?_⟩
  · simp only [traceStep]
    split_ifs with hxy hxo
    · exact Finset.mem_erase.mpr ⟨by intro h; exact hne (by simp_all), hxz.2.2.2.1⟩
    · exact Finset.mem_erase.mpr ⟨by intro h; exact hne (by simp_all [Finset.pair_comm]), hxz.2.2.2.1⟩
    · exact hxz.2.2.2.1
  · simp only [traceStep]
    split_ifs with hzy hzo
    · exact Finset.mem_erase.mpr ⟨by intro h; exact hne (by simp_all [Finset.pair_comm]), hxz.2.2.2.2⟩
    · exact Finset.mem_erase.mpr ⟨by intro h; exact hne (by simp_all), hxz.2.2.2.2⟩
    · exact hxz.2.2.2.2

theorem presentNeighbors_card_le_kept {G : Finset Plane} (D : Network G) (x : Plane) :
    (D.presentNeighbors x).card ≤ (D.kept x).card := by
  apply Finset.card_le_card
  intro z hz
  exact (Finset.mem_filter.mp hz).2.2.2.2.1

theorem TraceState.step {G : Finset Plane} {D : Network G} {bad : Finset Plane}
    {y a o : Plane} (hs : TraceState D bad y a) (hyS : y ∉ protectedSites G)
    (hyo : D.Present y o) (hoB : o ∉ bad) :
    TraceState (traceStep D y o) bad o y := by
  have hyG := (Finset.mem_filter.mp hyo.1).1
  have hyX := (Finset.mem_filter.mp hyo.1).2
  have hyo_ne : y ≠ o := adjacent_ne hyo.2.2.1
  have hoy_ne := Ne.symm hyo_ne
  have hN : neighbors y ∩ G = neighbors y := interior_neighbors hyG hyS
  have haN : a ∈ neighbors y := (adjacent_iff y a).mp hs.arrival_adj
  have hoK : o ∈ D.kept y := hyo.2.2.2.1
  have hyK : y ∈ D.kept o := hyo.2.2.2.2
  have departed_two (hU : D.status y = .U) :
      ((traceStep D y o).kept y).card = 2 := by
    have hk := hs.liveU hU
    rw [hN] at hk
    have hoN : o ∈ (neighbors y).erase a := by simpa [hk] using hoK
    simp only [traceStep, ite_true]
    rw [hk, Finset.card_erase_of_mem hoN, Finset.card_erase_of_mem haN, neighbors_card]
  have stat_o : (traceStep D y o).status o = D.status o := by
    simp [traceStep, hoy_ne]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, adjacent_symm hyo.2.2.1, ?_⟩
  · intro x hx
    have hxy : x ≠ y := by intro h; subst x; exact hx hyG
    simpa [traceStep, hxy] using hs.outside x hx
  · intro x
    exact (traceStep_kept_subset D y o x).trans (hs.subset x)
  · intro x hx z hz hadj
    have hm := hs.mutualKept x (traceStep_active_subset D y o hx)
      z (traceStep_active_subset D y o hz) hadj
    by_cases hxy : x = y <;> by_cases hxo : x = o <;>
      by_cases hzy : z = y <;> by_cases hzo : z = o <;>
      simp_all [traceStep, Finset.mem_erase]
  · intro x hxo hxb hU
    have hxy : x ≠ y := by
      intro heq
      subst x
      simp only [traceStep, Function.update_self] at hU
      split_ifs at hU
    simpa [traceStep, hxy, hxo] using hs.fullU x hxy hxb (by simpa [traceStep, hxy] using hU)
  · intro x hxo hD
    by_cases hxy : x = y
    · subst x
      have hU : D.status y = .U := by
        simp only [traceStep, Function.update_self] at hD
        split_ifs at hD with h
        all_goals simp_all
      exact departed_two hU
    · simpa [traceStep, hxy, hxo] using hs.twoD x hxy (by simpa [traceStep, hxy] using hD)
  · intro hU
    have hk := hs.fullU o hoy_ne hoB (stat_o ▸ hU)
    simp [traceStep, hoy_ne, hk]
  · intro hD
    have hk := hs.twoD o hoy_ne (stat_o ▸ hD)
    have hc : ((traceStep D y o).kept o).card = 1 := by
      simp only [traceStep, hoy_ne, ite_false, ite_true]
      rw [Finset.card_erase_of_mem hyK, hk]
    exact (presentNeighbors_card_le_kept _ _).trans (by omega)
  · by_cases hU : D.status y = .U
    · right
      exact ⟨by simp [traceStep, hU], departed_two hU, by simp [traceStep]⟩
    · left
      simp [traceStep, hU]
  · intro x hx
    have hxy : x ≠ y := by intro h; subst x; exact hyS hx
    simpa [traceStep, hxy] using hs.protectedU x hx

theorem traceNetwork_append_step {G : Finset Plane} (D : Network G)
    (l : List Plane) (x z : Plane) :
    traceNetwork D (l ++ [x, z]) = traceStep (traceNetwork D (l ++ [x])) x z := by
  induction l generalizing D with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simpa [traceNetwork] using ih (traceStep D a b)

theorem prefixNetwork_eq_range {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    prefixNetwork D u w j = traceNetwork D ((List.range (j + 1)).map (wordVertex u w)) := by
  simp [prefixNetwork, wordVertices, ← List.map_take, List.take_range, Nat.min_eq_left (by omega : j + 1 ≤ n + 1)]

theorem prefixNetwork_zero {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) : prefixNetwork D u w 0 = D := by
  rw [prefixNetwork_eq_range D u w 0 (by omega)]
  rfl

theorem prefixNetwork_succ {G : Finset Plane} {n : ℕ} (D : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  rw [prefixNetwork_eq_range D u w (j + 1) (by omega), prefixNetwork_eq_range D u w j (by omega)]
  rw [List.range_succ, List.map_append]
  cases j with
  | zero => rfl
  | succ j =>
    rw [show List.range (j + 1 + 1) = List.range (j + 1) ++ [j + 1] from List.range_succ, List.map_append]
    simpa [List.append_assoc] using traceNetwork_append_step D
      ((List.range (j + 1)).map (wordVertex u w)) (wordVertex u w (j + 1))
      (wordVertex u w (j + 1 + 1))

theorem prefix_state {G : Finset Plane} {n : ℕ} {D : Network G} {bad : Finset Plane}
    {u a : Plane} {w : DirectionWord n} {T : Finset Plane}
    (hs : TraceState D bad u a) (hw : StoppedNetworkTrail D u T w)
    (j : ℕ) (hj : j ≤ n) (hb : ∀ k ≤ j, wordVertex u w k ∉ bad) :
    TraceState (prefixNetwork D u w j) bad (wordVertex u w j)
      (if j = 0 then a else wordVertex u w (j - 1)) ∧
    ∀ k : Fin n, j ≤ k.val → (prefixNetwork D u w j).Present
      (wordVertex u w k.val) (wordVertex u w (k.val + 1)) := by
  induction j with
  | zero =>
    constructor
    · simpa [prefixNetwork_zero, wordVertex_zero] using hs
    · intro k _; simpa [prefixNetwork_zero] using hw.2.1 k
  | succ j ih =>
    obtain ⟨hsj, hpj⟩ := ih (by omega) (fun k hk => hb k (by omega))
    have hjn : j < n := by omega
    have hstate := hsj.step (hw.2.2.1 j hjn).2 (hpj ⟨j, hjn⟩ (Nat.le_refl j)) (hb (j + 1) (by omega))
    constructor
    · simpa [prefixNetwork_succ D u w j hjn] using hstate
    · intro k hk
      rw [prefixNetwork_succ D u w j hjn]
      apply preserve_present (hpj ⟨j, hjn⟩ (Nat.le_refl j)) hsj.liveD (hpj k (by omega))
      intro heq
      have hi : k = ⟨j, hjn⟩ := hw.1 (show wordBond u w k = wordBond u w ⟨j, hjn⟩ from heq)
      have hv : k.val = j := congrArg Fin.val hi
      omega

theorem normalizeStart_of_not_U {G : Finset Plane} (D : Network G) (u c : Plane)
    (h : D.status u ≠ .U) : normalizeStart D u c = D := by
  cases D with
  | mk s k => simp_all [normalizeStart]

theorem normalizeStart_present_subset {G : Finset Plane} (D : Network G) (u c : Plane)
    {x z : Plane} (h : (normalizeStart D u c).Present x z) : D.Present x z := by
  have sub (t : Plane) : (normalizeStart D u c).kept t ⊆ D.kept t := by
    simp only [normalizeStart]
    split_ifs <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.refl _
  exact ⟨h.1, h.2.1, h.2.2.1, sub x h.2.2.2.1, sub z h.2.2.2.2⟩

theorem normalizeStart_mutual {G : Finset Plane} {D : Network G} {u c : Plane}
    (hc : D.status c = .X)
    (hm : ∀ x ∈ D.active, ∀ z ∈ D.active, Adjacent x z →
      (z ∈ D.kept x ↔ x ∈ D.kept z)) :
    ∀ x ∈ (normalizeStart D u c).active, ∀ z ∈ (normalizeStart D u c).active,
      Adjacent x z →
      (z ∈ (normalizeStart D u c).kept x ↔ x ∈ (normalizeStart D u c).kept z) := by
  intro x hx z hz hadj
  have hxc : x ≠ c := by intro h; subst x; exact (Finset.mem_filter.mp hx).2 hc
  have hzc : z ≠ c := by intro h; subst z; exact (Finset.mem_filter.mp hz).2 hc
  have hh := hm x hx z hz hadj
  simp only [normalizeStart]
  split_ifs <;> simp_all

theorem initial_state (p : AKLT.Blueprint.Rec.PairSetup) :
    TraceState p.normalized ∅ p.u p.c := by
  have hcons := p.pair.1
  have hc := p.pair.2.2.2.2.1
  have huc := p.pair.2.2.2.2.2.1
  have hupair := p.pair.2.2.2.2.2.2.2.2.1
  change TraceState (normalizeStart p.D p.u p.c) ∅ p.u p.c
  refine ⟨hcons.1.1.1, ?_, normalizeStart_mutual hc hcons.2.2.2, ?_, ?_, ?_, ?_,
    Or.inl hc, huc, fun x hx => (hcons.1.2 x hx).1⟩
  · intro x
    simp only [normalizeStart]
    split_ifs
    · exact (Finset.erase_subset _ _).trans (hcons.1.1.2.1 x)
    · exact hcons.1.1.2.1 x
  · intro x hxu _ hU
    change p.D.status x = .U at hU
    have hxG : x ∈ p.G := by
      by_contra hx
      have := hcons.1.1.1 x hx
      simp_all
    simpa [normalizeStart, hxu] using hcons.2.1 x hxG hU
  · intro x hxu hD
    change p.D.status x = .D at hD
    have hxG : x ∈ p.G := by
      by_contra hx
      have := hcons.1.1.1 x hx
      simp_all
    simpa [normalizeStart, hxu] using hcons.2.2.1 x hxG hD
  · intro hU
    change p.D.status p.u = .U at hU
    have huG := (Finset.mem_filter.mp p.pair.2.1).1
    simp [normalizeStart, hU, hcons.2.1 p.u huG hU]
  · intro hD
    change p.D.status p.u = .D at hD
    have hd : (p.D.presentNeighbors p.u).card ≤ 1 := by
      rcases hupair with hU | ⟨_, hd⟩
      · simp_all
      · exact hd
    have hn := normalizeStart_of_not_U p.D p.u p.c (by simp [hD])
    simpa [hn] using hd

theorem traceNetwork_present_subset {G : Finset Plane} (D : Network G) (l : List Plane)
    {x z : Plane} (h : (traceNetwork D l).Present x z) : D.Present x z := by
  induction l generalizing D with
  | nil => exact h
  | cons a l ih =>
    cases l with
    | nil => exact h
    | cons b l => exact traceStep_present_subset D a b (ih (traceStep D a b) h)

theorem traceNetwork_status_X {G : Finset Plane} (D : Network G) (l : List Plane)
    {x : Plane} (h : D.status x = .X) : (traceNetwork D l).status x = .X := by
  induction l generalizing D with
  | nil => exact h
  | cons a l ih =>
    cases l with
    | nil => exact h
    | cons b l =>
      apply ih
      by_cases hxa : x = a
      · subst x; simp [traceStep, h]
      · simpa [traceStep, hxa] using h

theorem prefix_status_unvisited {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) (x : Plane)
    (hx : ∀ k < j, wordVertex u w k ≠ x) :
    (prefixNetwork D u w j).status x = D.status x := by
  induction j with
  | zero => rw [prefixNetwork_zero]
  | succ j ih =>
    rw [prefixNetwork_succ D u w j (by omega)]
    have hn : x ≠ wordVertex u w j := Ne.symm (hx j (by omega))
    simpa [traceStep, hn] using ih (by omega) (fun k hk => hx k (by omega))

theorem TraceState.restart {G : Finset Plane} {D : Network G} {e a v c : Plane}
    (hs : TraceState D ∅ e a) (he : e ∈ protectedSites G) (hve : v ≠ e)
    (hc : D.status c = .X) (hvc : Adjacent v c)
    (hdeg : D.status v = .D → (D.presentNeighbors v).card ≤ 1) :
    TraceState (normalizeStart D v c) {e} v c := by
  refine ⟨hs.outside, ?_, normalizeStart_mutual hc hs.mutualKept, ?_, ?_, ?_, ?_,
    Or.inl hc, hvc, hs.protectedU⟩
  · intro x
    simp only [normalizeStart]
    split_ifs
    · exact (Finset.erase_subset _ _).trans (hs.subset x)
    · exact hs.subset x
  · intro x hxv hxe hU
    have hxe' : x ≠ e := by simpa using hxe
    simpa [normalizeStart, hxv] using hs.fullU x hxe' (by simp) hU
  · intro x hxv hD
    change D.status x = .D at hD
    have hxe : x ≠ e := by
      intro h; subst x; have := hs.protectedU e he; simp_all
    simpa [normalizeStart, hxv] using hs.twoD x hxe hD
  · intro hU
    change D.status v = .U at hU
    have hk := hs.fullU v hve (by simp) hU
    simp [normalizeStart, hU, hk]
  · intro hD
    change D.status v = .D at hD
    have hn := normalizeStart_of_not_U D v c (by simp [hD])
    simpa [hn] using hdeg hD

theorem word_arrival {n : ℕ} {u c : Plane} {incoming : Compass}
    (hu : u = c + incoming.step) (w : DirectionWord n) (i : Fin n) :
    (if i.val = 0 then c else wordVertex u w (i.val - 1)) =
      wordVertex u w i.val - (wordIncoming incoming w i).step := by
  by_cases hi : i.val = 0
  · simp [wordIncoming, hi, wordVertex_zero, hu]
  · have hj : i.val - 1 < n := by omega
    have hv := wordVertex_succ u w (i.val - 1) hj
    have he : i.val - 1 + 1 = i.val := by omega
    rw [he] at hv
    simp [hi, wordIncoming, hv]

theorem second_state (p : AKLT.Blueprint.Rec.PairSetup) (hpv : p.v ∉ protectedSites p.G)
    (n : ℕ) (w : DirectionWord n)
    (hfirst : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G)
    (incoming : Compass) (hin : p.v = p.c + incoming.step)
    (m : ℕ) (w' : DirectionWord m)
    (hsecond : StoppedNetworkTrail
      (normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
      p.v (protectedSites p.G) w') (i : Fin m) :
    TraceState
      (prefixNetwork (normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
        p.v w' i.val) {wordVertex p.u w n}
      (wordVertex p.v w' i.val)
      (wordVertex p.v w' i.val - (wordIncoming incoming w' i).step) ∧
    (prefixNetwork (normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
      p.v w' i.val).Present (wordVertex p.v w' i.val) (wordVertex p.v w' (i.val + 1)) := by
  let F := traceNetwork p.normalized (wordVertices p.u w)
  let e := wordVertex p.u w n
  have hprefix : prefixNetwork p.normalized p.u w n = F := by
    rw [prefixNetwork_eq_range p.normalized p.u w n (by omega)]
    rfl
  have ht := (prefix_state (initial_state p) hfirst n (by omega) (by simp)).1
  rw [hprefix] at ht
  have hve : p.v ≠ e := by intro h; exact hpv (h ▸ he)
  have hc : F.status p.c = .X := traceNetwork_status_X _ _ p.pair.2.2.2.2.1
  have hvstat : F.status p.v = p.D.status p.v := by
    rw [← hprefix]
    apply prefix_status_unvisited
    · omega
    · intro k hk hkv
      have ha := (hfirst.2.2.1 k hk).1
      exact ha (by simp [hkv])
  have hdeg : F.status p.v = .D → (F.presentNeighbors p.v).card ≤ 1 := by
    intro hvD
    have hd : (p.D.presentNeighbors p.v).card ≤ 1 := by
      rcases p.pair.2.2.2.2.2.2.2.2.2 with hU | ⟨_, hd⟩
      · simp_all
      · exact hd
    apply le_trans (Finset.card_le_card ?_) hd
    intro z hz
    have hpres := (Finset.mem_filter.mp hz).2
    have horig := normalizeStart_present_subset p.D p.u p.c
      (traceNetwork_present_subset p.normalized (wordVertices p.u w) hpres)
    exact present_neighbor horig
  have hi0 := ht.restart he hve hc p.pair.2.2.2.2.2.2.1 hdeg
  have hb : ∀ k ≤ i.val, wordVertex p.v w' k ∉ ({e} : Finset Plane) := by
    intro k hk
    simp only [Finset.mem_singleton]
    intro hke
    have ha := (hsecond.2.2.1 k (by omega)).2
    exact ha (hke ▸ he)
  have hi := prefix_state hi0 hsecond i.val (by omega) hb
  constructor
  · rw [word_arrival hin w' i] at hi
    exact hi.1
  · exact hi.2 i (Nat.le_refl i.val)

end AKLT.W.REC098
