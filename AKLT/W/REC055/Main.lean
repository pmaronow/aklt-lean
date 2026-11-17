module
public import AKLT.Blueprint.Rec.NodesClosure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC055

private theorem adjacent_mem_neighbors {x y : Plane} (h : Adjacent x y) : y ∈ neighbours x := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  have hsum : (x₁ - y₁).natAbs + (x₂ - y₂).natAbs = 1 := h
  have hcases : ((x₁ - y₁).natAbs = 1 ∧ (x₂ - y₂).natAbs = 0) ∨
      ((x₁ - y₁).natAbs = 0 ∧ (x₂ - y₂).natAbs = 1) := by omega
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hx' : x₁ - y₁ = 1 ∨ x₁ - y₁ = -1 := Int.natAbs_eq_iff.mp hx
    have hy' : x₂ - y₂ = 0 := by
      have := Int.natAbs_eq_zero.mp hy
      exact this
    rcases hx' with hx' | hx'
    · refine ⟨Compass.west, ?_⟩
      simp [Compass.step, Prod.ext_iff]
      omega
    · refine ⟨Compass.east, ?_⟩
      simp [Compass.step, Prod.ext_iff]
      omega
  · have hx' : x₁ - y₁ = 0 := Int.natAbs_eq_zero.mp hx
    have hy' : x₂ - y₂ = 1 ∨ x₂ - y₂ = -1 := Int.natAbs_eq_iff.mp hy
    rcases hy' with hy' | hy'
    · refine ⟨Compass.south, ?_⟩
      simp [Compass.step, Prod.ext_iff]
      omega
    · refine ⟨Compass.north, ?_⟩
      simp [Compass.step, Prod.ext_iff]
      omega

private theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  have hinj : Function.Injective (fun d : Compass => x + d.step) := by
    intro a b hab
    have hstep : a.step = b.step := add_left_cancel hab
    cases a <;> cases b <;> simp_all [Compass.step]
  rw [neighbours, Finset.card_image_of_injective Finset.univ hinj]
  simpa using (show Fintype.card Compass = 4 by decide)

private theorem adjacent_ne {x y : Plane} (h : Adjacent x y) : x ≠ y := by
  intro heq
  subst y
  have hz := h
  simp [Adjacent, latticeDist] at hz

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have h₁ : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by
    rw [show y.1 - x.1 = -(x.1 - y.1) by omega, Int.natAbs_neg]
  have h₂ : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by
    rw [show y.2 - x.2 = -(x.2 - y.2) by omega, Int.natAbs_neg]
  simpa [Adjacent, latticeDist, h₁, h₂, Nat.add_comm] using h

private theorem step_active_subset {G : Finset Plane} (D : Network G) (y o : Plane) :
    (traceStep D y o).active ⊆ D.active := by
  intro x hx
  simp only [Network.active, Finset.mem_filter] at hx ⊢
  rcases hx with ⟨hxG, hne⟩
  refine ⟨hxG, ?_⟩
  by_cases hxy : x = y
  · subst x
    simp only [traceStep, Function.update_apply] at hne
    by_cases hU : D.status y = .U <;> simp [hU] at hne ⊢
  · simpa [traceStep, hxy] using hne

private theorem step_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  by_cases hxy : x = y
  · subst x
    simpa [traceStep] using (Finset.erase_subset o (D.kept y))
  · by_cases hxo : x = o
    · subst x
      simpa [traceStep, hxy] using (Finset.erase_subset y (D.kept o))
    · simp [traceStep, hxy, hxo]

private theorem step_present_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x := by
  intro z hz
  simp only [Network.presentNeighbours, Finset.mem_filter] at hz ⊢
  rcases hz with ⟨hzN, hpres⟩
  rcases hpres with ⟨hxa, hza, hadj, hzx, hxz⟩
  refine ⟨hzN, ?_⟩
  exact ⟨step_active_subset D y o hxa, step_active_subset D y o hza, hadj,
    step_kept_subset D y o x hzx, step_kept_subset D y o z hxz⟩

private theorem step_remove_left_of_ne {G : Finset Plane} (D : Network G) {y o : Plane}
    (hne : y ≠ o) : o ∉ (traceStep D y o).presentNeighbours y := by
  intro ho
  have hp := (Finset.mem_filter.mp ho).2
  have hmem : o ∈ (D.kept y).erase o := by simpa [traceStep, hne] using hp.2.2.2.1
  exact (Finset.mem_erase.mp hmem).1 rfl

private theorem step_remove_right_of_ne {G : Finset Plane} (D : Network G) {y o : Plane}
    (hne : y ≠ o) : y ∉ (traceStep D y o).presentNeighbours o := by
  intro hy
  have hp := (Finset.mem_filter.mp hy).2
  have hmem : y ∈ (D.kept o).erase y := by simpa [traceStep, hne.symm] using hp.2.2.2.2
  exact (Finset.mem_erase.mp hmem).1 rfl

private theorem step_pn_subset_erase_left_of_ne {G : Finset Plane} (D : Network G)
    {y o : Plane} (hne : y ≠ o) :
    (traceStep D y o).presentNeighbours y ⊆ (D.presentNeighbours y).erase o := by
  intro z hz
  have hz0 := step_present_subset D y o y hz
  have hzne : z ≠ o := by
    intro heq
    subst z
    exact step_remove_left_of_ne D hne hz
  exact Finset.mem_erase.mpr ⟨hzne, hz0⟩

private theorem step_pn_subset_erase_right_of_ne {G : Finset Plane} (D : Network G)
    {y o : Plane} (hne : y ≠ o) :
    (traceStep D y o).presentNeighbours o ⊆ (D.presentNeighbours o).erase y := by
  intro z hz
  have hz0 := step_present_subset D y o o hz
  have hzne : z ≠ y := by
    intro heq
    subst z
    exact step_remove_right_of_ne D hne hz
  exact Finset.mem_erase.mpr ⟨hzne, hz0⟩

private theorem step_localRules {G : Finset Plane} (D : Network G) {y o : Plane}
    (hlocal : D.LocalRules)
    (hsafe : D.status y = .U → (D.presentNeighbours y).card ≤ 3 ∧
      (o ∉ D.presentNeighbours y → (D.presentNeighbours y).card ≤ 2))
    (hne : y ≠ o) :
    (traceStep D y o).LocalRules := by
  rcases hlocal with ⟨houtside, hkept, hD, hfactor⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxy : x = y
    · subst x
      have hY : D.status y = .X := houtside y hx
      simp [traceStep, hY]
    · simpa [traceStep, hxy] using houtside x hx
  · intro x
    exact (step_kept_subset D y o x).trans (hkept x)
  · intro x hxG hxD
    by_cases hxy : x = y
    · subst x
      by_cases hU : D.status y = .U
      · have hstatus : (traceStep D y o).status y = .D := by simp [traceStep, hU]
        rw [hstatus] at hxD
        by_cases hout : o ∈ D.presentNeighbours y
        · have hcard : ((traceStep D y o).presentNeighbours y).card ≤
              (D.presentNeighbours y).card - 1 := by
            calc
              _ ≤ ((D.presentNeighbours y).erase o).card :=
                Finset.card_le_card (step_pn_subset_erase_left_of_ne D hne)
              _ = (D.presentNeighbours y).card - 1 := Finset.card_erase_of_mem hout
          have hsafe1 := hsafe hU |>.1
          omega
        · have hcard := Finset.card_le_card (step_present_subset D y o y)
          have hsafe2 := hsafe hU |>.2 hout
          omega
      · have hstatus : (traceStep D y o).status y = .X := by simp [traceStep, hU]
        rw [hstatus] at hxD
        cases hxD
    · have hdeq : D.status x = .D := by simpa [traceStep, hxy] using hxD
      have hcard := Finset.card_le_card (step_present_subset D y o x)
      exact (hcard.trans (hD x hxG hdeq))
  · intro x hx
    have hactive : x ∈ D.active := step_active_subset D y o hx
    have hcard := Finset.card_le_card (step_present_subset D y o x)
    have hfactor0 := hfactor x hactive
    omega

private theorem step_auxiliary {G : Finset Plane} (D : Network G) {y o : Plane}
    (haux : D.Auxiliary)
    (hsafe : D.status y = .U → (D.presentNeighbours y).card ≤ 3 ∧
      (o ∉ D.presentNeighbours y → (D.presentNeighbours y).card ≤ 2))
    (hne : y ≠ o) (hnot : y ∉ protectedSites G) : (traceStep D y o).Auxiliary := by
  rcases haux with ⟨hloc, hprot⟩
  refine ⟨step_localRules D hloc hsafe hne, ?_⟩
  intro x hx
  have hxy : x ≠ y := by
    intro heq
    subst x
    exact hnot hx
  simpa [traceStep, hxy] using hprot x hx

private theorem traceNetwork_append_pair {G : Finset Plane} (D : Network G)
    (l : List Plane) (a b : Plane) :
    traceNetwork D (l ++ [a, b]) = traceStep (traceNetwork D (l ++ [a])) a b := by
  induction l generalizing D with
  | nil => simp [traceNetwork]
  | cons x xs ih =>
    cases xs with
    | nil => simp [traceNetwork]
    | cons y ys =>
      simpa [traceNetwork] using ih (traceStep D x y)

private theorem prefix_step {G : Finset Plane} (D : Network G) (u : Plane)
    {n : ℕ} (w : DirectionWord n) {j : ℕ} (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  let L := wordVertices u w
  have hlen : (j + 1) < L.length := by
    simp [L, wordVertices]
    omega
  have hlen0 : j < L.length := by omega
  have hget : ∀ i (hi : i < L.length), L[i]'hi = wordVertex u w i := by
    intro i hi
    have hmap : i < (List.map (wordVertex u w) (List.range (n + 1))).length := by
      simpa [L, wordVertices] using hi
    have hidx : i < n + 1 := by simpa using hmap
    have hrange : i < (List.range (n + 1)).length := by simpa using hidx
    change (List.map (wordVertex u w) (List.range (n + 1)))[i]'hmap = wordVertex u w i
    rw [List.getElem_map (f := wordVertex u w) (l := List.range (n + 1)) (h := hmap)]
    rw [List.getElem_range hrange]
  have htake1 : L.take (j + 1) = L.take j ++ [wordVertex u w j] := by
    rw [List.take_succ_eq_append_getElem hlen0]
    simp [hget j hlen0]
  have htake2 : L.take (j + 2) = L.take j ++ [wordVertex u w j, wordVertex u w (j + 1)] := by
    rw [show j + 2 = (j + 1) + 1 by omega,
      List.take_succ_eq_append_getElem hlen]
    rw [htake1]
    simp [hget (j + 1) hlen]
  change traceNetwork D (L.take (j + 2)) = _
  rw [htake2, traceNetwork_append_pair]
  rw [← htake1]
  rfl

private theorem prefix_zero {G : Finset Plane} (D : Network G) (u : Plane)
    {n : ℕ} (w : DirectionWord n) : prefixNetwork D u w 0 = D := by
  simp [prefixNetwork, wordVertices, List.take_add_one, traceNetwork]

private theorem prefix_final {G : Finset Plane} (D : Network G) (u : Plane)
    {n : ℕ} (w : DirectionWord n) :
    prefixNetwork D u w n = traceNetwork D (wordVertices u w) := by
  unfold prefixNetwork
  have hlen : (wordVertices u w).length ≤ n + 1 := by simp [wordVertices]
  rw [List.take_of_length_le hlen]

private theorem normalize_kept_mem_of_active {G : Finset Plane} (D : Network G)
    {u c x z : Plane} (hc : D.status c = .X) (hx : x ∈ D.active) (hz : z ∈ D.active) :
    z ∈ (normalizeStart D u c).kept x ↔ z ∈ D.kept x := by
  have hzc : z ≠ c := by
    intro h
    subst z
    exact (Finset.mem_filter.mp hz).2 hc
  by_cases hxu : x = u
  · subst x
    by_cases hU : D.status u = .U
    · simp [normalizeStart, hU, hzc]
    · simp [normalizeStart, hU]
  · simp [normalizeStart, hxu]

private theorem normalize_present_iff {G : Finset Plane} (D : Network G)
    {u c x z : Plane} (hc : D.status c = .X) :
    (normalizeStart D u c).Present x z ↔ D.Present x z := by
  have hactive : (normalizeStart D u c).active = D.active := by
    rfl
  constructor
  · intro h
    refine ⟨by simpa [hactive] using h.1, by simpa [hactive] using h.2.1,
      h.2.2.1, ?_, ?_⟩
    · exact (normalize_kept_mem_of_active D hc (by simpa [hactive] using h.1)
        (by simpa [hactive] using h.2.1)).mp h.2.2.2.1
    · exact (normalize_kept_mem_of_active D hc (by simpa [hactive] using h.2.1)
        (by simpa [hactive] using h.1)).mp h.2.2.2.2
  · intro h
    refine ⟨by simpa [hactive] using h.1, by simpa [hactive] using h.2.1,
      h.2.2.1, ?_, ?_⟩
    · exact (normalize_kept_mem_of_active D hc h.1 h.2.1).mpr h.2.2.2.1
    · exact (normalize_kept_mem_of_active D hc h.2.1 h.1).mpr h.2.2.2.2

private theorem normalize_presentNeighbours_eq {G : Finset Plane} (D : Network G)
    {u c : Plane} (hc : D.status c = .X) (x : Plane) :
    (normalizeStart D u c).presentNeighbours x = D.presentNeighbours x := by
  ext z
  simp only [Network.presentNeighbours, Finset.mem_filter]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, (normalize_present_iff D hc).mp h⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, (normalize_present_iff D hc).mpr h⟩

private theorem normalize_localRules {G : Finset Plane} (D : Network G)
    (hlocal : D.LocalRules) {u c : Plane} (hc : D.status c = .X) :
    (normalizeStart D u c).LocalRules := by
  rcases hlocal with ⟨houtside, hkept, hD, hfactor⟩
  have hactive : (normalizeStart D u c).active = D.active := by
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simpa [normalizeStart] using houtside x hx
  · intro x
    by_cases hxu : x = u
    · subst x
      by_cases hU : D.status u = .U
      · simpa [normalizeStart, hU] using (Finset.erase_subset c (D.kept u)).trans (hkept u)
      · simpa [normalizeStart, hU] using hkept u
    · simpa [normalizeStart, hxu] using hkept x
  · intro x hxG hxD
    have hD' : D.status x = .D := by simpa [normalizeStart] using hxD
    simpa [normalize_presentNeighbours_eq D hc x] using hD x hxG hD'
  · intro x hx
    have hx' : x ∈ D.active := by simpa [hactive] using hx
    simpa [normalize_presentNeighbours_eq D hc x] using hfactor x hx'

private theorem normalize_auxiliary {G : Finset Plane} (D : Network G)
    (haux : D.Auxiliary) {u c : Plane} (hc : D.status c = .X) :
    (normalizeStart D u c).Auxiliary := by
  rcases haux with ⟨hloc, hprotected⟩
  refine ⟨normalize_localRules D hloc hc, ?_⟩
  intro x hx
  simpa [normalizeStart] using hprotected x hx

private theorem present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  exact ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

private theorem pn_subset_neighbours_erase {G : Finset Plane} (D : Network G)
    {x c : Plane} (hcInactive : c ∉ D.active) :
    D.presentNeighbours x ⊆ (neighbours x).erase c := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzN, hpres⟩
  have hzc : z ≠ c := by
    intro heq
    subst z
    exact hcInactive hpres.2.1
  exact Finset.mem_erase.mpr ⟨hzc, hzN⟩

private theorem normalized_auxiliary (p : PairData) : p.normalized.Auxiliary := by
  rcases p.pair with ⟨hcons, huactive, hvactive, hcG, hcX, huc, hvc, htype, huCase, hvCase⟩
  have haux : p.D.Auxiliary := by
    refine ⟨hcons.1.1, ?_⟩
    intro x hx
    exact (hcons.1.2 x hx).1
  exact normalize_auxiliary p.D haux hcX

private theorem prefix_pn_subset_initial (p : PairData) {n : ℕ} (w : DirectionWord n) :
    ∀ j ≤ n, ∀ x, (prefixNetwork p.normalized p.u w j).presentNeighbours x ⊆
      p.normalized.presentNeighbours x := by
  intro j hj
  induction j with
  | zero =>
      intro x
      simpa [prefix_zero] using (Finset.Subset.rfl : p.normalized.presentNeighbours x ⊆ _)
  | succ j ih =>
      intro x
      have hjlt : j < n := by omega
      have hprev := ih (by omega) x
      rw [prefix_step p.normalized p.u w hjlt]
      exact (step_present_subset _ _ _ _).trans hprev

private theorem prefix_arrival_absent (p : PairData) {n : ℕ} (w : DirectionWord n)
    (hstop : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    {j : ℕ} (hj0 : 0 < j) (hj : j ≤ n) :
    wordVertex p.u w (j - 1) ∉
      (prefixNetwork p.normalized p.u w j).presentNeighbours (wordVertex p.u w j) := by
  have hklt : j - 1 < n := by omega
  let k : Fin n := ⟨j - 1, hklt⟩
  have hstep := hstop.2.1 k
  have hAdj : Adjacent (wordVertex p.u w (j - 1)) (wordVertex p.u w j) := by
    simpa [k, Nat.sub_add_cancel (by omega : 1 ≤ j)] using hstep.2.2.1
  have hne : wordVertex p.u w (j - 1) ≠ wordVertex p.u w j := adjacent_ne hAdj
  have hrec := prefix_step p.normalized p.u w hklt
  have hrec' : prefixNetwork p.normalized p.u w j =
      traceStep (prefixNetwork p.normalized p.u w (j - 1))
        (wordVertex p.u w (j - 1)) (wordVertex p.u w j) := by
    simpa [k, Nat.sub_add_cancel (by omega : 1 ≤ j)] using hrec
  rw [hrec']
  exact step_remove_right_of_ne _ hne

private theorem trail_neighbor_sites_distinct (p : PairData) {n : ℕ}
    (w : DirectionWord n) (htrail : Function.Injective (wordBond p.u w))
    {j : ℕ} (hj0 : 0 < j) (hj : j < n) :
    wordVertex p.u w (j - 1) ≠ wordVertex p.u w (j + 1) := by
  intro hsame
  let i : Fin n := ⟨j - 1, by omega⟩
  let k : Fin n := ⟨j, hj⟩
  have heq : wordBond p.u w i = wordBond p.u w k := by
    ext z
    simp [wordBond, i, k, hsame, Nat.sub_add_cancel (by omega : 1 ≤ j)] <;> tauto
  have hik := htrail heq
  have hval := congrArg Fin.val hik
  dsimp [i, k] at hval
  omega

private theorem prefix_source_safe (p : PairData) {n : ℕ} (w : DirectionWord n)
    (hstop : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    {j : ℕ} (hj : j < n) :
    (prefixNetwork p.normalized p.u w j).status (wordVertex p.u w j) = .U →
    ((prefixNetwork p.normalized p.u w j).presentNeighbours (wordVertex p.u w j)).card ≤ 3 ∧
      (wordVertex p.u w (j + 1) ∉
        (prefixNetwork p.normalized p.u w j).presentNeighbours (wordVertex p.u w j) →
        ((prefixNetwork p.normalized p.u w j).presentNeighbours (wordVertex p.u w j)).card ≤ 2) := by
  intro hU
  rcases p.pair with ⟨_, _, _, _, hcX, huc, _, _, _, _⟩
  let E := prefixNetwork p.normalized p.u w j
  let y := wordVertex p.u w j
  let o := wordVertex p.u w (j + 1)
  by_cases hj0 : j = 0
  · subst j
    have hcenter : p.c ∈ neighbours p.u := adjacent_mem_neighbors huc
    have hcinactive : p.c ∉ p.normalized.active := by
      change p.c ∉ p.normalized.active
      simp only [Network.active, Finset.mem_filter]
      intro h
      exact h.2 (by simpa [PairData.normalized, normalizeStart] using hcX)
    have hsub := pn_subset_neighbours_erase (x := p.u) p.normalized hcinactive
    have hcard : (p.normalized.presentNeighbours p.u).card ≤ 3 := by
      calc
        _ ≤ ((neighbours p.u).erase p.c).card := Finset.card_le_card hsub
        _ = (neighbours p.u).card - 1 := Finset.card_erase_of_mem hcenter
        _ = 3 := by rw [neighbours_card]
    have hout : o ∈ p.normalized.presentNeighbours p.u := by
      have he := hstop.2.1 ⟨0, hj⟩
      have he' : p.normalized.Present p.u o := by simpa [o, wordVertex] using he
      exact Finset.mem_filter.mpr ⟨adjacent_mem_neighbors he'.2.2.1, he'⟩
    have hy : wordVertex p.u w 0 = p.u := by simp [wordVertex]
    constructor
    · simpa [E, prefix_zero, y, hy] using hcard
    · intro hnot
      exact (hnot (by simpa [E, prefix_zero, y, o, hy] using hout)).elim
  · have hj0' : 0 < j := Nat.pos_of_ne_zero hj0
    have hprevAbsent := prefix_arrival_absent p w hstop hj0' (by omega)
    let prev := wordVertex p.u w (j - 1)
    have hprevOrig : prev ∈ p.normalized.presentNeighbours y := by
      let k : Fin n := ⟨j - 1, by omega⟩
      have hEdge := hstop.2.1 k
      have hRev := present_symm p.normalized hEdge
      have hRev' : p.normalized.Present y prev := by
        simpa [y, prev, k, Nat.sub_add_cancel (by omega : 1 ≤ j)] using hRev
      have hAdj : Adjacent y prev := by
        exact hRev'.2.2.1
      exact Finset.mem_filter.mpr ⟨adjacent_mem_neighbors hAdj, hRev'⟩
    have hnextOrig : o ∈ p.normalized.presentNeighbours y := by
      have hEdge := hstop.2.1 ⟨j, hj⟩
      exact Finset.mem_filter.mpr ⟨adjacent_mem_neighbors hEdge.2.2.1, hEdge⟩
    have hdistinct := trail_neighbor_sites_distinct p w hstop.1 hj0' hj
    have hsubset := prefix_pn_subset_initial p w j (by omega) y
    have hcard0 : (p.normalized.presentNeighbours y).card ≤ 4 := by
      calc
        _ ≤ (neighbours y).card := Finset.card_le_card (by
          intro z hz
          exact (Finset.mem_filter.mp hz).1)
        _ = 4 := neighbours_card y
    have hsub1 : E.presentNeighbours y ⊆ (p.normalized.presentNeighbours y).erase prev := by
      intro z hz
      have hz0 := hsubset hz
      exact Finset.mem_erase.mpr ⟨by
        intro heq
        subst z
        exact hprevAbsent hz, hz0⟩
    have hcard1 : (E.presentNeighbours y).card ≤ 3 := by
      calc
        _ ≤ ((p.normalized.presentNeighbours y).erase prev).card := Finset.card_le_card hsub1
        _ = (p.normalized.presentNeighbours y).card - 1 := Finset.card_erase_of_mem hprevOrig
        _ ≤ 3 := by omega
    constructor
    · exact hcard1
    · intro hnextAbsent
      have hsub2 : E.presentNeighbours y ⊆
          ((p.normalized.presentNeighbours y).erase prev).erase o := by
        intro z hz
        have hz1 := Finset.mem_erase.mp (hsub1 hz)
        have hz0 := hsubset hz
        exact Finset.mem_erase.mpr ⟨by
          intro heq
          subst z
          exact hnextAbsent hz, Finset.mem_erase.mpr hz1⟩
      have hcard2 : (E.presentNeighbours y).card ≤ 2 := by
        calc
          _ ≤ (((p.normalized.presentNeighbours y).erase prev).erase o).card := Finset.card_le_card hsub2
          _ = (p.normalized.presentNeighbours y).card - 2 := by
            rw [Finset.card_erase_of_mem]
            · rw [Finset.card_erase_of_mem hprevOrig]
              omega
            · exact Finset.mem_erase.mpr ⟨hdistinct.symm, hnextOrig⟩
          _ ≤ 2 := by omega
      exact hcard2

private theorem prefix_auxiliary (p : PairData) {n : ℕ} (w : DirectionWord n)
    (hstop : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w) :
    ∀ j ≤ n, (prefixNetwork p.normalized p.u w j).Auxiliary := by
  intro j hj
  induction j with
  | zero =>
      simpa [prefix_zero] using normalized_auxiliary p
  | succ j ih =>
      have hjlt : j < n := by omega
      have hprevAux := ih (by omega)
      have hsafe := prefix_source_safe p w hstop hjlt
      have hstep := hstop.2.1 ⟨j, hjlt⟩
      have hne : wordVertex p.u w j ≠ wordVertex p.u w (j + 1) :=
        adjacent_ne hstep.2.2.1
      have hnot : wordVertex p.u w j ∉ protectedSites p.G :=
        (hstop.2.2.1 j hjlt).2
      rw [prefix_step p.normalized p.u w hjlt]
      exact step_auxiliary _ hprevAux hsafe hne hnot

private theorem prefix_status_eq (p : PairData) {n : ℕ} (w : DirectionWord n)
    {x : Plane} (havoid : ∀ j < n, wordVertex p.u w j ≠ x) :
    ∀ j ≤ n, (prefixNetwork p.normalized p.u w j).status x = p.normalized.status x := by
  intro j hj
  induction j with
  | zero => simp [prefix_zero]
  | succ j ih =>
      have hjlt : j < n := by omega
      have hprev := ih (by omega)
      have hne : x ≠ wordVertex p.u w j := (havoid j hjlt).symm
      rw [prefix_step p.normalized p.u w hjlt]
      simpa [traceStep, hne] using hprev

private def legSlots (G : Finset Plane) (x : Plane) : Finset Plane :=
  ((originalLegs G).filter fun e => e.1 = x).image Prod.snd

private theorem originalLeg_endpoint {G : Finset Plane} {x z : Plane}
    (h : (x, z) ∈ originalLegs G) : z ∈ neighbours x ∧ z ∉ G := by
  rcases Finset.mem_biUnion.mp h with ⟨a, ha, h⟩
  rcases Finset.mem_image.mp h with ⟨b, hb, hab⟩
  have hab' : a = x ∧ b = z := Prod.mk.inj hab
  rcases Finset.mem_sdiff.mp hb with ⟨hbN, hbG⟩
  exact ⟨by simpa [hab'.1, hab'.2] using hbN,
    by simpa [hab'.2] using hbG⟩

private theorem factor_count_le_three_of_missing {G : Finset Plane} (D : Network G)
    {x z : Plane} (hzN : z ∈ neighbours x) (hzG : z ∈ G)
    (hzAbsent : z ∉ D.presentNeighbours x) :
    (D.presentNeighbours x).card + ((originalLegs G).filter fun e => e.1 = x).card ≤ 3 := by
  let L := legSlots G x
  have hLegCard : L.card = ((originalLegs G).filter fun e => e.1 = x).card := by
    unfold L legSlots
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have ha' : a.1 = x := (Finset.mem_filter.mp ha).2
    have hb' : b.1 = x := (Finset.mem_filter.mp hb).2
    cases a with
    | mk a₁ a₂ =>
      cases b with
      | mk b₁ b₂ =>
        simp_all
  have hDis : Disjoint (D.presentNeighbours x) L := by
    apply Finset.disjoint_left.mpr
    intro a ha hLa
    have haActive : a ∈ D.active := (Finset.mem_filter.mp ha).2.2.1
    have haG : a ∈ G := (Finset.mem_filter.mp haActive).1
    have hLa' : a ∉ G := by
      rcases Finset.mem_image.mp hLa with ⟨e, he, hae⟩
      have hex : (e.1, e.2) ∈ originalLegs G := (Finset.mem_filter.mp he).1
      have hnot := (originalLeg_endpoint hex).2
      intro haG'
      exact hnot (hae ▸ haG')
    exact hLa' haG
  have hSub : D.presentNeighbours x ∪ L ⊆ (neighbours x).erase z := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have hN : a ∈ neighbours x := (Finset.mem_filter.mp ha).1
      have hneq : a ≠ z := by
        intro heq
        subst a
        exact hzAbsent ha
      exact Finset.mem_erase.mpr ⟨hneq, hN⟩
    · rcases Finset.mem_image.mp ha with ⟨e, he, hae⟩
      have hex : (e.1, e.2) ∈ originalLegs G := (Finset.mem_filter.mp he).1
      have heq : e.1 = x := (Finset.mem_filter.mp he).2
      have hN : e.2 ∈ neighbours x := by
        simpa [heq] using (originalLeg_endpoint hex).1
      have hnotG := (originalLeg_endpoint hex).2
      have hneq : a ≠ z := by
        intro heq'
        apply hnotG
        rw [hae, heq']
        exact hzG
      exact Finset.mem_erase.mpr ⟨hneq, by simpa [hae] using hN⟩
  have hcardUnion : (D.presentNeighbours x ∪ L).card =
      (D.presentNeighbours x).card + L.card := Finset.card_union_of_disjoint hDis
  calc
    (D.presentNeighbours x).card + ((originalLegs G).filter fun e => e.1 = x).card =
        (D.presentNeighbours x ∪ L).card := by rw [hcardUnion, hLegCard]
    _ ≤ ((neighbours x).erase z).card := Finset.card_le_card hSub
    _ = 3 := by rw [Finset.card_erase_of_mem hzN, neighbours_card]

theorem main : AKLT.Blueprint.Rec.SecondStartStatement := by
  intro p hvOutside n w hstop hend
  let q : PairData := p.toPairData
  rcases p.pair with ⟨hcons, huactive, hvactive, hcG, hcX, huc, hvc, htype, huCase, hvCase⟩
  let e := wordVertex p.u w n
  let E0 := traceNetwork p.normalized (wordVertices p.u w)
  let E := normalizeStart E0 p.v p.c
  have hcInactive : p.c ∉ p.normalized.active := by
    change p.c ∉ p.normalized.active
    simp only [Network.active, Finset.mem_filter]
    intro h
    exact h.2 (by simpa [PairData.normalized, normalizeStart] using hcX)
  have havoidV : ∀ j < n, wordVertex p.u w j ≠ p.v := by
    intro j hj heq
    have hnot := (hstop.2.2.1 j hj).1
    apply hnot
    rw [heq]
    exact Finset.mem_insert_self p.v (protectedSites p.G)
  have havoidC : ∀ j < n, wordVertex p.u w j ≠ p.c := by
    intro j hj heq
    have hEdge := hstop.2.1 ⟨j, hj⟩
    apply hcInactive
    simpa [heq] using hEdge.1
  have haux0 : E0.Auxiliary := by
    dsimp [E0]
    rw [← prefix_final]
    exact prefix_auxiliary q w hstop n le_rfl
  have hstatusV : E0.status p.v = p.normalized.status p.v := by
    change (traceNetwork p.normalized (wordVertices p.u w)).status p.v = _
    rw [← prefix_final]
    exact prefix_status_eq q w havoidV n le_rfl
  have hstatusC : E0.status p.c = .X := by
    have hnorm : p.normalized.status p.c = .X := by
      simpa [PairData.normalized, normalizeStart] using hcX
    change (traceNetwork p.normalized (wordVertices p.u w)).status p.c = .X
    rw [← prefix_final]
    rw [prefix_status_eq q w havoidC n le_rfl]
    exact hnorm
  have hauxE : E.Auxiliary := by
    dsimp [E]
    exact normalize_auxiliary E0 haux0 hstatusC
  have hstatusE_v : E.status p.v = p.D.status p.v := by
    calc
      E.status p.v = E0.status p.v := rfl
      _ = p.normalized.status p.v := hstatusV
      _ = p.D.status p.v := rfl
  have hstatusE_c : E.status p.c = .X := by
    change E0.status p.c = .X
    exact hstatusC
  have hnormPN : p.normalized.presentNeighbours p.v = p.D.presentNeighbours p.v := by
    simpa [PairData.normalized] using normalize_presentNeighbours_eq p.D hcX p.v
  have hPNsub : E.presentNeighbours p.v ⊆ p.normalized.presentNeighbours p.v := by
    rw [normalize_presentNeighbours_eq E0 hstatusC]
    dsimp [E0]
    rw [← prefix_final]
    exact prefix_pn_subset_initial q w n le_rfl p.v
  have hstart : E.AdmissibleStart p.v := by
    refine ⟨?_, hvOutside, ?_⟩
    · have hnormActive : p.v ∈ p.normalized.active := by
        change p.v ∈ p.D.active
        exact hvactive
      have hG : p.v ∈ p.G := (Finset.mem_filter.mp hnormActive).1
      have hneX : p.normalized.status p.v ≠ .X := (Finset.mem_filter.mp hnormActive).2
      have hE0neX : E0.status p.v ≠ .X := by rw [hstatusV]; exact hneX
      have hEneX : E.status p.v ≠ .X := by
        change E0.status p.v ≠ .X
        exact hE0neX
      exact Finset.mem_filter.mpr ⟨hG, hEneX⟩
    · rcases hvCase with hU | ⟨hD, hdeg⟩
      · left
        refine ⟨?_, ?_⟩
        · exact hstatusE_v.trans hU
        · have hcenter : p.c ∈ neighbours p.v := adjacent_mem_neighbors hvc
          have hsubN := pn_subset_neighbours_erase p.normalized (x := p.v) hcInactive
          have hdegN : (p.normalized.presentNeighbours p.v).card ≤ 3 := by
            calc
              _ ≤ ((neighbours p.v).erase p.c).card := Finset.card_le_card hsubN
              _ = (neighbours p.v).card - 1 := Finset.card_erase_of_mem hcenter
              _ = 3 := by rw [neighbours_card]
          exact (Finset.card_le_card hPNsub).trans hdegN
      · right
        refine ⟨?_, ?_⟩
        · exact hstatusE_v.trans hD
        · calc
            (E.presentNeighbours p.v).card ≤ (p.normalized.presentNeighbours p.v).card :=
              Finset.card_le_card hPNsub
            _ = (p.D.presentNeighbours p.v).card := congrArg Finset.card hnormPN
            _ ≤ 1 := hdeg
  have hnoIncoming : ¬ E.Present p.c p.v := by
    intro hpres
    have hcActive : p.c ∈ E.active := hpres.1
    have hcNotX : E.status p.c ≠ .X := (Finset.mem_filter.mp hcActive).2
    exact hcNotX hstatusE_c
  have hEfactor : (E.presentNeighbours e).card +
      ((originalLegs p.G).filter fun b => b.1 = e).card ≤ 3 := by
    by_cases hn : n = 0
    · subst n
      have heq : e = p.u := by simp [e, wordVertex]
      have hcN : p.c ∈ neighbours e := by simpa [heq] using adjacent_mem_neighbors huc
      have hcAbsent : p.c ∉ E.presentNeighbours e := by
        intro hz
        have hcAct : p.c ∈ E.active := (Finset.mem_filter.mp hz).2.2.1
        have hcNotX : E.status p.c ≠ .X := (Finset.mem_filter.mp hcAct).2
        exact hcNotX hstatusE_c
      exact factor_count_le_three_of_missing E hcN hcG hcAbsent
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let prev := wordVertex p.u w (n - 1)
      have hprevAbsent : prev ∉ E.presentNeighbours e := by
        have h0 := prefix_arrival_absent q w hstop hnpos (by omega)
        have h0' : prev ∉ E0.presentNeighbours e := by
          dsimp [E0, e, prev]
          rw [← prefix_final]
          simpa using h0
        rw [normalize_presentNeighbours_eq E0 hstatusC e]
        exact h0'
      have hEdge := hstop.2.1 ⟨n - 1, by omega⟩
      have hprevG : prev ∈ p.G := (Finset.mem_filter.mp hEdge.1).1
      have hAdj : Adjacent e prev := by
        have hs := adjacent_symm hEdge.2.2.1
        simpa [e, prev, Nat.sub_add_cancel (by omega : 1 ≤ n)] using hs
      have hprevN : prev ∈ neighbours e := adjacent_mem_neighbors hAdj
      exact factor_count_le_three_of_missing E hprevN hprevG hprevAbsent
  have htargetStatus : E.status e = .U := hauxE.2 e hend
  have htargetActive : e ∈ E.active := by
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hend).1, ?_⟩
    rw [htargetStatus]
    decide
  change E.Auxiliary ∧ E.AdmissibleStart p.v ∧ ¬ E.Present p.c p.v ∧
    AdmissibleTarget E e
  exact ⟨hauxE, hstart, hnoIncoming,
    ⟨htargetActive, Or.inl ⟨htargetStatus, hEfactor⟩⟩⟩

end AKLT.W.REC055
