import AKLT.Blueprint.Rec.NodesWalk

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC039

theorem adjacent_mem_neighbours {x y : Plane} (h : Adjacent x y) : y ∈ neighbours x := by
  classical
  unfold Adjacent latticeDist at h
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp only [Prod.mk.injEq, Compass.step] at h ⊢
  have hab : (a - c).natAbs + (b - d).natAbs = 1 := h
  have hx : (a - c).natAbs = 0 ∨ (a - c).natAbs = 1 := by omega
  have hy : (b - d).natAbs = 0 ∨ (b - d).natAbs = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · omega
  · have hac : a = c := by omega
    have hbd : b = d + 1 ∨ b = d - 1 := by omega
    rcases hbd with hbd | hbd
    · refine ⟨Compass.south, ?_⟩
      simp [Compass.step, hac, hbd]
    · refine ⟨Compass.north, ?_⟩
      simp [Compass.step, hac, hbd]
  · have hbc : b = d := by omega
    have hac : a = c + 1 ∨ a = c - 1 := by omega
    rcases hac with hac | hac
    · refine ⟨Compass.west, ?_⟩
      simp [Compass.step, hbc, hac]
    · refine ⟨Compass.east, ?_⟩
      simp [Compass.step, hbc, hac]
  · omega

theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent latticeDist at h ⊢
  have h1 : y.1 - x.1 = -(x.1 - y.1) := by ring
  have h2 : y.2 - x.2 = -(x.2 - y.2) := by ring
  rw [h1, h2, Int.natAbs_neg, Int.natAbs_neg]
  exact h

theorem adjacent_ne {x y : Plane} (h : Adjacent x y) : x ≠ y := by
  intro heq
  subst y
  simp [Adjacent, latticeDist] at h

theorem traceStep_active_subset {G : Finset Plane} (D : Network G) (y o x : Plane)
    (hx : x ∈ (traceStep D y o).active) : x ∈ D.active := by
  by_cases hxy : x = y
  · subst x
    simp only [Network.active, Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    by_cases hs : D.status y = .U
    · simp [traceStep, hs]
    · cases hD : D.status y <;> simp [traceStep, hD] at hx ⊢ <;> simp_all
  · have hstat : (traceStep D y o).status x = D.status x := by simp [traceStep, hxy]
    simpa [Network.active, Finset.mem_filter, hstat] using hx

theorem traceStep_kept_subset {G : Finset Plane} (D : Network G) (y o x : Plane) :
    (traceStep D y o).kept x ⊆ D.kept x := by
  classical
  by_cases hxy : x = y
  · subst x
    simpa [traceStep] using (Finset.erase_subset o (D.kept y))
  · by_cases hxo : x = o
    · subst x
      simpa [traceStep, hxy] using (Finset.erase_subset y (D.kept o))
    · simp [traceStep, hxy, hxo]

theorem traceStep_present_subset {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (h : (traceStep D y o).Present x z) : D.Present x z := by
  rcases h with ⟨hx, hz, hadj, hzx, hxz⟩
  refine ⟨traceStep_active_subset D y o x hx, traceStep_active_subset D y o z hz,
    hadj, traceStep_kept_subset D y o x hzx, traceStep_kept_subset D y o z hxz⟩

theorem present_symm {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : D.Present x z) : D.Present z x := by
  exact ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem traceStep_present_of_away {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (h : D.Present x z) (hoy : o ≠ y) (hx : x ≠ y) (hz : z ≠ y) :
    (traceStep D y o).Present x z := by
  rcases h with ⟨hxa, hza, hadj, hzx, hxz⟩
  have hxa' : x ∈ (traceStep D y o).active := by
    rcases Finset.mem_filter.mp hxa with ⟨hg, hs⟩
    apply Finset.mem_filter.mpr
    refine ⟨hg, ?_⟩
    have hstatus : (traceStep D y o).status x = D.status x := by
      simp [traceStep, Function.update_of_ne hx]
    simpa [hstatus] using hs
  have hza' : z ∈ (traceStep D y o).active := by
    rcases Finset.mem_filter.mp hza with ⟨hg, hs⟩
    apply Finset.mem_filter.mpr
    refine ⟨hg, ?_⟩
    have hstatus : (traceStep D y o).status z = D.status z := by
      simp [traceStep, Function.update_of_ne hz]
    simpa [hstatus] using hs
  have hzx' : z ∈ (traceStep D y o).kept x := by
    by_cases hxo : x = o
    · subst x
      have hzy : z ≠ y := hz
      simpa [traceStep, hoy, hzy] using hzx
    · simpa [traceStep, hoy, hx, hxo] using hzx
  have hxz' : x ∈ (traceStep D y o).kept z := by
    by_cases hzo : z = o
    · subst z
      have hxy : x ≠ y := hx
      simpa [traceStep, hoy, hxy] using hxz
    · simpa [traceStep, hoy, hz, hzo] using hxz
  exact ⟨hxa', hza', hadj, hzx', hxz'⟩

theorem traceStep_present_of_u {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (hyo : D.Present y o) (h : D.Present x z) (hU : D.status y = .U)
    (hxy : ¬ (x = y ∧ z = o)) (hyx : ¬ (x = o ∧ z = y)) :
    (traceStep D y o).Present x z := by
  rcases h with ⟨hxa, hza, hadj, hzx, hxz⟩
  have hoy : o ≠ y := adjacent_ne (adjacent_symm hyo.2.2.1)
  have hxa' : x ∈ (traceStep D y o).active := by
    by_cases hxy' : x = y
    · subst x
      have hG : y ∈ G := (Finset.mem_filter.mp hxa).1
      apply Finset.mem_filter.mpr
      refine ⟨hG, ?_⟩
      simp [Network.active, traceStep, hU]
    · rcases Finset.mem_filter.mp hxa with ⟨hg, hs⟩
      apply Finset.mem_filter.mpr
      refine ⟨hg, ?_⟩
      have hstatus : (traceStep D y o).status x = D.status x := by
        simp [traceStep, Function.update_of_ne hxy']
      simpa [hstatus] using hs
  have hza' : z ∈ (traceStep D y o).active := by
    by_cases hzy' : z = y
    · subst z
      have hG : y ∈ G := (Finset.mem_filter.mp hza).1
      apply Finset.mem_filter.mpr
      refine ⟨hG, ?_⟩
      simp [Network.active, traceStep, hU]
    · rcases Finset.mem_filter.mp hza with ⟨hg, hs⟩
      apply Finset.mem_filter.mpr
      refine ⟨hg, ?_⟩
      have hstatus : (traceStep D y o).status z = D.status z := by
        simp [traceStep, Function.update_of_ne hzy']
      simpa [hstatus] using hs
  have hzx' : z ∈ (traceStep D y o).kept x := by
    by_cases hxy' : x = y
    · subst x
      have hne : z ≠ o := by
        intro heq
        exact hxy ⟨rfl, heq⟩
      simpa [traceStep, hne] using hzx
    · by_cases hxo : x = o
      · subst x
        have hne : z ≠ y := by
          intro heq
          exact hyx ⟨rfl, heq⟩
        simpa [traceStep, hoy, hxy', hne] using hzx
      · simpa [traceStep, hxy', hxo] using hzx
  have hxz' : x ∈ (traceStep D y o).kept z := by
    by_cases hzy' : z = y
    · subst z
      have hne : x ≠ o := by
        intro heq
        exact hyx ⟨heq, rfl⟩
      simpa [traceStep, hne] using hxz
    · by_cases hzo : z = o
      · subst z
        have hne : x ≠ y := by
          intro heq
          exact hxy ⟨heq, rfl⟩
        simpa [traceStep, hoy, hzy', hne] using hxz
      · simpa [traceStep, hzy', hzo] using hxz
  exact ⟨hxa', hza', hadj, hzx', hxz'⟩

theorem traceStep_source_edge_absent {G : Finset Plane} (D : Network G) (y o : Plane)
    (hyo : D.Present y o) : ¬ (traceStep D y o).Present y o := by
  intro h
  rcases h with ⟨_, _, _, hkeep, _⟩
  have hykeep : (traceStep D y o).kept y = (D.kept y).erase o := by simp [traceStep]
  rw [hykeep] at hkeep
  exact (Finset.mem_erase.mp hkeep).1 rfl

theorem traceStep_target_edge_absent {G : Finset Plane} (D : Network G) (y o : Plane)
    (hyo : D.Present y o) : ¬ (traceStep D y o).Present o y := by
  intro h
  rcases h with ⟨_, _, _, hkeep, _⟩
  have hokeep : (traceStep D y o).kept o = (D.kept o).erase y := by
    have hne : o ≠ y := adjacent_ne (adjacent_symm hyo.2.2.1)
    simp [traceStep, hne]
  rw [hokeep] at hkeep
  exact (Finset.mem_erase.mp hkeep).1 rfl

theorem traceStep_degree_strict_source {G : Finset Plane} (D : Network G) (y o : Plane)
    (hyo : D.Present y o) :
    (traceStep D y o).presentNeighbours y ⊂ D.presentNeighbours y := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      traceStep_present_subset D y o y z (Finset.mem_filter.mp hz).2⟩
  · intro heq
    have hmem : o ∈ D.presentNeighbours y := by
      apply Finset.mem_filter.mpr
      exact ⟨adjacent_mem_neighbours hyo.2.2.1, hyo⟩
    have : o ∈ (traceStep D y o).presentNeighbours y := by simpa [heq] using hmem
    exact traceStep_source_edge_absent D y o hyo (Finset.mem_filter.mp this).2

theorem traceStep_degree_strict_target {G : Finset Plane} (D : Network G) (y o : Plane)
    (hyo : D.Present y o) :
    (traceStep D y o).presentNeighbours o ⊂ D.presentNeighbours o := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      traceStep_present_subset D y o o z (Finset.mem_filter.mp hz).2⟩
  · intro heq
    have hmem : y ∈ D.presentNeighbours o := by
      apply Finset.mem_filter.mpr
      exact ⟨adjacent_mem_neighbours (adjacent_symm hyo.2.2.1),
        ⟨hyo.2.1, hyo.1, adjacent_symm hyo.2.2.1, hyo.2.2.2.2, hyo.2.2.2.1⟩⟩
    have : y ∈ (traceStep D y o).presentNeighbours o := by simpa [heq] using hmem
    exact traceStep_target_edge_absent D y o hyo (Finset.mem_filter.mp this).2

theorem traceStep_auxiliary {G : Finset Plane} (D : Network G) (y o : Plane)
    (hD : D.Auxiliary) (hy : y ∉ protectedSites G) (hyo : D.Present y o)
    (hUdeg : D.status y = .U → (D.presentNeighbours y).card ≤ 3) :
    (traceStep D y o).Auxiliary := by
  classical
  have hsrcG : y ∈ G := (Finset.mem_filter.mp hyo.1).1
  have hsrcActive : y ∈ D.active := hyo.1
  have hsourceCard : (traceStep D y o).presentNeighbours y ⊂ D.presentNeighbours y :=
    traceStep_degree_strict_source D y o hyo
  have htargetCard : (traceStep D y o).presentNeighbours o ⊂ D.presentNeighbours o :=
    traceStep_degree_strict_target D y o hyo
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hxG
      by_cases hxy : x = y
      · subst x
        exact False.elim (hxG hsrcG)
      · simpa [traceStep, hxy] using hD.1.1 x hxG
    · intro x z hz
      exact hD.1.2.1 x (traceStep_kept_subset D y o x hz)
    · intro x hxG hxD
      by_cases hxy : x = y
      · subst x
        have hstatusU : D.status y = .U := by
          simp [traceStep] at hxD
          cases hs : D.status y <;> simp [traceStep, hs] at hxD ⊢
        have hlt : ((traceStep D y o).presentNeighbours y).card <
            (D.presentNeighbours y).card := Finset.card_lt_card hsourceCard
        have hpre : (D.presentNeighbours y).card ≤ 3 := hUdeg hstatusU
        omega
      · have hs : D.status x = .D := by simpa [traceStep, hxy] using hxD
        have hpre := hD.1.2.2.1 x hxG hs
        have hsub : (traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x := by
          intro z hz
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
            traceStep_present_subset D y o x z (Finset.mem_filter.mp hz).2⟩
        have hle := Finset.card_le_card hsub
        omega
    · intro x hx
      have hx' := traceStep_active_subset D y o x hx
      have hpre := hD.1.2.2.2 x hx'
      have hsub : (traceStep D y o).presentNeighbours x ⊆ D.presentNeighbours x := by
        intro z hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
          traceStep_present_subset D y o x z (Finset.mem_filter.mp hz).2⟩
      have hle := Finset.card_le_card hsub
      omega
  · intro x hx
    have hxy : x ≠ y := by
      intro heq
      subst x
      exact hy hx
    simpa [traceStep, hxy] using hD.2 x hx

theorem traceStep_admissible_target {G : Finset Plane} (D : Network G) (y o : Plane)
    (hD : D.Auxiliary) (hyo : D.Present y o) (ho : o ∉ protectedSites G) :
    (traceStep D y o).AdmissibleStart o := by
  classical
  have hne : o ≠ y := adjacent_ne (adjacent_symm hyo.2.2.1)
  have hactive : o ∈ (traceStep D y o).active := by
    rcases Finset.mem_filter.mp hyo.2.1 with ⟨hg, hs⟩
    apply Finset.mem_filter.mpr
    refine ⟨hg, ?_⟩
    have hstatus : (traceStep D y o).status o = D.status o := by
      simp [traceStep, Function.update_of_ne hne]
    simpa [hstatus] using hs
  have hstatus : (traceStep D y o).status o = D.status o := by simp [traceStep, hne]
  have hnotX : D.status o ≠ .X := (Finset.mem_filter.mp hyo.2.1).2
  have hnewlt : (traceStep D y o).presentNeighbours o ⊂ D.presentNeighbours o :=
    traceStep_degree_strict_target D y o hyo
  have hcardlt : ((traceStep D y o).presentNeighbours o).card <
      (D.presentNeighbours o).card := Finset.card_lt_card hnewlt
  refine ⟨hactive, ho, ?_⟩
  cases hs : D.status o with
  | U =>
      have htotal := hD.1.2.2.2 o hyo.2.1
      have hcard : (D.presentNeighbours o).card ≤ 4 := by omega
      have hnew : ((traceStep D y o).presentNeighbours o).card ≤ 3 := by omega
      exact Or.inl ⟨by simpa [hstatus] using hs, hnew⟩
  | D =>
      have hG : o ∈ G := (Finset.mem_filter.mp hyo.2.1).1
      have hdegree := hD.1.2.2.1 o hG hs
      have hnew : ((traceStep D y o).presentNeighbours o).card ≤ 1 := by omega
      exact Or.inr ⟨by simpa [hstatus] using hs, hnew⟩
  | X => exact False.elim (hnotX hs)

theorem card_presentNeighbours_ge_two {G : Finset Plane} (D : Network G)
    (y a b : Plane) (hya : D.Present y a) (hyb : D.Present y b) (hab : a ≠ b) :
    2 ≤ (D.presentNeighbours y).card := by
  have ha : a ∈ D.presentNeighbours y :=
    Finset.mem_filter.mpr ⟨adjacent_mem_neighbours hya.2.2.1, hya⟩
  have hb : b ∈ D.presentNeighbours y :=
    Finset.mem_filter.mpr ⟨adjacent_mem_neighbours hyb.2.2.1, hyb⟩
  have hsub : ({a, b} : Finset Plane) ⊆ D.presentNeighbours y := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxa | hxb
    · subst x
      exact ha
    · have hxb' : x = b := by simpa using hxb
      subst x
      exact hb
  have hcard := Finset.card_le_card hsub
  simpa [hab] using hcard

theorem traceNetwork_snoc {G : Finset Plane} (D : Network G) (l : List Plane)
    (o : Plane) (hl : l ≠ []) :
    traceNetwork D (l ++ [o]) =
      traceStep (traceNetwork D l) (l.getLast hl) o := by
  induction l generalizing D o with
  | nil => contradiction
  | cons a rest ih =>
      cases rest with
      | nil => simp [traceNetwork]
      | cons b rest =>
          have htail : (b :: rest) ≠ [] := by simp
          change traceNetwork (traceStep D a b) ((b :: rest) ++ [o]) =
            traceStep (traceNetwork (traceStep D a b) (b :: rest))
              ((a :: b :: rest).getLast hl) o
          rw [ih (traceStep D a b) o htail]
          have hlast : (a :: b :: rest).getLast hl = (b :: rest).getLast htail :=
            List.getLast_cons htail
          rw [hlast]

theorem wordVertices_get {n : ℕ} (u : Plane) (w : DirectionWord n) (i : ℕ)
    (hi : i ≤ n) : (wordVertices u w)[i]? = some (wordVertex u w i) := by
  simp [wordVertices, Nat.lt_succ_of_le hi]

theorem prefixNetwork_succ {G : Finset Plane} (D : Network G) {n : ℕ}
    (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    prefixNetwork D u w (j + 1) =
      traceStep (prefixNetwork D u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  let V := wordVertices u w
  have hjle : j ≤ n := Nat.le_of_lt hj
  have hgetj : V[j]? = some (wordVertex u w j) := by
    simpa [V] using wordVertices_get u w j hjle
  have hgetnext : V[j + 1]? = some (wordVertex u w (j + 1)) := by
    apply wordVertices_get
    omega
  have htakej : V.take (j + 1) = V.take j ++ [wordVertex u w j] := by
    rw [List.take_succ]
    simp [hgetj]
  have htakenext : V.take (j + 2) = V.take (j + 1) ++ [wordVertex u w (j + 1)] := by
    have hnum : j + 2 = (j + 1) + 1 := by omega
    rw [hnum, List.take_succ, hgetnext, Option.toList_some]
  have hne : V.take (j + 1) ≠ [] := by
    intro hnil
    have hzero := (List.take_eq_nil_iff).mp hnil
    simp [V, wordVertices] at hzero
  have hlast : (V.take (j + 1)).getLast hne = wordVertex u w j := by
    have hsnoc : V.take j ++ [wordVertex u w j] ≠ [] := by simp
    have hlast' : (V.take j ++ [wordVertex u w j]).getLast hsnoc = wordVertex u w j := by
      rw [List.getLast_append_of_ne_nil hsnoc (by simp)]
      simp
    simpa [htakej] using hlast'
  unfold prefixNetwork
  change traceNetwork D (V.take (j + 2)) =
    traceStep (traceNetwork D (V.take (j + 1))) (wordVertex u w j)
      (wordVertex u w (j + 1))
  rw [htakenext, traceNetwork_snoc D (V.take (j + 1)) _ hne, hlast]

theorem trace_prefix_invariant {G : Finset Plane} (D : Network G) (hD : D.Auxiliary)
    (u : Plane) (hstart : D.AdmissibleStart u) (T : Finset Plane) {n : ℕ}
    (w : DirectionWord n) (htrail : StoppedNetworkTrail D u T w) :
    ∀ j ≤ n,
      (prefixNetwork D u w j).Auxiliary ∧
      (∀ k : Fin n, j ≤ k.val →
        (prefixNetwork D u w j).Present (wordVertex u w k.val)
          (wordVertex u w (k.val + 1))) ∧
      (j < n → (prefixNetwork D u w j).AdmissibleStart (wordVertex u w j)) := by
  classical
  intro j
  induction j with
  | zero =>
      intro hj
      have hv0 : wordVertex u w 0 = u := by simp [wordVertex]
      have hget0 : (wordVertices u w)[0]? = some u := by
        simpa [hv0] using wordVertices_get u w 0 (Nat.zero_le n)
      have htake0 : (wordVertices u w).take 1 = [u] := by
        rw [List.take_succ]
        simp [hget0]
      have hzero : prefixNetwork D u w 0 = D := by
        simp [prefixNetwork, htake0, traceNetwork]
      refine ⟨?_, ?_, ?_⟩
      · simpa [hzero] using hD
      · intro k hk
        have hp := htrail.2.1 k
        simpa [hzero] using hp
      · intro _
        simpa [hzero, hv0] using hstart
  | succ j ih =>
      intro hj
      have hjn : j ≤ n := by omega
      have hjlt : j < n := by omega
      have hprev := ih hjn
      let E := prefixNetwork D u w j
      let y := wordVertex u w j
      let o := wordVertex u w (j + 1)
      have hcur : E.Present y o := by
        simpa [E, y, o] using hprev.2.1 ⟨j, hjlt⟩ (by rfl)
      have hoy : o ≠ y := adjacent_ne (adjacent_symm hcur.2.2.1)
      have hprevStart : E.AdmissibleStart y := hprev.2.2 hjlt
      have hsourceUdeg : E.status y = .U → (E.presentNeighbours y).card ≤ 3 := by
        intro hyU
        rcases hprevStart.2.2 with hU | hD'
        · exact hU.2
        · rw [hD'.1] at hyU
          cases hyU
      have hyProtected : y ∉ protectedSites G := (htrail.2.2.1 j hjlt).2
      have hnextEq : prefixNetwork D u w (j + 1) = traceStep E y o := by
        simpa [E, y, o] using prefixNetwork_succ D u w j hjlt
      have hnextAux : (prefixNetwork D u w (j + 1)).Auxiliary := by
        rw [hnextEq]
        exact traceStep_auxiliary E y o hprev.1 hyProtected hcur hsourceUdeg
      have hfuture : ∀ k : Fin n, j + 1 ≤ k.val →
          (prefixNetwork D u w (j + 1)).Present (wordVertex u w k.val)
            (wordVertex u w (k.val + 1)) := by
        intro k hkj
        have hOld : E.Present (wordVertex u w k.val) (wordVertex u w (k.val + 1)) :=
          hprev.2.1 k (by omega)
        have hneCurrent : k ≠ (⟨j, hjlt⟩ : Fin n) := by
          intro heq
          have : k.val = j := by simpa using congrArg Fin.val heq
          omega
        have hbonds : wordBond u w k ≠ wordBond u w ⟨j, hjlt⟩ := by
          intro heq
          exact hneCurrent (htrail.1 heq)
        have hnotDirect : ¬ (wordVertex u w k.val = y ∧
            wordVertex u w (k.val + 1) = o) := by
          intro hh
          apply hbonds
          simp [wordBond, y, o, hh.1, hh.2]
        have hnotReverse : ¬ (wordVertex u w k.val = o ∧
            wordVertex u w (k.val + 1) = y) := by
          intro hh
          apply hbonds
          simp [wordBond, y, o, hh.1, hh.2, Finset.pair_comm]
        rw [hnextEq]
        rcases hprevStart.2.2 with ⟨hyU, _⟩ | ⟨hyD, hdegD⟩
        · exact traceStep_present_of_u E y o (wordVertex u w k.val)
            (wordVertex u w (k.val + 1)) hcur hOld hyU hnotDirect hnotReverse
        · have hxne : wordVertex u w k.val ≠ y := by
            intro heq
            have hzo : wordVertex u w (k.val + 1) ≠ o := by
              intro heq'
              exact hnotDirect ⟨heq, heq'⟩
            have hOld' : E.Present y (wordVertex u w (k.val + 1)) := by
              simpa [y, heq] using hOld
            have htwo := card_presentNeighbours_ge_two E y o
              (wordVertex u w (k.val + 1)) hcur hOld' hzo.symm
            omega
          have hzne : wordVertex u w (k.val + 1) ≠ y := by
            intro heq
            have hxo : wordVertex u w k.val ≠ o := by
              intro heq'
              exact hnotReverse ⟨heq', heq⟩
            have hOldSymm := present_symm hOld
            have hOldSymm' : E.Present y (wordVertex u w k.val) := by
              simpa [y, heq] using hOldSymm
            have htwo := card_presentNeighbours_ge_two E y o
              (wordVertex u w k.val) hcur hOldSymm' hxo.symm
            omega
          exact traceStep_present_of_away E y o (wordVertex u w k.val)
            (wordVertex u w (k.val + 1)) hOld hoy hxne hzne
      refine ⟨hnextAux, hfuture, ?_⟩
      intro hjnext
      have hoProtected : o ∉ protectedSites G := by
        exact (htrail.2.2.1 (j + 1) (by omega)).2
      rw [hnextEq]
      exact traceStep_admissible_target E y o hprev.1 hcur hoProtected

theorem main : AKLT.Blueprint.Rec.TraceDynamicsStatement := by
  unfold AKLT.Blueprint.Rec.TraceDynamicsStatement
  intro G D hD u hstart T n w htrail
  have hInv := trace_prefix_invariant D hD u hstart T w htrail
  constructor
  · intro j hj
    exact (hInv j hj).1
  · intro i
    have h := hInv i.val (Nat.le_of_lt i.isLt)
    exact ⟨h.2.2 i.isLt, h.2.1 i (Nat.le_refl _)⟩

end AKLT.W.REC039
