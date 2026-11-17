module
public import AKLT.W.REC080.Exceptions
public import AKLT.W.REC054.Main
public import AKLT.W.REC096.Main
public import AKLT.W.REC039.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

theorem normalize_auxiliary {G : Finset Plane} (D : Network G) (u c : Plane)
    (hD : D.Auxiliary) (hc : D.status c = .X) :
    (normalizeStart D u c).Auxiliary := by
  have hn (x : Plane) : (normalizeStart D u c).presentNeighbors x =
      D.presentNeighbors x := by
    ext z
    simp only [Network.presentNeighbors, Finset.mem_filter, normalize_present D u c hc]
  refine ⟨⟨hD.1.1, ?_, ?_, ?_⟩, hD.2⟩
  · intro x z hz
    apply hD.1.2.1 x
    dsimp [normalizeStart] at hz
    split_ifs at hz
    · exact Finset.mem_of_mem_erase hz
    · exact hz
  · intro x hx hs
    rw [hn]
    exact hD.1.2.2.1 x hx hs
  · intro x hx
    rw [hn]
    exact hD.1.2.2.2 x hx

theorem terminal_auxiliary (p : PairData) (hu : p.u ∉ protectedSites p.G)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G) :
    (terminalNetwork p w).Auxiliary := by
  obtain ⟨incoming, hi⟩ := adjacent_direction p.pair.2.2.2.2.2.1
  let ps : PairSetup := ⟨p, incoming, hi, hu⟩
  have ht : StoppedNetworkTrail ps.normalized ps.u (protectedSites ps.G) w :=
    ⟨hw.1, hw.2.1, fun j hj => ⟨(hw.2.2.1 j hj).2, (hw.2.2.1 j hj).2⟩, he⟩
  exact normalize_auxiliary _ _ _ (AKLT.W.REC054.main ps n w ht).1
    (trace_removed p.normalized p.c p.pair.2.2.2.2.1 _)

/-- During the second walk the first protected hit is the only fixed defect.
All other kept-set defects are at the moving endpoint. -/
structure DefectInvariant {G : Finset Plane} (E : Network G) (y a e : Plane) : Prop where
  outside : ∀ x, x ∉ G → E.status x = .X
  kept_sub : ∀ x, E.kept x ⊆ neighbors x ∩ G
  u_full : ∀ x ∈ G, x ≠ y → x ≠ e → E.status x = .U →
    E.kept x = neighbors x ∩ G
  d_two : ∀ x ∈ G, x ≠ y → E.status x = .D → (E.kept x).card = 2
  agree : ∀ x ∈ E.active, ∀ z ∈ E.active, Adjacent x z →
    (z ∈ E.kept x ↔ x ∈ E.kept z)
  arrival_adj : Adjacent y a
  arrival_notU : E.status a ≠ .U
  liveU : E.status y = .U → E.kept y = (neighbors y ∩ G).erase a
  liveD : E.status y = .D → ∀ x z, E.Present y x → E.Present y z → x = z
  fixedU : E.status e = .U

theorem defect_step {G : Finset Plane} {E : Network G} {y a e o : Plane}
    (h : DefectInvariant E y a e) (hy : y ∉ protectedSites G)
    (he : e ∈ protectedSites G) (ho : o ≠ e) (hp : E.Present y o) :
    DefectInvariant (traceStep E y o) o y e := by
  classical
  have hyG := (Finset.mem_filter.mp hp.1).1
  have hoG := (Finset.mem_filter.mp hp.2.1).1
  have hyo := AKLT.W.REC096.adjacent_ne hp.2.2.1
  have hye : y ≠ e := by rintro rfl; exact hy he
  have hfull : neighbors y ∩ G = neighbors y := by
    apply Finset.inter_eq_left.mpr
    intro z hz
    exact AKLT.W.REC096.interior_ball hyG hy
      (((AKLT.W.REC096.adjacent_iff _ _).mpr hz).le.trans (by decide))
  have hUcard (hu : E.status y = .U) : (E.kept y).card = 3 := by
    rw [h.liveU hu, hfull,
      Finset.card_erase_of_mem ((AKLT.W.REC096.adjacent_iff _ _).mp h.arrival_adj),
      neighbors_card]
  refine ⟨?_, ?_, ?_, ?_, ?_, AKLT.W.REC096.adjacent_symm hp.2.2.1,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [AKLT.W.REC096.step_status_ne E y o x (fun hx' => hx (hx' ▸ hyG))]
    exact h.outside x hx
  · intro x z hz
    exact h.kept_sub x ((AKLT.W.REC096.step_kept_iff E y o x z).mp hz).1
  · intro x hx hxo hxe hu
    have hxy : x ≠ y := by
      rintro rfl
      simp only [traceStep, Function.update_self] at hu
      split_ifs at hu
    rw [AKLT.W.REC096.step_status_ne E y o x hxy] at hu
    simpa [traceStep, hxy, hxo] using h.u_full x hx hxy hxe hu
  · intro x hx hxo hd
    by_cases hxy : x = y
    · subst x
      have hu : E.status y = .U := by
        by_contra hn
        simp [traceStep, hn] at hd
      simp [traceStep, Finset.card_erase_of_mem hp.2.2.2.1, hUcard hu]
    · rw [AKLT.W.REC096.step_status_ne E y o x hxy] at hd
      simpa [traceStep, hxy, hxo] using h.d_two x hx hxy hd
  · intro x hx z hz hadj
    have hm := h.agree x (traceStep_active_subset E y o hx)
      z (traceStep_active_subset E y o hz) hadj
    rw [AKLT.W.REC096.step_kept_iff, AKLT.W.REC096.step_kept_iff]
    tauto
  · simp [traceStep]
    split_ifs <;> simp
  · intro hu
    have hou : E.status o = .U := by
      simpa [AKLT.W.REC096.step_status_ne E y o o hyo.symm] using hu
    simpa [traceStep, hyo.symm] using
      congrArg (fun k : Finset Plane => k.erase y) (h.u_full o hoG hyo.symm ho hou)
  · intro hd x z hpx hpz
    have hod : E.status o = .D := by
      simpa [AKLT.W.REC096.step_status_ne E y o o hyo.symm] using hd
    have hc : ((traceStep E y o).kept o).card = 1 := by
      simp [traceStep, hyo.symm, Finset.card_erase_of_mem hp.2.2.2.2,
        h.d_two o hoG hyo.symm hod]
    exact (Finset.card_le_one.mp (Nat.le_of_eq hc)) x hpx.2.2.2.1 z hpz.2.2.2.1
  · simpa [AKLT.W.REC096.step_status_ne E y o e hye.symm] using h.fixedU

theorem removeSite_present {G : Finset Plane} (E : Network G) (e x z : Plane)
    (hx : x ≠ e) (hz : z ≠ e) :
    (removeSite E e).Present x z ↔ E.Present x z := by
  have hstat (t : Plane) (ht : t ≠ e) : (removeSite E e).status t = E.status t := by
    simp [removeSite, ht]
  have hact (t : Plane) (ht : t ≠ e) :
      t ∈ (removeSite E e).active ↔ t ∈ E.active := by
    simp only [Network.active, Finset.mem_filter, hstat t ht]
  unfold Network.Present
  rw [hact x hx, hact z hz]
  rfl

/-- Erase the fixed defect only in a comparison network. Its radius-two
neighborhood is excluded before transferring the extracted cover back. -/
theorem defect_remove {G : Finset Plane} {E : Network G} {y a e : Plane}
    (h : DefectInvariant E y a e) (hy : y ≠ e) (he : e ∈ G) :
    AKLT.W.REC096.PrefixInvariant (removeSite E e) y a := by
  have hact : (removeSite E e).active ⊆ E.active := by
    intro x hx
    have hxe : x ≠ e := by
      rintro rfl
      exact (Finset.mem_filter.mp hx).2 (by simp [removeSite])
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
      by simpa [removeSite, hxe] using (Finset.mem_filter.mp hx).2⟩
  refine ⟨?_, h.kept_sub, ?_, ?_, ?_, h.arrival_adj, ?_, ?_, ?_⟩
  · intro x hx
    have hxe : x ≠ e := fun hh => hx (hh ▸ he)
    simpa [removeSite, hxe] using h.outside x hx
  · intro x hx hxy hU
    have hxe : x ≠ e := by
      rintro rfl
      simp [removeSite] at hU
    exact h.u_full x hx hxy hxe (by simpa [removeSite, hxe] using hU)
  · intro x hx hxy hD
    have hxe : x ≠ e := by
      rintro rfl
      simp [removeSite] at hD
    exact h.d_two x hx hxy (by simpa [removeSite, hxe] using hD)
  · intro x hx z hz hadj
    exact h.agree x (hact hx) z (hact hz) hadj
  · by_cases ha : a = e
    · simp [removeSite, ha]
    · simpa [removeSite, ha] using h.arrival_notU
  · intro hU
    exact h.liveU (by simpa [removeSite, hy] using hU)
  · intro hD x z hpx hpz
    have hx : x ≠ e := by
      rintro rfl
      exact (Finset.mem_filter.mp hpx.2.1).2 (by simp [removeSite])
    have hz : z ≠ e := by
      rintro rfl
      exact (Finset.mem_filter.mp hpz.2.1).2 (by simp [removeSite])
    exact h.liveD (by simpa [removeSite, hy] using hD) x z
      ((removeSite_present E e y x hy hx).mp hpx)
      ((removeSite_present E e y z hy hz).mp hpz)

theorem defect_covered {G : Finset Plane} {E : Network G} {y e : Plane}
    {incoming outgoing : Compass} (h : DefectInvariant E y (y - incoming.step) e)
    (hyG : y ∈ G) (hyS : y ∉ protectedSites G) (he : e ∈ protectedSites G)
    (hU : E.status y = .U) (hp : E.Present y (y + outgoing.step))
    (hfar : 2 < latticeDist y e) :
    AKLT.Defs.CoveredDepartureV2 E y incoming outgoing := by
  have hye : y ≠ e := by rintro rfl; simp [latticeDist] at hfar
  have hchart (z : Plane) (hz : z ∈ templateSites) :
      y + normalizeRotation incoming z ≠ e := by
    intro hh
    have hd := AKLT.W.REC096.chart_dist y (0, 0) z incoming
    rw [AKLT.W.REC096.chart_zero, AKLT.W.REC096.chart_apply, hh] at hd
    have := AKLT.W.REC096.template_dist hz
    omega
  have ho : y + outgoing.step ≠ e := by
    intro hh
    have hd := compass_distance y outgoing
    rw [hh] at hd
    omega
  have hr := AKLT.W.REC096.invariant_covered
    (defect_remove h hye (Finset.mem_filter.mp he).1) hyG hyS
    (by simpa [removeSite, hye] using hU)
    ((removeSite_present E e y (y + outgoing.step) hye ho).mpr hp)
  obtain ⟨π, hπ, hout, hstatus, hbonds⟩ := hr
  refine ⟨π, hπ, hout, ?_, ?_⟩
  · intro z hz
    simpa [removeSite, hchart z (Finset.mem_sdiff.mp hz).1] using hstatus z hz
  · intro z hz t ht
    have hb := hbonds z hz t ht
    change (if t ∈ templateTips then _ else _) at hb ⊢
    rw [removeSite_present E e _ _ (hchart z (Finset.mem_sdiff.mp hz).1) (hchart t ht)] at hb
    exact hb

theorem terminal_defect_initial (p : PairData) (hu : p.u ∉ protectedSites p.G)
    (hv : p.v ∉ protectedSites p.G) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G) :
    DefectInvariant (terminalNetwork p w) p.v p.c (wordVertex p.u w n) := by
  classical
  obtain ⟨incoming, hi⟩ := adjacent_direction p.pair.2.2.2.2.2.1
  let ps : PairSetup := ⟨p, incoming, hi, hu⟩
  let F := traceNetwork p.normalized (wordVertices p.u w)
  let e := wordVertex p.u w n
  have hEnd : prefixNetwork p.normalized p.u w n = F := by
    unfold prefixNetwork
    rw [List.take_of_length_le (by simp [wordVertices])]
  have hI := (AKLT.W.REC096.prefix_invariant ps (insert p.v (protectedSites p.G))
    w hw n le_rfl).1
  change AKLT.W.REC096.PrefixInvariant (prefixNetwork p.normalized p.u w n) e _ at hI
  rw [hEnd] at hI
  have heU : F.status e = .U :=
    (stopped_status_protected p.normalized p.u (insert p.v (protectedSites p.G))
      w hw e he).trans (p.pair.1.1.2 e he).1
  have hve : p.v ≠ e := by rintro hh; exact hv (hh ▸ he)
  have hcX : F.status p.c = .X := trace_removed p.normalized p.c p.pair.2.2.2.2.1 _
  have hflag (x z : Plane) (hz : z ∈ F.active) :
      z ∈ (terminalNetwork p w).kept x ↔ z ∈ F.kept x := by
    have hzc : z ≠ p.c := by
      rintro rfl
      exact (Finset.mem_filter.mp hz).2 hcX
    change z ∈ (if x = p.v ∧ F.status p.v = .U then (F.kept x).erase p.c
      else F.kept x) ↔ _
    split_ifs <;> simp [hzc]
  refine ⟨hI.outside, ?_, ?_, ?_, ?_, p.pair.2.2.2.2.2.2.1, ?_, ?_, ?_, heU⟩
  · intro x z hz
    apply hI.kept_sub x
    change z ∈ (if x = p.v ∧ F.status p.v = .U then (F.kept x).erase p.c
      else F.kept x) at hz
    split_ifs at hz
    · exact Finset.mem_of_mem_erase hz
    · exact hz
  · intro x hx hxv hxe hxU
    simpa [terminalNetwork, normalizeStart, hxv] using hI.u_full x hx hxe hxU
  · intro x hx hxv hxD
    have hxe : x ≠ e := by
      rintro rfl
      have hbad : Status.U = .D := heU.symm.trans hxD
      cases hbad
    simpa [terminalNetwork, normalizeStart, hxv] using hI.d_two x hx hxe hxD
  · intro x hx z hz hadj
    rw [hflag x z hz, hflag z x hx]
    exact hI.agree x hx z hz hadj
  · rw [terminal_center_removed]
    decide
  · intro hvU
    change F.status p.v = .U at hvU
    have hvG := (Finset.mem_filter.mp p.pair.2.2.1).1
    change (if p.v = p.v ∧ F.status p.v = .U then (F.kept p.v).erase p.c
      else F.kept p.v) = _
    simp [hvU, hI.u_full p.v hvG hve hvU]
  · intro hvD x z hpx hpz
    have hstart := terminal_start_admissible p hv w hw
    rcases hstart.2.2 with hU | hD
    · have hbad : Status.D = .U := hvD.symm.trans hU.1
      cases hbad
    · exact (Finset.card_le_one.mp hD.2) x
        (AKLT.W.REC096.present_mem_neighbors hpx) z
        (AKLT.W.REC096.present_mem_neighbors hpz)

theorem terminal_defect_prefix (p : PairData) (hu : p.u ∉ protectedSites p.G)
    (hv : p.v ∉ protectedSites p.G) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G) {m : ℕ} (w' : DirectionWord m)
    (hw' : StoppedNetworkTrail (terminalNetwork p w) p.v (protectedSites p.G) w')
    (j : ℕ) (hj : j < m) :
    DefectInvariant (prefixNetwork (terminalNetwork p w) p.v w' j)
      (wordVertex p.v w' j) (if j = 0 then p.c else wordVertex p.v w' (j - 1))
      (wordVertex p.u w n) := by
  have hDyn := AKLT.W.REC039.main p.G (terminalNetwork p w)
    (terminal_auxiliary p hu w hw he) p.v (terminal_start_admissible p hv w hw)
    (protectedSites p.G) m w' hw'
  induction j with
  | zero =>
    simpa only [AKLT.W.REC096.prefix_zero, AKLT.W.REC096.word_vertex_zero,
      ↓reduceIte] using terminal_defect_initial p hu hv w hw he
  | succ j ih =>
    have hjm : j < m := by omega
    have hcur := (hDyn.2 ⟨j, hjm⟩).2
    have ho : wordVertex p.v w' (j + 1) ≠ wordVertex p.u w n := by
      intro hh
      exact (hw'.2.2.1 (j + 1) hj).2 (hh ▸ he)
    rw [AKLT.W.REC096.prefix_step _ _ _ j hjm]
    simpa using defect_step (ih hjm) (hw'.2.2.1 j hjm).2 he ho hcur

theorem terminal_exception_location : TerminalExceptionLocationStatementV2 := by
  intro p hv n w hw he
  dsimp only
  intro incoming hi m w' hw' i hU hbad
  let E := terminalNetwork p.toPairData w
  let y := wordVertex p.v w' i.val
  let e := wordVertex p.u w n
  have hInv := terminal_defect_prefix p.toPairData p.interior hv w hw he w' hw' i.val i.isLt
  have harr : (if i.val = 0 then p.c else wordVertex p.v w' (i.val - 1)) =
      y - (wordIncoming incoming w' i).step := by
    by_cases hz : i.val = 0
    · simp [hz, y, wordIncoming, hi]
    · have hj : i.val - 1 < m := by omega
      have hsucc : i.val - 1 + 1 = i.val := by omega
      have hstep := AKLT.W.REC096.word_vertex_succ p.v w' (i.val - 1) hj
      rw [hsucc] at hstep
      simp only [hz, ↓reduceIte, wordIncoming, ↓reduceDIte]
      change wordVertex p.v w' (i.val - 1) = wordVertex p.v w' i.val - _
      rw [hstep]
      simp
  rw [harr] at hInv
  have hyS : y ∉ protectedSites p.G := (hw'.2.2.1 i.val i.isLt).2
  have hye : y ≠ e := fun hh => hyS (hh ▸ he)
  have hd0 : latticeDist y e ≠ 0 := by
    intro hh
    apply hye
    have hx : y.1 = e.1 := by unfold latticeDist at hh; omega
    have hz : y.2 = e.2 := by unfold latticeDist at hh; omega
    exact Prod.ext hx hz
  refine ⟨Nat.pos_of_ne_zero hd0, le_of_not_gt ?_⟩
  intro hfar
  have hp := (AKLT.W.REC039.main p.G E (terminal_auxiliary p.toPairData p.interior w hw he)
    p.v (terminal_start_admissible p.toPairData hv w hw) (protectedSites p.G) m w' hw').2 i
  apply hbad
  apply defect_covered hInv (Finset.mem_filter.mp hp.1.1).1 hyS he hU
  · simpa [E, y, AKLT.W.REC096.word_vertex_succ p.v w' i.val i.isLt] using hp.2
  · exact hfar

theorem uncoveredCountV2_le_twelve_of_location {G : Finset Plane} (D : Network G)
    (u e : Plane) (incoming : Compass) {n : ℕ} (w : DirectionWord n)
    (hloc : ∀ i : Fin n,
      (prefixNetwork D u w i.val).status (wordVertex u w i.val) = .U →
      ¬ AKLT.Defs.CoveredDepartureV2 (prefixNetwork D u w i.val) (wordVertex u w i.val)
        (wordIncoming incoming w i) (w i) →
      0 < latticeDist (wordVertex u w i.val) e ∧
        latticeDist (wordVertex u w i.val) e ≤ 2) :
    uncoveredCountV2 D u incoming w ≤ 12 := by
  classical
  rw [← diamond_twelve e]
  apply Finset.card_le_card_of_injOn (fun i : Fin n => wordVertex u w i.val)
  · intro i hi
    obtain ⟨hiU, hiBad⟩ := (Finset.mem_filter.mp hi).2
    have hd := hloc i hiU hiBad
    refine Finset.mem_filter.mpr ⟨?_, hd⟩
    norm_num [square]
    unfold latticeDist at hd
    omega
  · intro i hi j hj heq
    exact u_departure_injective D u w i j (Finset.mem_filter.mp hi).2.1
      (Finset.mem_filter.mp hj).2.1 heq

theorem terminal_exception_count : TerminalExceptionCountStatementV2 := by
  intro p hv n w hw he
  dsimp only
  intro incoming hi m w' hw'
  exact uncoveredCountV2_le_twelve_of_location _ p.v (wordVertex p.u w n) incoming w'
    (terminal_exception_location p hv n w hw he incoming hi m w' hw')

end AKLT.W.REC080
