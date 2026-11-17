module
public import AKLT.W.REC096.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec
open AKLT.W.REC096

namespace AKLT.W.REC099

/-- Removing a site preserves exactly the bonds whose endpoints differ from it. -/
private theorem present_removeSite_iff {G : Finset Plane} (E : Network G) (e x z : Plane) :
    (removeSite E e).Present x z ↔ E.Present x z ∧ x ≠ e ∧ z ≠ e := by
  classical
  by_cases hx : x = e <;> by_cases hz : z = e <;>
    simp [Network.Present, Network.active, removeSite, hx, hz, Function.update_apply]

private theorem removeSite_traceStep {G : Finset Plane} (E : Network G) (e y o : Plane) :
    removeSite (traceStep E y o) e = traceStep (removeSite E e) y o := by
  classical
  apply congrArg (fun s : Plane → Status => Network.mk s (traceStep E y o).kept)
  funext x
  by_cases hxe : x = e <;> by_cases hxy : x = y <;>
    by_cases hye : y = e <;> simp_all [removeSite, traceStep]

private theorem removeSite_traceNetwork {G : Finset Plane} (E : Network G) (e : Plane)
    (xs : List Plane) :
    removeSite (traceNetwork E xs) e = traceNetwork (removeSite E e) xs := by
  induction xs generalizing E with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons z xs =>
      change removeSite (traceNetwork (traceStep E x z) (z :: xs)) e = _
      rw [ih, removeSite_traceStep]
      rfl

private theorem prefix_removeSite {G : Finset Plane} {n : ℕ} (E : Network G) (e u : Plane)
    (w : DirectionWord n) (j : ℕ) :
    prefixNetwork (removeSite E e) u w j = removeSite (prefixNetwork E u w j) e :=
  (removeSite_traceNetwork E e _).symm

private theorem step_present_subset {G : Finset Plane} (E : Network G) (y o : Plane)
    {x z : Plane} (h : (traceStep E y o).Present x z) : E.Present x z :=
  ⟨step_active_subset E y o h.1, step_active_subset E y o h.2.1, h.2.2.1,
    ((step_kept_iff E y o x z).mp h.2.2.2.1).1,
    ((step_kept_iff E y o z x).mp h.2.2.2.2).1⟩

private theorem trace_present_subset {G : Finset Plane} (E : Network G) (xs : List Plane)
    {x z : Plane} (h : (traceNetwork E xs).Present x z) : E.Present x z := by
  induction xs generalizing E with
  | nil => exact h
  | cons a xs ih =>
    cases xs with
    | nil => exact h
    | cons b xs => exact step_present_subset E a b (ih (traceStep E a b) h)

private theorem normalize_present_subset {G : Finset Plane} (E : Network G) (u c : Plane)
    {x z : Plane} (h : (normalizeStart E u c).Present x z) : E.Present x z := by
  have hk (t : Plane) : (normalizeStart E u c).kept t ⊆ E.kept t := by
    simp only [normalizeStart]
    split_ifs
    · exact Finset.erase_subset _ _
    · exact Finset.Subset.refl _
  exact ⟨h.1, h.2.1, h.2.2.1, hk x h.2.2.2.1, hk z h.2.2.2.2⟩

private theorem trace_status_X {G : Finset Plane} (E : Network G) (xs : List Plane)
    {x : Plane} (h : E.status x = .X) : (traceNetwork E xs).status x = .X := by
  induction xs generalizing E with
  | nil => exact h
  | cons a xs ih =>
    cases xs with
    | nil => exact h
    | cons b xs =>
      apply ih (traceStep E a b)
      by_cases hx : x = a
      · subst x
        simp [traceStep, h]
      · simpa [traceStep, hx] using h

private theorem trace_status_untouched {G : Finset Plane} (E : Network G) (xs : List Plane)
    {x : Plane} (h : x ∉ xs) : (traceNetwork E xs).status x = E.status x := by
  induction xs generalizing E with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      have hxa : x ≠ a := by intro he; exact h (by simp [he])
      have htail : x ∉ b :: xs := by intro hm; exact h (by simp [hm])
      change (traceNetwork (traceStep E a b) (b :: xs)).status x = _
      rw [ih (traceStep E a b) htail, step_status_ne E a b x hxa]

/-- Once the fixed terminal defect is removed, normalization at a fresh start
restores precisely the invariant needed for the ordinary local template proof. -/
private theorem restart_invariant {G : Finset Plane} {F : Network G} {e a v c : Plane}
    (h : PrefixInvariant F e a) (hv : v ≠ e) (hc : F.status c = .X)
    (hadj : Adjacent v c)
    (hD : F.status v = .D → ∀ x z, F.Present v x → F.Present v z → x = z) :
    PrefixInvariant (removeSite (normalizeStart F v c) e) v c := by
  classical
  let E := removeSite (normalizeStart F v c) e
  have hs (x : Plane) (hx : x ≠ e) : E.status x = F.status x := by
    simp [E, removeSite, normalizeStart, hx]
  have hk (x z : Plane) (hz : z ≠ c) : z ∈ E.kept x ↔ z ∈ F.kept x := by
    simp only [E, removeSite, normalizeStart]
    split_ifs <;> simp [hz]
  have hactive {x : Plane} (hx : x ∈ E.active) : x ∈ F.active := by
    have hx' := Finset.mem_filter.mp hx
    have hxe : x ≠ e := by
      intro he
      subst x
      simpa [E, removeSite] using hx'.2
    exact Finset.mem_filter.mpr ⟨hx'.1, by simpa [hs x hxe] using hx'.2⟩
  have hne {x : Plane} (hx : E.status x ≠ .X) : x ≠ e := by
    intro he
    subst x
    exact hx (by simp [E, removeSite])
  refine ⟨?_, ?_, ?_, ?_, ?_, hadj, ?_, ?_, ?_⟩
  · intro x hx
    by_cases he : x = e
    · simp [removeSite, he]
    · rw [hs x he]
      exact h.outside x hx
  · intro x
    change (normalizeStart F v c).kept x ⊆ _
    simp only [normalizeStart]
    split_ifs
    · exact (Finset.erase_subset _ _).trans (h.kept_sub x)
    · exact h.kept_sub x
  · intro x hx hxv hU
    have hxe := hne (by rw [hU]; decide)
    rw [hs x hxe] at hU
    simpa [E, removeSite, normalizeStart, hxv] using h.u_full x hx hxe hU
  · intro x hx hxv hd
    have hxe := hne (by rw [hd]; decide)
    rw [hs x hxe] at hd
    simpa [E, removeSite, normalizeStart, hxv] using h.d_two x hx hxe hd
  · intro x hx z hz hadj'
    have hxc : x ≠ c := by
      intro he
      subst x
      exact (Finset.mem_filter.mp (hactive hx)).2 hc
    have hzc : z ≠ c := by
      intro he
      subst z
      exact (Finset.mem_filter.mp (hactive hz)).2 hc
    rw [hk x z hzc, hk z x hxc]
    exact h.agree x (hactive hx) z (hactive hz) hadj'
  · by_cases hce : c = e
    · simp [removeSite, hce]
    · rw [hs c hce, hc]; decide
  · intro hu
    rw [hs v hv] at hu
    have hvG : v ∈ G := by
      by_contra hout
      have := h.outside v hout
      rw [hu] at this
      cases this
    simpa [E, removeSite, normalizeStart, hu] using
      congrArg (fun s : Finset Plane => s.erase c) (h.u_full v hvG hv hu)
  · intro hd x z hpx hpz
    rw [hs v hv] at hd
    exact hD hd x z
      (normalize_present_subset F v c ((present_removeSite_iff _ _ _ _).mp hpx).1)
      (normalize_present_subset F v c ((present_removeSite_iff _ _ _ _).mp hpz).1)


/-- The first trace leaves an ordinary invariant after its terminal site is
removed and its untouched second endpoint is normalized. -/
private theorem second_initial_invariant (p : PairSetup) (hv : p.v ∉ protectedSites p.G)
    {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G) :
    PrefixInvariant
      (removeSite (normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
        (wordVertex p.u w n)) p.v p.c := by
  classical
  let F := traceNetwork p.normalized (wordVertices p.u w)
  let e := wordVertex p.u w n
  have hF : PrefixInvariant F e (arrivalSite p w n) := by
    have htake : (wordVertices p.u w).take (n + 1) = wordVertices p.u w :=
      List.take_of_length_le (by simp [wordVertices])
    simpa only [prefixNetwork, htake] using
      (prefix_invariant p (insert p.v (protectedSites p.G)) w hw n le_rfl).1
  rcases p.pair with ⟨hcon, hu, hvActive, hcG, hcX, hadju, hadjv, hgeom, huc, hvc⟩
  have hve : p.v ≠ e := by
    intro hve
    exact hv (hve ▸ he)
  have hc : F.status p.c = .X := trace_status_X p.normalized _ hcX
  apply restart_invariant hF hve hc hadjv
  have hnot : p.v ∉ wordVertices p.u w := by
    intro hm
    obtain ⟨j, hj, hjv⟩ := List.mem_map.mp hm
    have hjle : j ≤ n := by simpa using hj
    by_cases hjn : j < n
    · exact (hw.2.2.1 j hjn).1 (by simp [hjv])
    · have hjn : j = n := by omega
      subst j
      exact hv (hjv ▸ he)
  intro hd x z hpx hpz
  have hdOrig : p.D.status p.v = .D := by
    change (traceNetwork p.normalized (wordVertices p.u w)).status p.v = .D at hd
    rw [trace_status_untouched p.normalized _ hnot] at hd
    exact hd
  have hdeg : (p.D.presentNeighbours p.v).card ≤ 1 := by
    rcases hvc with hU | ⟨_, hdeg⟩
    · rw [hdOrig] at hU
      cases hU
    · exact hdeg
  apply Finset.card_le_one.mp hdeg
  · exact present_mem_neighbours
      (normalize_present_subset p.D p.u p.c (trace_present_subset p.normalized _ hpx))
  · exact present_mem_neighbours
      (normalize_present_subset p.D p.u p.c (trace_present_subset p.normalized _ hpz))

/-- Only the bonds through the requested departure are needed by the prefix
induction; a later terminal bond may meet the removed defect. -/
private theorem prefix_invariant_to {G : Finset Plane} {n : ℕ} (E : Network G) (u c : Plane)
    (w : DirectionWord n) (q : Fin n) (hinit : PrefixInvariant E u c)
    (hinj : Function.Injective (wordBond u w))
    (hS : ∀ j < n, wordVertex u w j ∉ protectedSites G)
    (hpres : ∀ k : Fin n, k.val ≤ q.val →
      E.Present (wordVertex u w k.val) (wordVertex u w (k.val + 1)))
    (j : ℕ) (hj : j ≤ q.val) :
    PrefixInvariant (prefixNetwork E u w j) (wordVertex u w j)
      (if j = 0 then c else wordVertex u w (j - 1)) ∧
    (∀ k : Fin n, j ≤ k.val → k.val ≤ q.val →
      (prefixNetwork E u w j).Present (wordVertex u w k.val) (wordVertex u w (k.val + 1))) := by
  induction j with
  | zero =>
    simp only [prefix_zero, word_vertex_zero, ↓reduceIte]
    exact ⟨hinit, fun k _ hk => hpres k hk⟩
  | succ j ih =>
    have hjn : j < n := by omega
    obtain ⟨hinv, hfuture⟩ := ih (by omega)
    have hp := hfuture ⟨j, hjn⟩ le_rfl (show j ≤ q.val by omega)
    rw [prefix_step _ _ _ j hjn]
    constructor
    · simpa using invariant_step hinv (hS j hjn) hp
    · intro k hk hkq
      apply step_preserves_unused hinv hp (hfuture k (by omega) hkq)
      intro heq
      have hkj : k = ⟨j, hjn⟩ := hinj heq
      have : k.val = j := congrArg Fin.val hkj
      omega

private theorem word_arrival_eq {n : ℕ} (u c : Plane) (incoming : Compass)
    (hu : u = c + incoming.step) (w : DirectionWord n) (i : Fin n) :
    (if i.val = 0 then c else wordVertex u w (i.val - 1)) =
      wordVertex u w i.val - (wordIncoming incoming w i).step := by
  by_cases hi : i.val = 0
  · simp [hi, wordIncoming, word_vertex_zero, hu]
  · have hpred : i.val - 1 < n := by omega
    have hsucc : i.val - 1 + 1 = i.val := by omega
    have hv := word_vertex_succ u w (i.val - 1) hpred
    rw [hsucc] at hv
    simp only [hi, ↓reduceIte, wordIncoming, ↓reduceDIte, hv]
    simp

/-- A radius-two template cannot see a removed site farther than two away. -/
private theorem covered_of_removeSite {G : Finset Plane} (E : Network G) (e y : Plane)
    (a out : Compass) (hfar : 2 < latticeDist y e)
    (hcov : AKLT.Defs.CoveredDepartureV2 (removeSite E e) y a out) :
    AKLT.Defs.CoveredDepartureV2 E y a out := by
  classical
  have hne (z : Plane) (hz : z ∈ templateSites) : y + normalizeRotation a z ≠ e := by
    intro heq
    have hd := chart_dist y (0, 0) z a
    rw [chart_zero, chart_apply, heq] at hd
    have := template_dist hz
    omega
  obtain ⟨π, hπ, hout, hstatus, hbonds⟩ := hcov
  refine ⟨π, hπ, hout, ?_, ?_⟩
  · intro z hz
    have hn := hne z (Finset.mem_sdiff.mp hz).1
    simpa only [removeSite, Function.update_of_ne hn] using hstatus z hz
  · intro z hz t ht
    have hzn := hne z (Finset.mem_sdiff.mp hz).1
    have htn := hne t ht
    have hp : (removeSite E e).Present (y + normalizeRotation a z) (y + normalizeRotation a t) ↔
        E.Present (y + normalizeRotation a z) (y + normalizeRotation a t) := by
      constructor
      · intro hp
        exact ((present_removeSite_iff E e _ _).mp hp).1
      · intro hp
        exact (present_removeSite_iff E e _ _).mpr ⟨hp, hzn, htn⟩
    simpa only [hp] using hbonds z hz t ht

/-- Every second-trail U departure outside the terminal diamond has a shared
covered pattern. The fixed defect is removed only in this auxiliary proof. -/
theorem terminalLocalCover :
    ∀ p : PairSetup, p.v ∉ protectedSites p.G → ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w →
      wordVertex p.u w n ∈ protectedSites p.G →
      let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
      ∀ incoming : Compass, p.v = p.c + incoming.step → ∀ m : ℕ, ∀ w' : DirectionWord m,
        StoppedNetworkTrail E p.v (protectedSites p.G) w' → ∀ i : Fin m,
        (prefixNetwork E p.v w' i.val).status (wordVertex p.v w' i.val) = .U →
        2 < latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) →
        AKLT.Defs.CoveredDepartureV2 (prefixNetwork E p.v w' i.val)
          (wordVertex p.v w' i.val) (wordIncoming incoming w' i) (w' i) := by
  intro p hv n w hw he
  dsimp
  intro incoming hincoming m w' hw' i hU hfar
  let E := normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c
  let e := wordVertex p.u w n
  let R := removeSite E e
  change 2 < latticeDist (wordVertex p.v w' i.val) e at hfar
  have hinit : PrefixInvariant R p.v p.c := second_initial_invariant p hv w hw he
  have hstart (j : ℕ) (hj : j < m) : wordVertex p.v w' j ≠ e := by
    intro heq
    exact (hw'.2.2.1 j hj).2 (heq ▸ he)
  have hend : wordVertex p.v w' (i.val + 1) ≠ e := by
    intro heq
    have hd := step_adjacent (wordVertex p.v w' i.val) (w' i)
    rw [← word_vertex_succ p.v w' i.val i.isLt] at hd
    rw [heq] at hd
    change latticeDist (wordVertex p.v w' i.val) e = 1 at hd
    omega
  have hpres (k : Fin m) (hk : k.val ≤ i.val) :
      R.Present (wordVertex p.v w' k.val) (wordVertex p.v w' (k.val + 1)) := by
    apply (present_removeSite_iff E e _ _).mpr
    refine ⟨hw'.2.1 k, hstart k.val k.isLt, ?_⟩
    by_cases hki : k.val = i.val
    · simpa only [hki] using hend
    · exact hstart (k.val + 1) (by omega)
  obtain ⟨hinv, hfuture⟩ := prefix_invariant_to R p.v p.c w' i hinit hw'.1
    (fun j hj => (hw'.2.2.1 j hj).2) hpres i.val le_rfl
  rw [word_arrival_eq p.v p.c incoming hincoming w' i] at hinv
  have hp := hfuture i le_rfl le_rfl
  have hyG := (Finset.mem_filter.mp hp.1).1
  rw [word_vertex_succ p.v w' i.val i.isLt] at hp
  have hUR : (prefixNetwork R p.v w' i.val).status (wordVertex p.v w' i.val) = .U := by
    rw [prefix_removeSite]
    simpa [removeSite, hstart i.val i.isLt] using hU
  have hcov := invariant_covered hinv hyG (hw'.2.2.1 i.val i.isLt).2 hUR hp
  rw [prefix_removeSite] at hcov
  exact covered_of_removeSite (prefixNetwork E p.v w' i.val) e _ _ _ hfar hcov

end AKLT.W.REC099

#print axioms AKLT.W.REC099.terminalLocalCover
