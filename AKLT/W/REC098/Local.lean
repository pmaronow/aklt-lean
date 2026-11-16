import AKLT.W.REC098.Trace

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC098

def rotateDir : Compass → Compass → Compass
  | .north, d => d
  | .east, .east => .south
  | .east, .north => .east
  | .east, .west => .north
  | .east, .south => .west
  | .south, d => d.reverse
  | .west, .east => .north
  | .west, .north => .west
  | .west, .west => .south
  | .west, .south => .east

def chart (y : Plane) (a : Compass) (z : Plane) : Plane := y + normalizeRotation a z

theorem chart_injective (y : Plane) (a : Compass) : Function.Injective (chart y a) := by
  intro z t h
  have hh := add_left_cancel h
  cases a <;> simp only [normalizeRotation, Prod.mk.injEq] at hh
  all_goals ext <;> simp_all

theorem rotateDir_surjective (a : Compass) : Function.Surjective (rotateDir a) := by
  intro b
  cases a <;> cases b <;>
    first | exact ⟨.east, rfl⟩ | exact ⟨.north, rfl⟩ | exact ⟨.west, rfl⟩ | exact ⟨.south, rfl⟩

theorem chart_zero (y : Plane) (a : Compass) : chart y a (0, 0) = y := by
  cases a <;> simp [chart, normalizeRotation]

theorem chart_add_step (y z : Plane) (a d : Compass) :
    chart y a (z + d.step) = chart y a z + (rotateDir a d).step := by
  cases a <;> cases d <;> ext <;> simp [chart, normalizeRotation, rotateDir, Compass.step, Compass.reverse] <;> omega

theorem chart_south (y : Plane) (a : Compass) : chart y a (0, -1) = y - a.step := by
  cases a <;> ext <;> simp [chart, normalizeRotation, Compass.step] <;> omega

theorem chart_mem_neighbours (y z t : Plane) (a : Compass) :
    chart y a t ∈ neighbours (chart y a z) ↔ t ∈ neighbours z := by
  constructor
  · rintro ht
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp ht
    obtain ⟨e, he⟩ := rotateDir_surjective a d
    rw [← he, ← chart_add_step] at hd
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, chart_injective y a hd⟩
  · rintro ht
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp ht
    rw [chart_add_step]
    exact Finset.mem_image.mpr ⟨rotateDir a d, Finset.mem_univ _, rfl⟩

theorem chart_adjacent (y z t : Plane) (a : Compass) :
    Adjacent (chart y a z) (chart y a t) ↔ Adjacent z t := by
  rw [adjacent_iff, adjacent_iff, chart_mem_neighbours]

theorem chart_dist (y z t : Plane) (a : Compass) :
    latticeDist (chart y a z) (chart y a t) = latticeDist z t := by
  cases a <;> simp only [chart, normalizeRotation, latticeDist, Prod.fst_add, Prod.snd_add]
  all_goals omega

theorem templateSites_explicit : templateSites =
    {(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1),
      (1, 1), (-1, 1), (-1, -1), (1, -1), (2, 0), (0, 2), (-2, 0), (0, -2)} := by
  decide +kernel

theorem chart_ball (y : Plane) (a : Compass) {z : Plane} (hz : z ∈ templateSites) :
    latticeDist y (chart y a z) ≤ 2 := by
  have hdist := chart_dist y (0, 0) z a
  rw [chart_zero] at hdist
  rw [hdist]
  rw [templateSites_explicit] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem internalBonds_mem {G : Finset Plane} {x z : Plane} :
    (x, z) ∈ internalBonds G ↔ x ∈ G ∧ z ∈ G ∧ z ∈ positiveNeighbours x := by
  simp [internalBonds, and_assoc, and_left_comm]

theorem positive_either (x z : Plane) :
    z ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours z ↔ Adjacent x z := by
  rcases x with ⟨x₁, x₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    Adjacent, latticeDist]
  omega

theorem internalPresent_iff (π : PatternData) (z t : Plane) :
    π.InternalPresent z t ↔ z ∈ templateSites ∧ t ∈ templateSites ∧ Adjacent z t ∧
      π.statusAt z ≠ .X ∧ π.statusAt t ≠ .X ∧
      (z ∈ templateTips ∨ t ∈ π.keptAt z) ∧ (t ∈ templateTips ∨ z ∈ π.keptAt t) := by
  simp only [PatternData.InternalPresent, PatternData.bonds, Finset.mem_filter, internalBonds_mem]
  have hp := positive_either z t
  tauto

/-- Actual kept directions in coordinates of the template. -/
def localFlags {G : Finset Plane} (D : Network G) (y : Plane) (a : Compass)
    (z : Plane) : Finset Compass :=
  Finset.univ.filter fun d => chart y a (z + d.step) ∈ D.kept (chart y a z)

theorem localFlags_match {G : Finset Plane} (D : Network G) (y : Plane) (a : Compass)
    (z t : Plane) (hsub : D.kept (chart y a z) ⊆ neighbours (chart y a z)) :
    t ∈ (localFlags D y a z).image (fun d => z + d.step) ↔
      chart y a t ∈ D.kept (chart y a z) := by
  constructor
  · rintro ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hd).2
  · intro ht
    have hn := (chart_mem_neighbours y z t a).mp (hsub ht)
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa [hd] using ht⟩, hd⟩

theorem localFlags_image {G : Finset Plane} (D : Network G) (y : Plane) (a : Compass)
    (z : Plane) (hsub : D.kept (chart y a z) ⊆ neighbours (chart y a z)) :
    (localFlags D y a z).image (fun d => chart y a (z + d.step)) = D.kept (chart y a z) := by
  ext t
  constructor
  · rintro ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hd).2
  · intro ht
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp (hsub ht)
    obtain ⟨e, he⟩ := rotateDir_surjective a d
    have hchart : chart y a (z + e.step) = t := by rw [chart_add_step, he, hd]
    exact Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hchart ▸ ht⟩, hchart⟩

theorem localFlags_card {G : Finset Plane} (D : Network G) (y : Plane) (a : Compass)
    (z : Plane) (hsub : D.kept (chart y a z) ⊆ neighbours (chart y a z)) :
    ((localFlags D y a z).image (fun d => z + d.step)).card = (D.kept (chart y a z)).card := by
  have hi : Function.Injective (fun d : Compass => z + d.step) :=
    fun _ _ h => step_injective (add_left_cancel h)
  rw [Finset.card_image_of_injective _ hi, ← localFlags_image D y a z hsub]
  exact (Finset.card_image_of_injective _ (fun _ _ h => hi (chart_injective y a h))).symm

def localPattern {G : Finset Plane} (D : Network G) (y : Plane) (a out : Compass) : PatternData where
  outgoing := out
  status := fun z => if z.val ∈ templateTips then .U else D.status (chart y a z.val)
  kept := fun z => if z.val = (0, 0) then {.east, .north, .west}
    else if D.status (chart y a z.val) = .U then Finset.univ else localFlags D y a z.val

theorem localPattern_status {G : Finset Plane} (D : Network G) (y : Plane)
    (a out : Compass) {z : Plane} (hz : z ∈ templateSites \ templateTips) :
    (localPattern D y a out).statusAt z = D.status (chart y a z) := by
  simp [PatternData.statusAt, localPattern, (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2]

theorem localPattern_tip {G : Finset Plane} (D : Network G) (y : Plane)
    (a out : Compass) {z : Plane} (hz : z ∈ templateTips) :
    (localPattern D y a out).statusAt z = .U := by
  have hzS : z ∈ templateSites := (by decide +kernel : templateTips ⊆ templateSites) hz
  simp [PatternData.statusAt, localPattern, hzS, hz]

theorem localPattern_center_kept {G : Finset Plane} (D : Network G) (y : Plane)
    (a out : Compass) :
    (localPattern D y a out).keptAt (0, 0) = {(1, 0), (0, 1), (-1, 0)} := by
  simp [PatternData.keptAt, localPattern, (by decide +kernel : (0, 0) ∈ templateSites), Compass.step]

theorem localPattern_kept_U {G : Finset Plane} (D : Network G) (y : Plane)
    (a out : Compass) {z : Plane} (hz : z ∈ templateSites) (hne : z ≠ (0, 0))
    (hU : D.status (chart y a z) = .U) :
    (localPattern D y a out).keptAt z = neighbours z := by
  simp [PatternData.keptAt, localPattern, hz, hne, hU, neighbours]

theorem localPattern_kept_notU {G : Finset Plane} (D : Network G) (y : Plane)
    (a out : Compass) {z : Plane} (hz : z ∈ templateSites) (hne : z ≠ (0, 0))
    (hU : D.status (chart y a z) ≠ .U) :
    (localPattern D y a out).keptAt z =
      (localFlags D y a z).image (fun d => z + d.step) := by
  simp [PatternData.keptAt, localPattern, hz, hne, hU]

theorem localPattern_kept_match {G : Finset Plane} {D : Network G} {y : Plane}
    {a out : Compass} {bad : Finset Plane}
    (hs : TraceState D bad y (y - a.step)) (hU : D.status y = .U)
    (hG : ∀ t ∈ templateSites, chart y a t ∈ G)
    (hb : ∀ z ∈ templateSites, chart y a z ∉ bad)
    {z t : Plane} (hz : z ∈ templateSites \ templateTips) (ht : t ∈ templateSites) :
    t ∈ (localPattern D y a out).keptAt z ↔ chart y a t ∈ D.kept (chart y a z) := by
  have hzS := (Finset.mem_sdiff.mp hz).1
  have hsub : D.kept (chart y a z) ⊆ neighbours (chart y a z) :=
    fun _ hx => (Finset.mem_inter.mp (hs.subset _ hx)).1
  by_cases hz0 : z = (0, 0)
  · subst z
    rw [localPattern_center_kept, chart_zero, hs.liveU hU, ← chart_south]
    have heq : ({(1, 0), (0, 1), (-1, 0)} : Finset Plane) =
        (neighbours (0, 0)).erase (0, -1) := by decide +kernel
    rw [heq]
    simp only [Finset.mem_erase, Finset.mem_inter]
    rw [(chart_injective y a).ne_iff, show chart y a t ∈ neighbours y ↔ t ∈ neighbours (0, 0) from
      by simpa [chart_zero] using chart_mem_neighbours y (0, 0) t a]
    simp [hG t ht]
  · have hzy : chart y a z ≠ y := by
      intro heq
      exact hz0 (chart_injective y a (heq.trans (chart_zero y a).symm))
    by_cases hUz : D.status (chart y a z) = .U
    · rw [localPattern_kept_U D y a out hzS hz0 hUz, hs.fullU _ hzy (hb z hzS) hUz]
      simp [hG t ht, chart_mem_neighbours]
    · rw [localPattern_kept_notU D y a out hzS hz0 hUz]
      exact localFlags_match D y a z t hsub

theorem localPattern_D_card {G : Finset Plane} {D : Network G} {y : Plane}
    {a out : Compass} {bad : Finset Plane}
    (hs : TraceState D bad y (y - a.step)) {z : Plane}
    (hz : z ∈ templateSites) (hz0 : z ≠ (0, 0)) (hD : D.status (chart y a z) = .D) :
    ((localPattern D y a out).keptAt z).card = 2 := by
  rw [localPattern_kept_notU D y a out hz hz0 (by simp [hD])]
  rw [localFlags_card D y a z (fun _ hx => (Finset.mem_inter.mp (hs.subset _ hx)).1)]
  apply hs.twoD _ ?_ hD
  intro heq
  exact hz0 (chart_injective y a (heq.trans (chart_zero y a).symm))

theorem normalizeRotation_step (a d : Compass) :
    normalizeRotation a d.step = (rotateDir a d).step := by
  cases a <;> cases d <;> rfl

/-- Extract a shared-matcher cover whenever no fixed defect meets the template. -/
theorem state_covered {G : Finset Plane} {D : Network G} {y : Plane}
    {a outgoing : Compass} {bad : Finset Plane}
    (hs : TraceState D bad y (y - a.step)) (hyS : y ∉ protectedSites G)
    (hU : D.status y = .U) (hpres : D.Present y (y + outgoing.step))
    (hb : ∀ z ∈ templateSites, chart y a z ∉ bad) :
    AKLT.Defs.CoveredDepartureV2 D y a outgoing := by
  obtain ⟨out, hout⟩ := rotateDir_surjective a outgoing
  have hrot : normalizeRotation a out.step = outgoing.step := by rw [normalizeRotation_step, hout]
  have houtchart : chart y a out.step = y + outgoing.step := by simp [chart, hrot]
  have hG : ∀ t ∈ templateSites, chart y a t ∈ G := by
    intro t ht
    exact interior_ball (Finset.mem_filter.mp hpres.1).1 hyS (chart_ball y a ht)
  have hcenter : (0, 0) ∈ templateSites \ templateTips := by decide +kernel
  have hside : ∀ d : Compass, d.step ∈ templateSites \ templateTips := by
    intro d; cases d <;> decide +kernel
  have hstep0 : ∀ d : Compass, d.step ≠ (0, 0) := by intro d; cases d <;> decide +kernel
  have hcorners : ∀ z ∈ templateCorners, z ∈ templateSites \ templateTips ∧ z ≠ (0, 0) := by
    decide +kernel
  have houtS : out ≠ .south := by
    intro ho
    have hk : chart y a out.step ∈ D.kept y := by rw [houtchart]; exact hpres.2.2.2.1
    rw [ho] at hk
    have ha : y - a.step ∉ D.kept y := by rw [hs.liveU hU]; simp
    exact ha (by simpa [Compass.step, chart_south] using hk)
  let π := localPattern D y a out
  have hstat : ∀ z ∈ templateSites \ templateTips, π.statusAt z = D.status (chart y a z) :=
    fun _ hz => localPattern_status D y a out hz
  have hm : ∀ z ∈ templateSites \ templateTips, ∀ t ∈ templateSites,
      t ∈ π.keptAt z ↔ chart y a t ∈ D.kept (chart y a z) := by
    intro z hz t ht
    exact localPattern_kept_match hs hU hG hb hz ht
  have hπ : π.Covered := by
    refine ⟨houtS, ?_, localPattern_center_kept D y a out, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstat _ hcenter, chart_zero]
      exact hU
    · have hz : (0, -1) ∈ templateSites \ templateTips := hside .south
      have hzS := (Finset.mem_sdiff.mp hz).1
      rw [hstat (0, -1) hz, chart_south]
      rcases hs.arrival with hX | ⟨hD, _, hkeep⟩
      · exact Or.inl hX
      · refine Or.inr ⟨hD, ?_, ?_⟩
        · exact localPattern_D_card hs hzS (hstep0 .south) (by simpa [chart_south, Compass.step] using hD)
        · intro h
          have hh := (hm _ hz _ (Finset.mem_sdiff.mp hcenter).1).mp h
          exact hkeep (by simpa [chart_zero, chart_south, Compass.step] using hh)
    · intro d hd
      have hz := hside d
      have hzS := (Finset.mem_sdiff.mp hz).1
      rw [hstat _ hz]
      cases hsD : D.status (chart y a d.step) with
      | U => exact Or.inl rfl
      | X => exact Or.inr (Or.inl rfl)
      | D =>
        refine Or.inr (Or.inr ⟨rfl, localPattern_D_card hs hzS (hstep0 d) hsD, ?_⟩)
        apply (hm _ hz _ (Finset.mem_sdiff.mp hcenter).1).mpr
        have hk : d.step ∈ π.keptAt (0, 0) := by
          rw [localPattern_center_kept]
          cases d <;> simp_all [Compass.step]
        have hk' : chart y a d.step ∈ D.kept y := by
          simpa [chart_zero] using (hm _ hcenter _ hzS).mp hk
        have hact : chart y a d.step ∈ D.active :=
          Finset.mem_filter.mpr ⟨hG _ hzS, by simp [hsD]⟩
        have hadj : Adjacent y (chart y a d.step) := by
          have hh : Adjacent (0, 0) d.step := by cases d <;> decide +kernel
          simpa [chart_zero] using (chart_adjacent y (0, 0) d.step a).mpr hh
        simpa [chart_zero] using (hs.mutualKept y hpres.1 _ hact hadj).mp hk'
    · change π.statusAt out.step ≠ .X
      rw [hstat _ (hside out), houtchart]
      exact (Finset.mem_filter.mp hpres.2.1).2
    · intro z hz
      obtain ⟨hz', hz0⟩ := hcorners z hz
      rw [hstat _ hz']
      cases hsD : D.status (chart y a z) with
      | U => exact Or.inl rfl
      | X => exact Or.inr (Or.inl rfl)
      | D => exact Or.inr (Or.inr ⟨rfl, localPattern_D_card hs (Finset.mem_sdiff.mp hz').1 hz0 hsD⟩)
    · intro z hz hz0 hztip hzU
      have hz' := Finset.mem_sdiff.mpr ⟨hz, hztip⟩
      have hUz : D.status (chart y a z) = .U := (hstat z hz') ▸ hzU
      exact localPattern_kept_U D y a out hz hz0 hUz
    · intro z hz
      exact localPattern_tip D y a out hz
    · intro z hz t ht hzX htX hadj
      rw [hm _ hz _ (Finset.mem_sdiff.mp ht).1, hm _ ht _ (Finset.mem_sdiff.mp hz).1]
      apply hs.mutualKept
      · exact Finset.mem_filter.mpr ⟨hG z (Finset.mem_sdiff.mp hz).1, (hstat z hz) ▸ hzX⟩
      · exact Finset.mem_filter.mpr ⟨hG t (Finset.mem_sdiff.mp ht).1, (hstat t ht) ▸ htX⟩
      · exact (chart_adjacent y z t a).mpr hadj
  refine ⟨π, hπ, hrot, hstat, ?_⟩
  intro z hz t ht
  have hzS := (Finset.mem_sdiff.mp hz).1
  have hzN := (Finset.mem_sdiff.mp hz).2
  by_cases htip : t ∈ templateTips
  · simp only [htip, ite_true]
    intro hp
    apply (internalPresent_iff π z t).mpr
    refine ⟨hzS, ht, (chart_adjacent y z t a).mp hp.2.2.1, ?_, ?_, ?_, Or.inl htip⟩
    · rw [hstat z hz]
      exact (Finset.mem_filter.mp hp.1).2
    · rw [localPattern_tip D y a out htip]
      decide
    · exact Or.inr ((hm z hz t ht).mpr hp.2.2.2.1)
  · simp only [htip, ite_false]
    have ht' := Finset.mem_sdiff.mpr ⟨ht, htip⟩
    change π.InternalPresent z t ↔ D.Present (chart y a z) (chart y a t)
    rw [internalPresent_iff]
    simp only [hzS, ht, true_and, hzN, htip, false_or,
      hstat z hz, hstat t ht', hm z hz t ht, hm t ht' z hzS]
    simp only [Network.Present, Network.active, Finset.mem_filter, hG z hzS, hG t ht,
      true_and, chart_adjacent]
    tauto

end AKLT.W.REC098
