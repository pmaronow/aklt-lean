import AKLT.W.REC096.Trace

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC096

theorem template_sites_eq : templateSites =
    {(0, 0), (1, 0), (0, 1), (-1, 0), (0, -1),
      (1, 1), (-1, 1), (-1, -1), (1, -1), (2, 0), (0, 2), (-2, 0), (0, -2)} := by
  decide +kernel

theorem neighbours_zero : neighbours (0, 0) = {(1, 0), (0, 1), (-1, 0), (0, -1)} := by
  decide +kernel

def canonicalOutgoing : Compass → Compass → Compass
  | .north, b => b
  | .east, .east => .north
  | .east, .north => .west
  | .east, .west => .south
  | .east, .south => .east
  | .south, .east => .west
  | .south, .north => .south
  | .south, .west => .east
  | .south, .south => .north
  | .west, .east => .south
  | .west, .north => .east
  | .west, .west => .north
  | .west, .south => .west

theorem canonical_outgoing_step (a b : Compass) :
    normalizeRotation a (canonicalOutgoing a b).step = b.step := by
  cases a <;> cases b <;> rfl

theorem canonical_south (a b : Compass) :
    canonicalOutgoing a b = .south ↔ b = a.reverse := by
  cases a <;> cases b <;> decide

def pullKept {G : Finset Plane} (E : Network G) (y : Plane) (a : Compass)
    (z : Plane) : Finset Plane :=
  (E.kept (chart y a z)).image (chart y a).symm

@[simp] theorem mem_pullKept {G : Finset Plane} (E : Network G) (y : Plane) (a : Compass)
    (z t : Plane) : t ∈ pullKept E y a z ↔ chart y a t ∈ E.kept (chart y a z) := by
  simp [pullKept, Equiv.symm_apply_eq]

theorem pullKept_sub {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
    (h : PrefixInvariant E y arrival) (z : Plane) : pullKept E y a z ⊆ neighbours z := by
  intro t ht
  have hm := (Finset.mem_inter.mp (h.kept_sub _ ((mem_pullKept _ _ _ _ _).mp ht))).1
  rw [← adjacent_iff, ← chart_adjacent y z t a]
  exact (adjacent_iff _ _).mpr hm

def completedKept {G : Finset Plane} (E : Network G) (y : Plane) (a : Compass)
    (z : Plane) : Finset Plane :=
  if E.status (chart y a z) = .U ∧ z ≠ (0, 0) then neighbours z else pullKept E y a z

theorem completedKept_sub {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
    (h : PrefixInvariant E y arrival) (z : Plane) : completedKept E y a z ⊆ neighbours z := by
  unfold completedKept
  split_ifs
  · exact Finset.Subset.refl _
  · exact pullKept_sub h z

def extractedPattern {G : Finset Plane} (E : Network G) (y : Plane) (a out : Compass) : PatternData where
  outgoing := out
  status z := if z.val ∈ templateTips then .U else E.status (chart y a z.val)
  kept z := Finset.univ.filter fun d => z.val + d.step ∈ completedKept E y a z.val

theorem extracted_status {G : Finset Plane} (E : Network G) (y : Plane) (a out : Compass)
    {z : Plane} (hz : z ∈ templateSites) :
    (extractedPattern E y a out).statusAt z =
      if z ∈ templateTips then .U else E.status (chart y a z) := by
  simp [PatternData.statusAt, extractedPattern, hz]

theorem extracted_kept {G : Finset Plane} {E : Network G} {y arrival : Plane} {a out : Compass}
    (h : PrefixInvariant E y arrival) {z : Plane} (hz : z ∈ templateSites) :
    (extractedPattern E y a out).keptAt z = completedKept E y a z := by
  simp only [PatternData.keptAt, hz, ↓reduceDIte, extractedPattern]
  ext t
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, hd, rfl⟩; exact hd
  · intro ht
    rcases Finset.mem_image.mp (completedKept_sub h z ht) with ⟨d, _, rfl⟩
    exact ⟨d, ht, rfl⟩

theorem completed_mem_internal {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
    (h : PrefixInvariant E y arrival)
    (hG : ∀ z ∈ templateSites, chart y a z ∈ G)
    {z t : Plane} (hz : z ∈ templateSites) (ht : t ∈ templateSites) :
    t ∈ completedKept E y a z ↔ chart y a t ∈ E.kept (chart y a z) := by
  unfold completedKept
  split_ifs with hu
  · have hzy : chart y a z ≠ y := by
      simpa only [chart_zero] using (chart y a).injective.ne hu.2
    rw [h.u_full _ (hG z hz) hzy hu.1, Finset.mem_inter,
      and_iff_left (hG t ht), ← adjacent_iff, ← adjacent_iff, chart_adjacent]
  · exact mem_pullKept E y a z t

theorem completed_D_card {G : Finset Plane} {E : Network G} {y arrival : Plane} {a : Compass}
    (h : PrefixInvariant E y arrival) {z : Plane} (hzG : chart y a z ∈ G)
    (hz : z ≠ (0, 0)) (hd : E.status (chart y a z) = .D) :
    (completedKept E y a z).card = 2 := by
  have hzy : chart y a z ≠ y := by
    simpa only [chart_zero] using (chart y a).injective.ne hz
  have hn : ¬(E.status (chart y a z) = .U ∧ z ≠ (0, 0)) := by
    intro hh
    have he : Status.D = .U := hd.symm.trans hh.1
    cases he
  rw [completedKept, ite_eq_right hn, pullKept,
    Finset.card_image_of_injective _ (chart y a).symm.injective]
  exact h.d_two _ hzG hzy hd

theorem completed_center {G : Finset Plane} {E : Network G} {y : Plane} {a : Compass}
    (h : PrefixInvariant E y (y - a.step))
    (hy : y ∈ G) (hS : y ∉ protectedSites G) (hu : E.status y = .U) :
    completedKept E y a (0, 0) = {(1, 0), (0, 1), (-1, 0)} := by
  have hnG : neighbours y ∩ G = neighbours y := by
    apply Finset.inter_eq_left.mpr
    intro t ht
    exact interior_ball hy hS (((adjacent_iff _ _).mpr ht).le.trans (by decide))
  have hcanonical : completedKept E y a (0, 0) = (neighbours (0, 0)).erase (0, -1) := by
    ext t
    simp only [completedKept, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
      mem_pullKept, chart_zero, h.liveU hu, hnG, Finset.mem_erase]
    have he : chart y a t ≠ y - a.step ↔ t ≠ (0, -1) := by
      rw [← chart_south y a]
      exact not_congr (chart y a).injective.eq_iff
    have hn : chart y a t ∈ neighbours y ↔ t ∈ neighbours (0, 0) := by
      rw [← adjacent_iff, ← adjacent_iff]
      simpa only [chart_zero] using chart_adjacent y (0, 0) t a
    exact and_congr he hn
  rw [hcanonical, neighbours_zero]
  decide +kernel

theorem internalBonds_iff (S : Finset Plane) (x z : Plane) :
    (x, z) ∈ internalBonds S ↔ x ∈ S ∧ z ∈ S ∧ z ∈ positiveNeighbours x := by
  simp [internalBonds, Finset.mem_biUnion, Finset.mem_image, Prod.ext_iff, and_comm,
    and_left_comm, and_assoc]

theorem unoriented_internalBonds (S : Finset Plane) (x z : Plane) :
    ((x, z) ∈ internalBonds S ∨ (z, x) ∈ internalBonds S) ↔
      x ∈ S ∧ z ∈ S ∧ Adjacent x z := by
  rw [internalBonds_iff, internalBonds_iff]
  have ha : Adjacent x z ↔ z ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours z := by
    rw [adjacent_iff]
    simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨d, rfl⟩
      cases d <;> simp [positiveNeighbours, Compass.step, Prod.ext_iff]
    · intro hm
      simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with (hm | hm) | (hm | hm)
      · exact ⟨.east, by simpa [Compass.step, Prod.ext_iff] using hm.symm⟩
      · exact ⟨.north, by simpa [Compass.step, Prod.ext_iff] using hm.symm⟩
      · exact ⟨.west, by rw [hm]; ext <;> simp [Compass.step]⟩
      · exact ⟨.south, by rw [hm]; ext <;> simp [Compass.step]⟩
  rw [ha]
  tauto

theorem internal_present_iff (π : PatternData) {z t : Plane}
    (hz : z ∈ templateSites) (ht : t ∈ templateSites) :
    π.InternalPresent z t ↔ Adjacent z t ∧ π.statusAt z ≠ .X ∧ π.statusAt t ≠ .X ∧
      (z ∈ templateTips ∨ t ∈ π.keptAt z) ∧ (t ∈ templateTips ∨ z ∈ π.keptAt t) := by
  simp only [PatternData.InternalPresent, PatternData.bonds, Finset.mem_filter]
  have ha := unoriented_internalBonds templateSites z t
  simp only [hz, ht, true_and] at ha
  have hs : Adjacent z t ↔ Adjacent t z := ⟨adjacent_symm, adjacent_symm⟩
  tauto

theorem template_step (d : Compass) : d.step ∈ templateSites ∧ d.step ∉ templateTips := by
  cases d <;> decide +kernel

theorem template_tips_sub : templateTips ⊆ templateSites := by decide +kernel

theorem template_corner_facts {z : Plane} (hz : z ∈ templateCorners) :
    z ∈ templateSites ∧ z ∉ templateTips ∧ z ≠ (0, 0) := by
  simp only [templateCorners, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Extract the covered template from the live endpoint invariant. U flags
outside the template are completed; tip statuses are covering U statuses. -/
theorem invariant_covered {G : Finset Plane} {E : Network G} {y : Plane}
    {a out : Compass} (h : PrefixInvariant E y (y - a.step))
    (hy : y ∈ G) (hS : y ∉ protectedSites G) (hu : E.status y = .U)
    (hp : E.Present y (y + out.step)) : AKLT.Defs.CoveredDepartureV2 E y a out := by
  classical
  let o := canonicalOutgoing a out
  let π := extractedPattern E y a o
  have hG : ∀ z ∈ templateSites, chart y a z ∈ G :=
    fun _ hz => template_interior hy hS a hz
  have h0 : (0, 0) ∈ templateSites \ templateTips := by decide +kernel
  have hA : (0, -1) ∈ templateSites \ templateTips := by decide +kernel
  have hstatus (z : Plane) (hz : z ∈ templateSites \ templateTips) :
      π.statusAt z = E.status (chart y a z) := by
    rw [extracted_status E y a o (Finset.mem_sdiff.mp hz).1,
      ite_eq_right (Finset.mem_sdiff.mp hz).2]
  have hkept (z : Plane) (hz : z ∈ templateSites) :
      π.keptAt z = completedKept E y a z := extracted_kept h hz
  have hmk (z t : Plane) (hz : z ∈ templateSites) (ht : t ∈ templateSites) :
      t ∈ π.keptAt z ↔ chart y a t ∈ E.kept (chart y a z) := by
    rw [hkept z hz]
    exact completed_mem_internal h hG hz ht
  have hs0 : π.statusAt (0, 0) = .U := by rw [hstatus _ h0, chart_zero, hu]
  have hk0 : π.keptAt (0, 0) = {(1, 0), (0, 1), (-1, 0)} := by
    rw [hkept _ (Finset.mem_sdiff.mp h0).1]
    exact completed_center h hy hS hu
  have htip (z : Plane) (hz : z ∈ templateTips) : π.statusAt z = .U := by
    rw [extracted_status E y a o (template_tips_sub hz), ite_eq_left hz]
  have hagree : ∀ z ∈ templateSites \ templateTips, ∀ t ∈ templateSites \ templateTips,
      π.statusAt z ≠ .X → π.statusAt t ≠ .X → Adjacent z t →
        (t ∈ π.keptAt z ↔ z ∈ π.keptAt t) := by
    intro z hz t ht hsz hst hadj
    have hzS := (Finset.mem_sdiff.mp hz).1
    have htS := (Finset.mem_sdiff.mp ht).1
    rw [hstatus z hz] at hsz
    rw [hstatus t ht] at hst
    rw [hmk z t hzS htS, hmk t z htS hzS]
    exact h.agree _ (Finset.mem_filter.mpr ⟨hG z hzS, hsz⟩)
      _ (Finset.mem_filter.mpr ⟨hG t htS, hst⟩)
      ((chart_adjacent _ _ _ _).mpr hadj)
  have hD (z : Plane) (hz : z ∈ templateSites \ templateTips)
      (hne : z ≠ (0, 0)) (hd : π.statusAt z = .D) : (π.keptAt z).card = 2 := by
    rw [hkept _ (Finset.mem_sdiff.mp hz).1]
    exact completed_D_card h (hG z (Finset.mem_sdiff.mp hz).1) hne ((hstatus z hz) ▸ hd)
  have hoS : o.step ∈ templateSites \ templateTips := Finset.mem_sdiff.mpr (template_step o)
  have hochart : chart y a o.step = y + out.step := by
    exact congrArg (y + ·) (canonical_outgoing_step a out)
  have hsout : π.statusAt o.step ≠ .X := by
    rw [hstatus _ hoS, hochart]
    exact (Finset.mem_filter.mp hp.2.1).2
  have hko : o.step ∈ π.keptAt (0, 0) := by
    rw [hmk _ _ (Finset.mem_sdiff.mp h0).1 (Finset.mem_sdiff.mp hoS).1, chart_zero, hochart]
    exact hp.2.2.2.1
  have hno : o ≠ .south := by
    intro he
    rw [he, hk0] at hko
    simp [Compass.step] at hko
  have hcov : π.Covered := by
    refine ⟨hno, hs0, hk0, ?_, ?_, hsout, ?_, ?_, htip, hagree⟩
    · have hnotU : π.statusAt (0, -1) ≠ .U := by
        rw [hstatus _ hA, chart_south]
        exact h.arrival_notU
      cases hs : π.statusAt (0, -1) with
      | U => exact (hnotU hs).elim
      | X => exact Or.inl rfl
      | D =>
        right
        refine ⟨rfl, hD _ hA (by decide) hs, ?_⟩
        have hm := hagree (0, -1) hA (0, 0) h0 (by rw [hs]; decide)
          (by rw [hs0]; decide) (by decide +kernel)
        rw [hm, hk0]
        decide +kernel
    · intro d hd
      have hdS := Finset.mem_sdiff.mpr (template_step d)
      cases hs : π.statusAt d.step with
      | U => exact Or.inl rfl
      | X => exact Or.inr (Or.inl rfl)
      | D =>
        right; right
        refine ⟨rfl, hD _ hdS (by cases d <;> decide) hs, ?_⟩
        have hm := hagree d.step hdS (0, 0) h0 (by rw [hs]; decide)
          (by rw [hs0]; decide) (by cases d <;> decide +kernel)
        rw [hm, hk0]
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl <;> simp [Compass.step]
    · intro z hz
      have hzfacts := template_corner_facts hz
      have hzS := Finset.mem_sdiff.mpr ⟨hzfacts.1, hzfacts.2.1⟩
      cases hs : π.statusAt z with
      | U => exact Or.inl rfl
      | X => exact Or.inr (Or.inl rfl)
      | D => exact Or.inr (Or.inr ⟨rfl, hD z hzS hzfacts.2.2 hs⟩)
    · intro z hz hn0 hnt hsz
      have hzS := Finset.mem_sdiff.mpr ⟨hz, hnt⟩
      rw [hstatus z hzS] at hsz
      rw [hkept z hz]
      rw [completedKept, ite_eq_left ⟨hsz, hn0⟩]
  refine ⟨π, hcov, canonical_outgoing_step a out, hstatus, ?_⟩
  intro z hz t ht
  have hzS := (Finset.mem_sdiff.mp hz).1
  have hznt := (Finset.mem_sdiff.mp hz).2
  change if t ∈ templateTips then E.Present (chart y a z) (chart y a t) → π.InternalPresent z t
    else π.InternalPresent z t ↔ E.Present (chart y a z) (chart y a t)
  split_ifs with httip
  · intro hpres
    rw [internal_present_iff π hzS ht]
    refine ⟨(chart_adjacent _ _ _ _).mp hpres.2.2.1, ?_, ?_, ?_, Or.inl httip⟩
    · rw [hstatus z hz]; exact (Finset.mem_filter.mp hpres.1).2
    · rw [htip t httip]; decide
    · right
      exact (hmk z t hzS ht).mpr hpres.2.2.2.1
  · have htnt : t ∈ templateSites \ templateTips := Finset.mem_sdiff.mpr ⟨ht, httip⟩
    rw [internal_present_iff π hzS ht]
    simp only [hznt, httip, false_or, hstatus z hz, hstatus t htnt,
      hmk z t hzS ht, hmk t z ht hzS]
    unfold Network.Present Network.active
    simp only [Finset.mem_filter, hG z hzS, hG t ht, true_and, chart_adjacent]
    tauto

end AKLT.W.REC096
