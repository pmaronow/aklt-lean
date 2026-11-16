import AKLT.W.REC012.Local

noncomputable section
open scoped BigOperators
open AKLT.Defs
namespace AKLT.W.REC012

lemma latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  congr 1 <;> omega
lemma adjacent_ne {x y : Plane} (h : Adjacent x y) : x ≠ y := by
  rintro rfl
  simp [Adjacent, latticeDist] at h
lemma present_symm {G : Finset Plane} (D : Network G) {x y : Plane} :
    D.Present x y ↔ D.Present y x := by
  unfold Network.Present Adjacent
  rw [latticeDist_symm x y]
  tauto
lemma mem_internalBonds {G : Finset Plane} {e : Plane × Plane} (h : e ∈ internalBonds G) :
    e.1 ∈ G ∧ e.2 ∈ G ∧ e.2 ∈ positiveNeighbours e.1 := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter] at h
  obtain ⟨x, hx, z, ⟨hz, hzG⟩, he⟩ := h
  cases he
  exact ⟨hx, hzG, hz⟩
lemma positive_neighbour_ne {x y : Plane} (h : y ∈ positiveNeighbours x) : x ≠ y := by
  rcases x with ⟨x₁,x₂⟩; rcases y with ⟨y₁,y₂⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  intro he
  cases he
  omega
lemma positive_asymm {x y : Plane} (h : y ∈ positiveNeighbours x) : x ∉ positiveNeighbours y := by
  rcases x with ⟨x₁,x₂⟩; rcases y with ⟨y₁,y₂⟩
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at *
  omega
lemma positive_neighbour_mem {x y : Plane} (h : y ∈ positiveNeighbours x) : y ∈ neighbours x := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact Finset.mem_image.mpr ⟨.east, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
  · exact Finset.mem_image.mpr ⟨.north, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
lemma positive_neighbour_mem_reverse {x y : Plane} (h : y ∈ positiveNeighbours x) : x ∈ neighbours y := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact Finset.mem_image.mpr ⟨.west, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩
  · exact Finset.mem_image.mpr ⟨.south, Finset.mem_univ _, by ext <;> simp [Compass.step]⟩

/-- Bonds incident to the spin being integrated. -/
def incident {G : Finset Plane} (D : Network G) (y : Plane) : Finset (Plane × Plane) :=
  D.bonds.filter fun e => e.1 = y ∨ e.2 = y

def otherEnd (y : Plane) (e : Plane × Plane) : Plane := if e.1 = y then e.2 else e.1

lemma incident_other_ne {G : Finset Plane} (D : Network G) (y : Plane)
    {e : Plane × Plane} (he : e ∈ incident D y) : otherEnd y e ≠ y := by
  obtain ⟨hb, hi⟩ := Finset.mem_filter.mp he
  have hp := (mem_internalBonds (Finset.mem_filter.mp hb).1).2.2
  have hn := positive_neighbour_ne hp
  rcases hi with hi | hi
  · simpa [otherEnd, hi] using Ne.symm hn
  · simp only [otherEnd]
    split_ifs with h <;> simp_all

lemma incident_other_mem {G : Finset Plane} (D : Network G) (y : Plane)
    {e : Plane × Plane} (he : e ∈ incident D y) : otherEnd y e ∈ D.presentNeighbours y := by
  obtain ⟨hb, hi⟩ := Finset.mem_filter.mp he
  obtain ⟨hedge, hpres⟩ := Finset.mem_filter.mp hb
  have hp := (mem_internalBonds hedge).2.2
  apply Finset.mem_filter.mpr
  rcases hi with hi | hi
  · simp only [otherEnd, hi, ↓reduceIte]
    exact ⟨hi ▸ positive_neighbour_mem hp, hi ▸ hpres⟩
  · have hn := positive_neighbour_ne hp
    have hy : e.1 ≠ y := by simpa [hi] using hn
    simp only [otherEnd, hy, ↓reduceIte]
    exact ⟨hi ▸ positive_neighbour_mem_reverse hp, hi ▸ (present_symm D).mp hpres⟩

lemma incident_other_injective {G : Finset Plane} (D : Network G) (y : Plane) :
    Set.InjOn (otherEnd y) (incident D y) := by
  intro e he f hf h
  obtain ⟨heb, hei⟩ := Finset.mem_filter.mp he
  obtain ⟨hfb, hfi⟩ := Finset.mem_filter.mp hf
  have hep := (mem_internalBonds (Finset.mem_filter.mp heb).1).2.2
  have hfp := (mem_internalBonds (Finset.mem_filter.mp hfb).1).2.2
  by_cases hey : e.1 = y <;> by_cases hfy : f.1 = y
  · apply Prod.ext <;> simp_all [otherEnd]
  · have hfy' : f.2 = y := hfi.resolve_left hfy
    have heq : e.2 = f.1 := by simpa [otherEnd, hey, hfy] using h
    have hnot := positive_asymm hep
    exact (hnot (by simpa [hey, hfy', heq] using hfp)).elim
  · have hey' : e.2 = y := hei.resolve_left hey
    have heq : e.1 = f.2 := by simpa [otherEnd, hey, hfy] using h
    have hnot := positive_asymm hfp
    exact (hnot (by simpa [hfy, hey', heq] using hep)).elim
  · apply Prod.ext
    · simpa [otherEnd, hey, hfy] using h
    · exact (hei.resolve_left hey).trans (hfi.resolve_left hfy).symm

lemma incident_card_le {G : Finset Plane} (D : Network G) (y : Plane) :
    (incident D y).card ≤ (D.presentNeighbours y).card :=
  Finset.card_le_card_of_injOn (otherEnd y) (fun _ h => incident_other_mem D y h)
    (incident_other_injective D y)

lemma neighbour_dist {y z : Plane} (hz : z ∈ neighbours y) : latticeDist y z = 1 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hz
  cases d <;> simp [latticeDist, Compass.step]

lemma no_legs_at_start {G : Finset Plane} (D : Network G) (y : Plane)
    (hy : D.AdmissibleStart y) (e : originalLegs G) : e.val.1 ≠ y := by
  intro he
  have hyG : y ∈ G := (Finset.mem_filter.mp hy.1).1
  have hleg := e.property
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff] at hleg
  obtain ⟨x, hx, z, ⟨hz, hzG⟩, hex⟩ := hleg
  have hx' : x = y := by simpa [← hex] using he
  subst x
  have hd : boundaryDepth G y ≤ 1 := by
    unfold boundaryDepth setDistance
    exact iInf_le_of_le ⟨z, hzG⟩ (by simp [neighbour_dist hz])
  apply hy.2.1
  simp only [protectedSites, Finset.mem_filter]
  exact ⟨hyG, le_trans hd (by norm_num)⟩

lemma trace_active_off {G : Finset Plane} (D : Network G) (y o x : Plane) (hx : x ≠ y) :
    x ∈ (traceStep D y o).active ↔ x ∈ D.active := by
  unfold Network.active
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [traceStep, Function.update, hx]

lemma trace_present_off {G : Finset Plane} (D : Network G) (y o x z : Plane)
    (hx : x ≠ y) (hz : z ≠ y) :
    (traceStep D y o).Present x z ↔ D.Present x z := by
  have hk (a b : Plane) (ha : a ≠ y) (hb : b ≠ y) :
      b ∈ (traceStep D y o).kept a ↔ b ∈ D.kept a := by
    change b ∈ (if a = y then _ else if a = o then _ else _) ↔ _
    rw [ite_eq_right ha]
    split_ifs <;> simp [Finset.mem_erase, hb]
  unfold Network.Present
  rw [trace_active_off D y o x hx, trace_active_off D y o z hz, hk x z hx hz, hk z x hz hx]

lemma trace_neighbours_U {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) (ho : o ∈ D.presentNeighbours y) :
    (traceStep D y o).presentNeighbours y = (D.presentNeighbours y).erase o := by
  have hp := (Finset.mem_filter.mp ho).2
  have hyo := adjacent_ne hp.2.2.1
  ext x
  change x ∈ (neighbours y).filter _ ↔ x ∈ ((neighbours y).filter _).erase o
  rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
  by_cases hxy : x = y
  · subst x
    simp [Network.Present, Adjacent, latticeDist]
  by_cases hxo : x = o
  · subst x
    simp [Network.Present, traceStep, Finset.mem_erase]
  · simp [Network.Present, Network.active, Finset.mem_filter,
      traceStep, hU, hxy, hxo]

lemma trace_neighbours_D {G : Finset Plane} (D : Network G) (y o : Plane)
    (hD : D.status y = .D) : (traceStep D y o).presentNeighbours y = ∅ := by
  ext x
  simp [Network.presentNeighbours, Finset.mem_filter, Network.Present, Network.active, traceStep, hD]

end AKLT.W.REC012
