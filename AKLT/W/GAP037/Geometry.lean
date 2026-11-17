module
public import AKLT.W.GAP037.Basic
public import AKLT.Challenge.Sanity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable
namespace AKLT.W.GAP037
local instance (α : Type) : DecidableEq α := Classical.decEq α

@[simp] theorem mem_square (a z : Plane) (M : ℕ) : z ∈ square a M ↔
    a.1 - (M : ℤ) ≤ z.1 ∧ z.1 ≤ a.1 + M ∧
    a.2 - (M : ℤ) ≤ z.2 ∧ z.2 ≤ a.2 + M := by
  simp [square, and_assoc]

theorem square_mono (a : Plane) {m n : ℕ} (h : m ≤ n) : square a m ⊆ square a n := by
  intro z hz
  simp only [mem_square] at *
  omega

theorem intCast_inj_interval (P : ℕ) (m : ℕ) (hP : 2*m+1 ≤ P)
    (a x y : ℤ) (hx : a - (m : ℤ) ≤ x ∧ x ≤ a + m)
    (hy : a - (m : ℤ) ≤ y ∧ y ≤ a + m)
    (h : (x : ZMod P) = (y : ZMod P)) : x = y := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y P).mp h
  have habs : |y - x| < (P : ℤ) := abs_lt.mpr ⟨by omega, by omega⟩
  have hn : (y - x).natAbs < P := by
    have : ((y - x).natAbs : ℤ) < (P : ℤ) := by simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast this
  have hz : y - x = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hn)
  omega

/-- Injectivity on the full physical halo, proved directly from the period bounds. -/
theorem reduction_inj_halo (L N : Size) (M : ℕ)
    (hL : 2*M+3 ≤ L.val) (hN : 2*M+3 ≤ N.val) (a : Plane) :
    Set.InjOn (reduction L N) (↑(square a (M+1)) : Set Plane) := by
  intro x hx y hy heq
  simp only [Finset.mem_coe, mem_square] at hx hy
  apply Prod.ext
  · exact intCast_inj_interval L.val (M+1) (by omega) a.1 x.1 y.1
      ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩ (congrArg Prod.fst heq)
  · exact intCast_inj_interval N.val (M+1) (by omega) a.2 x.2 y.2
      ⟨hx.2.2.1, hx.2.2.2⟩ ⟨hy.2.2.1, hy.2.2.2⟩ (congrArg Prod.snd heq)

theorem coordinates_image {L N : Size} {M : ℕ} {a : Site L N}
    {κ : Site L N → Fin 3} (C : BoxCoordinates L N M a κ) :
    (square C.centre M).image (reduction L N) = torusSquare L N M a := by
  ext x
  constructor
  · rintro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    let t := C.change.sites.symm ⟨z, hz⟩
    have ht : reduction L N z = t.val := by
      simpa only [t, Equiv.apply_symm_apply] using C.site_reduces t
    rw [ht]
    exact t.property
  · intro hx
    exact Finset.mem_image.mpr ⟨(C.change.sites ⟨x, hx⟩).val,
      (C.change.sites ⟨x, hx⟩).property, C.site_reduces ⟨x, hx⟩⟩

/-- The four possible displacements of a nearest neighbour. -/
theorem adjacent_iff_steps (x y : Plane) : Adjacent x y ↔
    y = (x.1+1, x.2) ∨ y = (x.1, x.2+1) ∨
    x = (y.1+1, y.2) ∨ x = (y.1, y.2+1) := by
  constructor
  · intro h
    have hd : (x.1-y.1).natAbs + (x.2-y.2).natAbs = 1 := h
    rcases Nat.add_eq_one_iff.mp hd with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hx := Int.natAbs_eq_zero.mp hx
      rcases Int.natAbs_eq_iff.mp hy with hy | hy
      · right; right; right; apply Prod.ext <;> dsimp <;> omega
      · right; left; apply Prod.ext <;> dsimp <;> omega
    · have hy := Int.natAbs_eq_zero.mp hy
      rcases Int.natAbs_eq_iff.mp hx with hx | hx
      · right; right; left; apply Prod.ext <;> dsimp <;> omega
      · left; apply Prod.ext <;> dsimp <;> omega
  · rintro (rfl | rfl | rfl | rfl) <;>
      simp [Adjacent, latticeDist]

theorem mem_neighbours_iff (x y : Plane) : y ∈ neighbours x ↔ Adjacent x y := by
  rw [adjacent_iff_steps]
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    cases d <;> simp [Compass.step, Prod.add_def]
  · rintro (rfl | rfl | h | h)
    · exact ⟨.east, by simp [Compass.step, Prod.add_def]⟩
    · exact ⟨.north, by simp [Compass.step, Prod.add_def]⟩
    · exact ⟨.west, by rw [h]; simp [Compass.step, Prod.add_def]⟩
    · exact ⟨.south, by rw [h]; simp [Compass.step, Prod.add_def]⟩

@[simp] theorem mem_internalBonds (W : Finset Plane) (e : Plane × Plane) :
    e ∈ internalBonds W ↔ e.1 ∈ W ∧ e.2 ∈ W ∧ e.2 ∈ positiveNeighbours e.1 := by
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨x,hx,y,⟨hy,hyW⟩,rfl⟩
    exact ⟨hx,hyW,hy⟩
  · rintro ⟨hx,hy,he⟩
    exact ⟨e.1,hx,e.2,⟨he,hy⟩,rfl⟩

@[simp] theorem mem_originalLegs (W : Finset Plane) (e : Plane × Plane) :
    e ∈ originalLegs W ↔ e.1 ∈ W ∧ e.2 ∉ W ∧ Adjacent e.1 e.2 := by
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,y,⟨hy,hyW⟩,rfl⟩
    exact ⟨hx,hyW,(mem_neighbours_iff x y).mp hy⟩
  · rintro ⟨hx,hy,he⟩
    exact ⟨e.1,hx,e.2,⟨(mem_neighbours_iff e.1 e.2).mpr he,hy⟩,rfl⟩

theorem positive_adjacent {x y : Plane} (h : y ∈ positiveNeighbours x) : Adjacent x y := by
  apply (adjacent_iff_steps x y).mpr
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at h
  tauto

theorem adjacent_in_halo {a x y : Plane} {M : ℕ}
    (hx : x ∈ square a M) (hxy : Adjacent x y) : y ∈ square a (M+1) := by
  rw [adjacent_iff_steps] at hxy
  simp only [mem_square] at hx ⊢
  rcases hxy with h | h | h | h <;>
    have h1 := congrArg Prod.fst h <;> have h2 := congrArg Prod.snd h <;> dsimp at * <;> omega

/-- All factors involving at least one free plane site, counted once. -/
def planeEdges (W : Finset Plane) : Finset (Plane × Plane) := internalBonds W ∪ originalLegs W

theorem planeEdges_disjoint (W : Finset Plane) : Disjoint (internalBonds W) (originalLegs W) := by
  apply Finset.disjoint_left.mpr
  intro e hi he
  exact (mem_originalLegs W e).mp he |>.2.1 ((mem_internalBonds W e).mp hi).2.1

theorem planeEdges_data {W : Finset Plane} {e : Plane × Plane} (h : e ∈ planeEdges W) :
    e.1 ∈ W ∧ Adjacent e.1 e.2 := by
  rcases Finset.mem_union.mp h with h | h
  · have h := (mem_internalBonds W e).mp h
    exact ⟨h.1, positive_adjacent h.2.2⟩
  · have h := (mem_originalLegs W e).mp h
    exact ⟨h.1,h.2.2⟩

/-- Every lifted edge reduces to a frozen torus bond, without any parity assumption. -/
theorem adjacent_reduces (L N : Size) {x y : Plane} (h : Adjacent x y) :
    ∃ b : Bond L N, bondSites b = {reduction L N x, reduction L N y} := by
  rcases (adjacent_iff_steps x y).mp h with rfl | rfl | rfl | rfl
  · exact ⟨(reduction L N x, 0), by simp [bondSites, nextSite, reduction, Int.cast_add]⟩
  · exact ⟨(reduction L N x, 1), by simp [bondSites, nextSite, reduction, Int.cast_add]⟩
  · exact ⟨(reduction L N y, 0), by simp [bondSites, nextSite, reduction, Int.cast_add, Finset.pair_comm]⟩
  · exact ⟨(reduction L N y, 1), by simp [bondSites, nextSite, reduction, Int.cast_add, Finset.pair_comm]⟩

/-- The unique bond with the reduced unordered endpoints, when it exists. -/
def edgeBond (L N : Size) (e : Plane × Plane) : Bond L N :=
  if h : ∃ b : Bond L N, bondSites b = {reduction L N e.1, reduction L N e.2}
    then Classical.choose h else (0, 0)

theorem edgeBond_sites (L N : Size) {e : Plane × Plane} (h : Adjacent e.1 e.2) :
    bondSites (edgeBond L N e) = {reduction L N e.1, reduction L N e.2} := by
  have he := adjacent_reduces L N h
  simp only [edgeBond, dite_eq_left he]
  exact Classical.choose_spec he

theorem positive_asymm {x y : Plane} (hxy : y ∈ positiveNeighbours x)
    (hyx : x ∈ positiveNeighbours y) : False := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hxy hyx
  rcases hxy with hxy | hxy <;> rcases hyx with hyx | hyx <;>
    have h1 := congrArg Prod.fst hxy <;> have h2 := congrArg Prod.snd hxy <;>
    have h3 := congrArg Prod.fst hyx <;> have h4 := congrArg Prod.snd hyx <;> dsimp at * <;> omega

theorem planeEdges_positive {W : Finset Plane} {e : Plane × Plane}
    (h : e ∈ planeEdges W) (hy : e.2 ∈ W) : e.2 ∈ positiveNeighbours e.1 := by
  rcases Finset.mem_union.mp h with h | h
  · exact ((mem_internalBonds W e).mp h).2.2
  · exact (((mem_originalLegs W e).mp h).2.1 hy).elim

theorem pair_eq_pair_cases {α : Type} [DecidableEq α] {x y z w : α}
    (h : ({x,y} : Finset α) = {z,w}) : (x=z ∧ y=w) ∨ (x=w ∧ y=z) := by
  apply Set.pair_eq_pair_iff.mp
  simpa using congrArg (fun s : Finset α => (s : Set α)) h

/-- No internal or crossing edge is repeated under the reduction map. -/
theorem edgeBond_injective (L N : Size) (M : ℕ) (a : Plane)
    (hI : Set.InjOn (reduction L N) (↑(square a (M+1)) : Set Plane)) :
    Set.InjOn (edgeBond L N) (↑(planeEdges (square a M)) : Set (Plane × Plane)) := by
  intro e he f hf hef
  have heD := planeEdges_data he
  have hfD := planeEdges_data hf
  have he1 := square_mono a (Nat.le_succ M) heD.1
  have hf1 := square_mono a (Nat.le_succ M) hfD.1
  have he2 := adjacent_in_halo heD.1 heD.2
  have hf2 := adjacent_in_halo hfD.1 hfD.2
  have hp : ({reduction L N e.1, reduction L N e.2} : Finset (Site L N)) =
      {reduction L N f.1, reduction L N f.2} := by
    rw [← edgeBond_sites L N heD.2, ← edgeBond_sites L N hfD.2, hef]
  rcases pair_eq_pair_cases hp with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext (hI he1 hf1 h1) (hI he2 hf2 h2)
  · have h1 := hI he1 hf2 h1
    have h2 := hI he2 hf1 h2
    have hep := planeEdges_positive he (by rw [h2]; exact hfD.1)
    have hfp := planeEdges_positive hf (by rw [← h1]; exact heD.1)
    rw [← h2, ← h1] at hfp
    exact (positive_asymm hep hfp).elim

def Touches {L N : Size} (Q : Finset (Site L N)) (b : Bond L N) : Prop :=
  b.1 ∈ Q ∨ nextSite b.1 b.2 ∈ Q

def localBonds {L N : Size} (Q : Finset (Site L N)) : Finset (Bond L N) :=
  Finset.univ.filter (Touches Q)

theorem touches_of_mem {L N : Size} {Q : Finset (Site L N)} {b : Bond L N}
    {x : Site L N} (hx : x ∈ Q) (hb : x ∈ bondSites b) : Touches Q b := by
  simp only [bondSites, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact Or.inl hx
  · exact Or.inr hx

theorem edgeBond_local {L N : Size} {M : ℕ} {a : Plane}
    {e : Plane × Plane} (he : e ∈ planeEdges (square a M)) :
    edgeBond L N e ∈ localBonds ((square a M).image (reduction L N)) := by
  have hd := planeEdges_data he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, touches_of_mem (Finset.mem_image.mpr ⟨e.1,hd.1,rfl⟩) ?_⟩
  rw [edgeBond_sites L N hd.2]
  simp

theorem internal_edge_exists {W : Finset Plane} {x y : Plane}
    (hx : x ∈ W) (hy : y ∈ W) (hxy : Adjacent x y) :
    ∃ e ∈ internalBonds W, ({e.1,e.2} : Finset Plane) = {x,y} := by
  rcases (adjacent_iff_steps x y).mp hxy with h | h | h | h
  · refine ⟨(x,y), (mem_internalBonds W _).mpr ⟨hx,hy,?_⟩, rfl⟩
    simp [positiveNeighbours,h]
  · refine ⟨(x,y), (mem_internalBonds W _).mpr ⟨hx,hy,?_⟩, rfl⟩
    simp [positiveNeighbours,h]
  · refine ⟨(y,x), (mem_internalBonds W _).mpr ⟨hy,hx,?_⟩, Finset.pair_comm _ _⟩
    simp [positiveNeighbours,h]
  · refine ⟨(y,x), (mem_internalBonds W _).mpr ⟨hy,hx,?_⟩, Finset.pair_comm _ _⟩
    simp [positiveNeighbours,h]

/-- The exact lifted bond hypotheses make the reduction onto the local torus bonds. -/
theorem edgeBond_surjective (L N : Size) (M : ℕ) (a : Plane)
    (hB : LiftBonds L N M a) :
    ∀ b ∈ localBonds ((square a M).image (reduction L N)),
      ∃ e ∈ planeEdges (square a M), edgeBond L N e = b := by
  let Q := (square a M).image (reduction L N)
  intro b hb
  have ht : Touches Q b := (Finset.mem_filter.mp hb).2
  have hcross (hc : (bondSites b ∩ Q).card = 1) :
      ∃ e ∈ planeEdges (square a M), edgeBond L N e = b := by
    obtain ⟨x,hx,y,hy,hxy,hbxy⟩ := hB.2.1 b hc
    refine ⟨(x,y), Finset.mem_union_right _ ((mem_originalLegs _ _).mpr
      ⟨hx,(Finset.mem_sdiff.mp hy).2,hxy⟩), ?_⟩
    apply bonds_areDistinct L N
    exact (edgeBond_sites L N hxy).trans hbxy.symm
  by_cases hs : b.1 ∈ Q
  · by_cases ht' : nextSite b.1 b.2 ∈ Q
    · obtain ⟨x,hx,hxp⟩ := Finset.mem_image.mp hs
      obtain ⟨y,hy,hyp⟩ := Finset.mem_image.mp ht'
      have hxy : Adjacent x y := (hB.1 x y hx hy).mpr ⟨b, by rw [hxp,hyp]; rfl⟩
      obtain ⟨e,he,hep⟩ := internal_edge_exists hx hy hxy
      refine ⟨e, Finset.mem_union_left _ he, ?_⟩
      apply bonds_areDistinct L N
      have hr := congrArg (Finset.image (reduction L N)) hep
      simp only [Finset.image_insert, Finset.image_singleton] at hr
      rw [edgeBond_sites L N (planeEdges_data (Finset.mem_union_left _ he)).2, hr, hxp,hyp]
      rfl
    · apply hcross
      have hi : bondSites b ∩ Q = {b.1} := by
        ext x
        simp only [bondSites, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h,hx⟩
          rcases h with h | h
          · exact h
          · exact (ht' (h ▸ hx)).elim
        · rintro rfl
          exact ⟨Or.inl rfl,hs⟩
      rw [hi,Finset.card_singleton]
  · have ht' : nextSite b.1 b.2 ∈ Q := ht.resolve_left hs
    apply hcross
    have hi : bondSites b ∩ Q = {nextSite b.1 b.2} := by
      ext x
      simp only [bondSites, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h,hx⟩
        rcases h with h | h
        · exact (hs (h ▸ hx)).elim
        · exact h
      · rintro rfl
        exact ⟨Or.inr rfl,ht'⟩
    rw [hi,Finset.card_singleton]

theorem exteriorSites_data {W : Finset Plane} {z : Plane} (hz : z ∈ exteriorSites W) :
    z ∉ W ∧ ∃ x ∈ W, Adjacent x z := by
  obtain ⟨e,he,hez⟩ := Finset.mem_image.mp hz
  have hd := (mem_originalLegs W e).mp he
  subst z
  exact ⟨hd.2.1,e.1,hd.1,hd.2.2⟩

theorem planeEdges_second {W : Finset Plane} {e : Plane × Plane} (he : e ∈ planeEdges W) :
    e.2 ∈ W ∨ e.2 ∈ exteriorSites W := by
  rcases Finset.mem_union.mp he with hi | hl
  · exact Or.inl ((mem_internalBonds W e).mp hi).2.1
  · exact Or.inr (Finset.mem_image.mpr ⟨e,hl,rfl⟩)

end AKLT.W.GAP037
