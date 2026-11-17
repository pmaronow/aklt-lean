module
public import AKLT.W.REC014.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC014

theorem neighbour_adjacent {x z : Plane} (h : z ∈ neighbours x) : Adjacent x z := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp h
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

theorem adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x := by
  unfold Adjacent latticeDist at *
  omega

theorem adjacent_ne {x z : Plane} (h : Adjacent x z) : x ≠ z := by
  rintro rfl
  norm_num [Adjacent, latticeDist] at h

theorem adjacent_neighbour {x z : Plane} (h : Adjacent x z) : z ∈ neighbours x := by
  rcases x with ⟨a,b⟩
  rcases z with ⟨c,d⟩
  have hh : (a - c).natAbs + (b - d).natAbs = 1 := h
  have hc : c = a + 1 ∧ d = b ∨ c = a ∧ d = b + 1 ∨
      c = a - 1 ∧ d = b ∨ c = a ∧ d = b - 1 := by omega
  rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Finset.mem_image.mpr ⟨.east, Finset.mem_univ _, by simp [Compass.step]⟩
  · exact Finset.mem_image.mpr ⟨.north, Finset.mem_univ _, by simp [Compass.step]⟩
  · exact Finset.mem_image.mpr ⟨.west, Finset.mem_univ _, by simp [Compass.step, sub_eq_add_neg]⟩
  · exact Finset.mem_image.mpr ⟨.south, Finset.mem_univ _, by simp [Compass.step, sub_eq_add_neg]⟩

theorem present_symm {G : Finset Plane} (D : Network G) {x z : Plane}
    (h : D.Present x z) : D.Present z x :=
  ⟨h.2.1, h.1, adjacent_symm h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem present_neighbour {G : Finset Plane} (D : Network G) {x z : Plane}
    (h : D.Present x z) : z ∈ D.presentNeighbours x :=
  Finset.mem_filter.mpr ⟨adjacent_neighbour h.2.2.1, h⟩

theorem leg_data {G : Finset Plane} {e : Plane × Plane} (h : e ∈ originalLegs G) :
    e.1 ∈ G ∧ e.2 ∈ neighbours e.1 ∧ e.2 ∉ G := by
  obtain ⟨x,hx,h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
  cases he
  exact ⟨hx, (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩

theorem leg_protected {G : Finset Plane} (e : originalLegs G) :
    e.val.1 ∈ protectedSites G := by
  obtain ⟨hx,hz,hout⟩ := leg_data e.property
  apply Finset.mem_filter.mpr
  refine ⟨hx, ?_⟩
  have hdist : boundaryDepth G e.val.1 ≤ (1 : ℕ∞) := by
    unfold boundaryDepth setDistance
    calc
      _ ≤ (latticeDist e.val.1 e.val.2 : ℕ∞) :=
        iInf_le_of_le ⟨e.val.2, hout⟩ le_rfl
      _ = 1 := by rw [show latticeDist e.val.1 e.val.2 = 1 from neighbour_adjacent hz]; rfl
  exact hdist.trans (by norm_num)

theorem leg_count {G : Finset Plane} (x : Plane) :
    ((originalLegs G).filter fun e => e.1 = x).card ≤ 4 := by
  let s := (originalLegs G).filter fun e => e.1 = x
  calc
    s.card ≤ (neighbours x).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro e he
        obtain ⟨he,hx⟩ := Finset.mem_filter.mp he
        change e.2 ∈ neighbours x
        simpa only [hx] using (leg_data he).2.1
      · intro e he f hf hef
        apply Prod.ext
        · exact (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
        · exact hef
    _ ≤ (Finset.univ : Finset Compass).card := Finset.card_image_le
    _ = 4 := by decide

theorem bonds_data {G : Finset Plane} {e : Plane × Plane} (h : e ∈ internalBonds G) :
    e.1 ∈ G ∧ e.2 ∈ positiveNeighbours e.1 ∧ e.2 ∈ G := by
  obtain ⟨x,hx,h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
  cases he
  exact ⟨hx, (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩

theorem bond_orientation_unique {G : Finset Plane} {e f : Plane × Plane}
    (he : e ∈ internalBonds G) (hf : f ∈ internalBonds G)
    (h : (e.1 = f.1 ∧ e.2 = f.2) ∨ (e.1 = f.2 ∧ e.2 = f.1)) : e = f := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext h1 h2
  · have he := (bonds_data he).2.1
    have hf := (bonds_data hf).2.1
    simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at he hf
    rw [h1,h2] at he
    rcases he with he | he <;> rcases hf with hf | hf
    all_goals
      have ha := congrArg (fun p : Plane => p.1) he
      have hb := congrArg (fun p : Plane => p.2) he
      have hc := congrArg (fun p : Plane => p.1) hf
      have hd := congrArg (fun p : Plane => p.2) hf
      dsimp only at ha hb hc hd
      omega

theorem present_bond {G : Finset Plane} (D : Network G) {y o : Plane}
    (h : D.Present y o) :
    ∃ e ∈ D.bonds, (e.1 = y ∧ e.2 = o) ∨ (e.1 = o ∧ e.2 = y) := by
  have hn := adjacent_neighbour h.2.2.1
  obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hn
  have hy : y ∈ G := (Finset.mem_filter.mp h.1).1
  have ho : o ∈ G := (Finset.mem_filter.mp h.2.1).1
  cases d
  all_goals simp only [Compass.step, Prod.add_def] at hd
  case east | north =>
    refine ⟨(y,o), Finset.mem_filter.mpr ⟨?_,h⟩, Or.inl ⟨rfl,rfl⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨y,hy,Finset.mem_image.mpr ⟨o,Finset.mem_inter.mpr ⟨?_,ho⟩,rfl⟩⟩
    simp [positiveNeighbours, ← hd]
  case west | south =>
    refine ⟨(o,y), Finset.mem_filter.mpr ⟨?_,present_symm D h⟩, Or.inr ⟨rfl,rfl⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨o,ho,Finset.mem_image.mpr ⟨y,Finset.mem_inter.mpr ⟨?_,hy⟩,rfl⟩⟩
    simp [positiveNeighbours, ← hd, Prod.ext_iff]

end AKLT.W.REC014
