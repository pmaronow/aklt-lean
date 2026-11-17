module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN053

open AKLT.Blueprint.Win

private def incidentBonds (D : Finset Plane) (z : Plane) : Finset (Plane × Plane) :=
  (internalBonds D).filter fun e => e.1 = z ∨ e.2 = z

private def otherEndpoint (z : Plane) (e : Plane × Plane) : Plane :=
  if e.1 = z then e.2 else e.1

private def patchConfig {D V : Finset Plane} (hVD : V ⊆ D)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) : PlaneConfiguration D :=
  fun z => if hz : z.val ∈ V then a ⟨z.val, hz⟩ else σ z

private def localField (D : Finset Plane) (z : Plane)
    (σ : PlaneConfiguration D) (j : Fin (incidentBonds D z).card) : Vec3 :=
  extendIcoSpins σ (otherEndpoint z ((incidentBonds D z).equivFin.symm j).val)

private def localWeight (D : Finset Plane) (z : Plane)
    (σ : PlaneConfiguration D) (l : IcoLetter) : ℝ :=
  (1 / 12 : ℝ) * localProduct (localField D z σ) (icoVector l)

private def touchedBonds (D V : Finset Plane) : Finset (Plane × Plane) :=
  (internalBonds D).filter fun e => e.1 ∈ V ∨ e.2 ∈ V

private def restBonds (D V : Finset Plane) : Finset (Plane × Plane) :=
  (internalBonds D).filter fun e => e.1 ∉ V ∧ e.2 ∉ V

private def untouchedBonds (D V : Finset Plane) : Finset (Plane × Plane) :=
  (internalBonds D).filter fun e => ¬(e.1 ∈ V ∨ e.2 ∈ V)

private def edgeFactor {D : Finset Plane} (σ : PlaneConfiguration D) (e : Plane × Plane) : ℝ :=
  1 + dot (extendIcoSpins σ e.1) (extendIcoSpins σ e.2)

private def bondProduct {D : Finset Plane} (σ : PlaneConfiguration D) : ℝ :=
  ∏ e ∈ internalBonds D, edgeFactor σ e

private theorem latticeDist_triangle (a b c : Plane) :
    latticeDist a c ≤ latticeDist a b + latticeDist b c := by
  unfold latticeDist
  have hx : (a.1 - c.1).natAbs ≤ (a.1 - b.1).natAbs + (b.1 - c.1).natAbs := by
    calc
      (a.1 - c.1).natAbs = ((a.1 - b.1) + (b.1 - c.1)).natAbs := by congr 1 <;> omega
      _ ≤ _ := Int.natAbs_add_le _ _
  have hy : (a.2 - c.2).natAbs ≤ (a.2 - b.2).natAbs + (b.2 - c.2).natAbs := by
    calc
      (a.2 - c.2).natAbs = ((a.2 - b.2) + (b.2 - c.2)).natAbs := by congr 1 <;> omega
      _ ≤ _ := Int.natAbs_add_le _ _
  omega

private theorem neighbor_eq_step {x z : Plane} (hz : z ∈ neighbours x) :
    ∃ d : Compass, z = x + d.step := by
  unfold neighbours at hz
  rcases Finset.mem_image.mp hz with ⟨d, -, rfl⟩
  exact ⟨d, rfl⟩

private theorem neighbor_adjacent {x z : Plane} (hz : z ∈ neighbours x) : Adjacent x z := by
  obtain ⟨d, rfl⟩ := neighbor_eq_step hz
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

private theorem adjacent_neighbor {x z : Plane} (h : Adjacent x z) : z ∈ neighbours x := by
  unfold Adjacent latticeDist at h
  have hs : (x.1 - z.1).natAbs = 1 ∧ (x.2 - z.2).natAbs = 0 ∨
      (x.1 - z.1).natAbs = 0 ∧ (x.2 - z.2).natAbs = 1 := by omega
  rcases hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hx' : x.1 - z.1 = 1 ∨ x.1 - z.1 = -1 := by
      simpa using (Int.natAbs_eq_iff.mp hx)
    have hy' : x.2 - z.2 = 0 := Int.natAbs_eq_zero.mp hy
    rcases hx' with hx' | hx'
    · have hz : z = x + Compass.west.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      rw [hz]
      unfold neighbours
      exact Finset.mem_image.mpr ⟨Compass.west, Finset.mem_univ _, rfl⟩
    · have hz : z = x + Compass.east.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      rw [hz]
      unfold neighbours
      exact Finset.mem_image.mpr ⟨Compass.east, Finset.mem_univ _, rfl⟩
  · have hx' : x.1 - z.1 = 0 := Int.natAbs_eq_zero.mp hx
    have hy' : x.2 - z.2 = 1 ∨ x.2 - z.2 = -1 := by
      simpa using (Int.natAbs_eq_iff.mp hy)
    rcases hy' with hy' | hy'
    · have hz : z = x + Compass.south.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      rw [hz]
      unfold neighbours
      exact Finset.mem_image.mpr ⟨Compass.south, Finset.mem_univ _, rfl⟩
    · have hz : z = x + Compass.north.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      rw [hz]
      unfold neighbours
      exact Finset.mem_image.mpr ⟨Compass.north, Finset.mem_univ _, rfl⟩

private theorem adjacent_symmetric {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have hn : y ∈ neighbours x := adjacent_neighbor h
  obtain ⟨d, rfl⟩ := neighbor_eq_step hn
  have hr : x ∈ neighbours (x + d.step) := by
    unfold neighbours
    cases d with
    | east => exact Finset.mem_image.mpr ⟨Compass.west, Finset.mem_univ _, by
        ext <;> simp [Compass.step]⟩
    | north => exact Finset.mem_image.mpr ⟨Compass.south, Finset.mem_univ _, by
        ext <;> simp [Compass.step]⟩
    | west => exact Finset.mem_image.mpr ⟨Compass.east, Finset.mem_univ _, by
        ext <;> simp [Compass.step]⟩
    | south => exact Finset.mem_image.mpr ⟨Compass.north, Finset.mem_univ _, by
        ext <;> simp [Compass.step]⟩
  exact neighbor_adjacent hr

private theorem internalBond_orientation {D : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds D) :
    e.1.1 < e.2.1 ∨ (e.1.1 = e.2.1 ∧ e.1.2 < e.2.2) := by
  unfold internalBonds at he
  rcases Finset.mem_biUnion.mp he with ⟨u, hu, hb⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, rfl⟩
  have hp := (Finset.mem_inter.mp hv).1
  simp [positiveNeighbours] at hp
  change u.1 < v.1 ∨ (u.1 = v.1 ∧ u.2 < v.2)
  rcases hp with hp | hp
  · rcases Prod.mk.inj hp with ⟨hpx, hpy⟩
    omega
  · rcases Prod.mk.inj hp with ⟨hpx, hpy⟩
    omega

private theorem internalBond_adjacent {D : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds D) : Adjacent e.1 e.2 := by
  unfold internalBonds at he
  rcases Finset.mem_biUnion.mp he with ⟨u, hu, hb⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, heq⟩
  have hu' : u = e.1 := congrArg Prod.fst heq
  have hv' : v = e.2 := congrArg Prod.snd heq
  have hp : e.2 ∈ positiveNeighbours e.1 := by
    have hp := (Finset.mem_inter.mp hv).1
    simpa [hu', hv'] using hp
  simp [positiveNeighbours, Adjacent, latticeDist] at hp ⊢
  rcases hp with hp | hp <;> simp_all

private theorem internalBond_reverse_false {D : Finset Plane} {z q : Plane}
    (hzq : (z, q) ∈ internalBonds D) (hqz : (q, z) ∈ internalBonds D) : False := by
  have h₁ := internalBond_orientation hzq
  have h₂ := internalBond_orientation hqz
  change z.1 < q.1 ∨ (z.1 = q.1 ∧ z.2 < q.2) at h₁
  change q.1 < z.1 ∨ (q.1 = z.1 ∧ q.2 < z.2) at h₂
  rcases h₁ with h₁ | ⟨h₁x, h₁y⟩ <;>
    rcases h₂ with h₂ | ⟨h₂x, h₂y⟩ <;> omega

private theorem incident_other_neighbor {D : Finset Plane} {z : Plane}
    {e : Plane × Plane} (he : e ∈ incidentBonds D z) :
    otherEndpoint z e ∈ neighbours z := by
  have he' : e ∈ internalBonds D := (Finset.mem_filter.mp he).1
  have ht := (Finset.mem_filter.mp he).2
  by_cases hs : e.1 = z
  · simp [otherEndpoint, hs]
    exact adjacent_neighbor (by simpa [hs] using internalBond_adjacent he')
  · have ht' : e.2 = z := ht.resolve_left hs
    simp [otherEndpoint, hs]
    have hadj : Adjacent z e.1 := by
      rw [← ht']
      exact adjacent_symmetric (internalBond_adjacent he')
    exact adjacent_neighbor hadj

private theorem incident_other_mem {D : Finset Plane} {z : Plane}
    {e : Plane × Plane} (he : e ∈ incidentBonds D z) : otherEndpoint z e ∈ D := by
  have he' : e ∈ internalBonds D := (Finset.mem_filter.mp he).1
  unfold internalBonds at he'
  rcases Finset.mem_biUnion.mp he' with ⟨u, hu, hb⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, heq⟩
  have h₁ : u = e.1 := congrArg Prod.fst heq
  have h₂ : v = e.2 := congrArg Prod.snd heq
  have hvD : v ∈ D := (Finset.mem_inter.mp hv).2
  by_cases hs : e.1 = z
  · simpa [otherEndpoint, hs, h₂] using hvD
  · have ht : e.2 = z := (Finset.mem_filter.mp he).2.resolve_left hs
    simpa [otherEndpoint, hs, h₁, ht] using hu

private theorem incident_other_injective {D : Finset Plane} {z : Plane}
    {e f : Plane × Plane} (he : e ∈ incidentBonds D z) (hf : f ∈ incidentBonds D z)
    (hEq : otherEndpoint z e = otherEndpoint z f) : e = f := by
  have he' : e ∈ internalBonds D := (Finset.mem_filter.mp he).1
  have hf' : f ∈ internalBonds D := (Finset.mem_filter.mp hf).1
  have het := (Finset.mem_filter.mp he).2
  have hft := (Finset.mem_filter.mp hf).2
  by_cases hs : e.1 = z <;> by_cases ht : f.1 = z
  · have h₂ : e.2 = f.2 := by simpa [otherEndpoint, hs, ht] using hEq
    exact Prod.ext (hs.trans ht.symm) h₂
  · have h₂ : e.2 = f.1 := by simpa [otherEndpoint, hs, ht] using hEq
    have hev : (z, e.2) ∈ internalBonds D := by
      have heq : e = (z, e.2) := Prod.ext hs rfl
      rw [← heq]
      exact he'
    have hfv : (e.2, z) ∈ internalBonds D := by
      have hfz : f.2 = z := hft.resolve_left ht
      have heq : f = (e.2, z) := Prod.ext h₂.symm hfz
      rw [← heq]
      exact hf'
    exact False.elim (internalBond_reverse_false hev hfv)
  · have h₂ : e.1 = f.2 := by simpa [otherEndpoint, hs, ht] using hEq
    have hev : (z, e.1) ∈ internalBonds D := by
      have heq : f = (z, e.1) := Prod.ext ht h₂.symm
      rw [← heq]
      exact hf'
    have hfv : (e.1, z) ∈ internalBonds D := by
      have heq : e = (e.1, z) := Prod.ext rfl (het.resolve_left hs)
      rw [← heq]
      exact he'
    exact False.elim (internalBond_reverse_false hev hfv)
  · have h₁ : e.2 = z := het.resolve_left hs
    have h₂ : f.2 = z := hft.resolve_left ht
    have h₃ : e.1 = f.1 := by simpa [otherEndpoint, hs, ht] using hEq
    exact Prod.ext h₃ (h₁.trans h₂.symm)

private theorem neighbor_nonadjacent {x z w : Plane}
    (hz : z ∈ neighbours x) (hw : w ∈ neighbours x) (hzw : z ≠ w) :
    ¬ Adjacent z w := by
  obtain ⟨d, rfl⟩ := neighbor_eq_step hz
  obtain ⟨e, rfl⟩ := neighbor_eq_step hw
  have hde : d ≠ e := by
    intro h
    subst e
    exact hzw rfl
  cases d <;> cases e <;> simp_all [Compass.step, Adjacent, latticeDist]

private theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  unfold neighbours
  rw [Finset.card_image_of_injective _]
  · change Fintype.card Compass = 4
    decide
  · intro a b hab
    cases a <;> cases b <;> simp [Compass.step] at hab ⊢

private theorem depth_excludes_distance_le_two {G : Finset Plane} {x y : Plane}
    (hdepth : 3 ≤ boundaryDepth G x) (hxy : latticeDist x y ≤ 2) : y ∈ G := by
  by_contra hy
  have hle : boundaryDepth G x ≤ (latticeDist x y : ℕ∞) := by
    unfold boundaryDepth setDistance
    exact iInf_le (fun z : {z : Plane // z ∉ G} => (latticeDist x z.val : ℕ∞)) ⟨y, hy⟩
  have hle2 : boundaryDepth G x ≤ (2 : ℕ∞) := hle.trans (by exact_mod_cast hxy)
  have hgt : (2 : ℕ∞) < boundaryDepth G x := by
    exact lt_of_lt_of_le (by norm_num) hdepth
  exact (not_lt_of_ge hle2) hgt

private theorem survivors_subset (G Y : Finset Plane) (x : Plane) :
    survivors G Y x ⊆ G \ insert x Y := by
  intro z hz
  exact (Finset.mem_inter.mp hz).2

private theorem survivors_are_neighbours (G Y : Finset Plane) (x z : Plane)
    (hz : z ∈ survivors G Y x) : z ∈ neighbours x :=
  (Finset.mem_inter.mp hz).1

private theorem removal_x_not_live {G Y : Finset Plane} {x : Plane}
    (hstep : RemovalStep G Y x) : x ∉ G \ insert x Y := by
  simp [Finset.mem_sdiff]

private theorem incident_card_le_three {G Y : Finset Plane} {x z : Plane}
    (hstep : RemovalStep G Y x) (hz : z ∈ survivors G Y x) :
    (incidentBonds (G \ insert x Y) z).card ≤ 3 := by
  let D := G \ insert x Y
  let I := incidentBonds D z
  have hxD : x ∉ D := by
    dsimp [D]
    exact removal_x_not_live hstep
  have hxN : x ∈ neighbours z := by
    have hzN := survivors_are_neighbours G Y x z hz
    exact adjacent_neighbor (adjacent_symmetric (neighbor_adjacent hzN))
  have hmap : ∀ e : I.attach, otherEndpoint z e ∈ (neighbours z).erase x := by
    intro e
    apply Finset.mem_erase.mpr
    refine ⟨?_, incident_other_neighbor e.val.property⟩
    intro hEq
    exact hxD (hEq ▸ incident_other_mem e.val.property)
  have hinj : Function.Injective (fun e : I.attach =>
      (⟨otherEndpoint z e, hmap e⟩ : (neighbours z).erase x)) := by
    intro e f h
    apply Subtype.ext
    apply Subtype.ext
    exact incident_other_injective (z := z) (e := e.val.val) (f := f.val.val)
      e.val.property f.val.property (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective _ hinj
  have hsmall : ((neighbours z).erase x).card = 3 := by
    rw [Finset.card_erase_of_mem hxN, neighbours_card]
  simpa [I, Finset.card_attach, hsmall] using hcard

private theorem survivor_pair_not_adjacent {G Y : Finset Plane} {x z w : Plane}
    (hz : z ∈ survivors G Y x) (hw : w ∈ survivors G Y x) (hzw : z ≠ w) :
    ¬ Adjacent z w :=
  neighbor_nonadjacent (survivors_are_neighbours G Y x z hz)
    (survivors_are_neighbours G Y x w hw) hzw

private theorem incident_disjoint_of_not_adjacent {D : Finset Plane} {z w : Plane}
    (hzw : z ≠ w) (hn : ¬ Adjacent z w) :
    Disjoint (incidentBonds D z) (incidentBonds D w) := by
  rw [Finset.disjoint_left]
  intro e he hw
  have he' := (Finset.mem_filter.mp he).1
  have ht₁ := (Finset.mem_filter.mp he).2
  have ht₂ := (Finset.mem_filter.mp hw).2
  rcases ht₁ with hs₁ | ht₁ <;> rcases ht₂ with hs₂ | ht₂
  · exact False.elim (hzw (hs₁.symm.trans hs₂))
  · have hadj : Adjacent z w := by
      have h := internalBond_adjacent he'
      simpa [hs₁, ht₂] using h
    exact hn hadj
  · have hadj : Adjacent w z := by
      have h := internalBond_adjacent he'
      simpa [ht₁, hs₂] using h
    exact hn (adjacent_symmetric hadj)
  · exact False.elim (hzw (ht₁.symm.trans ht₂))

private theorem localField_normSq_le_one
    (hMom : AKLT.Blueprint.Top.MomentsStatement) {D : Finset Plane} {z : Plane}
    (σ : PlaneConfiguration D) (j : Fin (incidentBonds D z).card) :
    normSq (localField D z σ j) ≤ 1 := by
  have hmem := incident_other_mem ((incidentBonds D z).equivFin.symm j).property
  simp [localField, extendIcoSpins, hmem, hMom.2.1]

private theorem localWeight_is_uProduct {D : Finset Plane} {z : Plane}
    (σ : PlaneConfiguration D) (l : IcoLetter) :
    localWeight D z σ l = (1 / 12 : ℝ) *
      localProduct (localField D z σ) (icoVector l) := rfl

private theorem siteFunctional_localWeight {D : Finset Plane} {z : Plane}
    (σ : PlaneConfiguration D) :
    siteFunctional .U (localProduct (localField D z σ)) =
      ∑ l : IcoLetter, localWeight D z σ l := by
  simp [siteFunctional, spinWeight, spinVector, localWeight, localProduct, localField]

private theorem siteFunctional_localNumerator {D : Finset Plane} {z : Plane}
    (σ : PlaneConfiguration D) (i : Fin 3) :
    siteFunctional .U (fun n => n i * localProduct (localField D z σ) n) =
      ∑ l : IcoLetter, localWeight D z σ l * icoVector l i := by
  simp [siteFunctional, spinWeight, spinVector, localWeight, localProduct, localField,
    mul_comm, mul_left_comm, mul_assoc]

private theorem localWeight_facts
    (hMean : AKLT.Blueprint.Top.ThreeFactorMeanStatement)
    (hMom : AKLT.Blueprint.Top.MomentsStatement) {D : Finset Plane} {z : Plane}
    (σ : PlaneConfiguration D) (hk : (incidentBonds D z).card ≤ 3) :
    0 < ∑ l : IcoLetter, localWeight D z σ l ∧
      normSq (fun i =>
        (∑ l : IcoLetter, localWeight D z σ l * icoVector l i) /
          (∑ l : IcoLetter, localWeight D z σ l)) ≤ (3 / 5 : ℝ)^2 := by
  let a := localField D z σ
  have ha : ∀ j, normSq (a j) ≤ 1 := by
    intro j
    exact localField_normSq_le_one hMom σ j
  have h := hMean.1 (incidentBonds D z).card hk a ha .U (Or.inl rfl)
  have hnorm := siteFunctional_localWeight (σ := σ) (z := z)
  have hnum := fun i => siteFunctional_localNumerator (σ := σ) (z := z) i
  have hlocal : localMean .U a = fun i =>
      (∑ l : IcoLetter, localWeight D z σ l * icoVector l i) /
        (∑ l : IcoLetter, localWeight D z σ l) := by
    funext i
    simp [localMean, a, hnum i, hnorm]
  refine ⟨?_, ?_⟩
  · rw [← hnorm]
    exact h.1
  · rw [← hlocal]
    exact h.2

private theorem patch_inside {D V : Finset Plane} (hVD : V ⊆ D)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) {z : D} (hz : z.val ∈ V) :
    patchConfig hVD a σ z = a ⟨z.val, hz⟩ := by
  simp [patchConfig, hz]

private theorem patch_outside {D V : Finset Plane} (hVD : V ⊆ D)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) {z : D} (hz : z.val ∉ V) :
    patchConfig hVD a σ z = σ z := by
  simp [patchConfig, hz]

private theorem internalBond_left_mem {D : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds D) : e.1 ∈ D := by
  unfold internalBonds at he
  rcases Finset.mem_biUnion.mp he with ⟨u, hu, hb⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, hpair⟩
  exact congrArg Prod.fst hpair ▸ hu

private theorem internalBond_right_mem {D : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds D) : e.2 ∈ D := by
  unfold internalBonds at he
  rcases Finset.mem_biUnion.mp he with ⟨u, hu, hb⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, hpair⟩
  exact congrArg Prod.snd hpair ▸ (Finset.mem_inter.mp hv).2

private theorem not_adj_self (z : Plane) : ¬ Adjacent z z := by
  simp [Adjacent, latticeDist]

private theorem touching_eq_biUnion {D V : Finset Plane} :
    touchedBonds D V = V.biUnion (incidentBonds D) := by
  ext e
  simp only [touchedBonds, incidentBonds, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro ⟨he, hs | ht⟩
    · exact ⟨e.1, hs, he, Or.inl rfl⟩
    · exact ⟨e.2, ht, he, Or.inr rfl⟩
  · rintro ⟨z, hz, he, hs | ht⟩
    · exact ⟨he, Or.inl (hs ▸ hz)⟩
    · exact ⟨he, Or.inr (ht ▸ hz)⟩

private theorem incident_pairwise_disjoint {D V : Finset Plane}
    (hInd : ∀ z ∈ V, ∀ w ∈ V, z ≠ w → ¬ Adjacent z w) :
    (↑V : Set Plane).PairwiseDisjoint (incidentBonds D) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro z hz w hw h
  change z ∈ V at hz
  change w ∈ V at hw
  by_contra hzw
  obtain ⟨e, he⟩ := h
  have hd : Disjoint (incidentBonds D z) (incidentBonds D w) :=
    incident_disjoint_of_not_adjacent (D := D) hzw (hInd z hz w hw hzw)
  have he₁ : e ∈ incidentBonds D z := (Finset.mem_inter.mp he).1
  have he₂ : e ∈ incidentBonds D w := (Finset.mem_inter.mp he).2
  exact (Finset.disjoint_left.mp hd) he₁ he₂

private theorem patch_extend_inside {D V : Finset Plane} (hVD : V ⊆ D)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) {z : Plane}
    (hz : z ∈ V) :
    extendIcoSpins (patchConfig hVD a σ) z = icoVector (a ⟨z, hz⟩) := by
  have hzD : z ∈ D := hVD hz
  simp [extendIcoSpins, patchConfig, hz, hzD]

private theorem patch_extend_outside {D V : Finset Plane} (hVD : V ⊆ D)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) {z : Plane}
    (hzD : z ∈ D) (hz : z ∉ V) :
    extendIcoSpins (patchConfig hVD a σ) z = extendIcoSpins σ z := by
  simp [extendIcoSpins, patchConfig, hzD, hz]

private theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem incident_other_not_V {D V : Finset Plane} {z : Plane}
    (hInd : ∀ z ∈ V, ∀ w ∈ V, z ≠ w → ¬ Adjacent z w) (hz : z ∈ V)
    {e : Plane × Plane} (he : e ∈ incidentBonds D z) : otherEndpoint z e ∉ V := by
  have he' : e ∈ internalBonds D := (Finset.mem_filter.mp he).1
  have ht := (Finset.mem_filter.mp he).2
  have hadj := internalBond_adjacent he'
  have hne : e.1 ≠ e.2 := by
    intro h
    exact not_adj_self e.1 (by simpa [h] using hadj)
  have hother : otherEndpoint z e ≠ z := by
    by_cases hs : e.1 = z
    · unfold otherEndpoint
      rw [if_pos hs]
      intro h
      exact hne (hs.trans h.symm)
    · have ht' : e.2 = z := ht.resolve_left hs
      unfold otherEndpoint
      rw [if_neg hs]
      intro h
      exact hne (h.trans ht'.symm)
  intro hV
  have hn := incident_other_neighbor he
  by_cases hEq : otherEndpoint z e = z
  · exact hother (hEq)
  · exact hInd z hz (otherEndpoint z e) hV (fun h => hEq h.symm) (neighbor_adjacent hn)

private theorem patch_edge_eq_local {D V : Finset Plane} (hVD : V ⊆ D)
    (hInd : ∀ z ∈ V, ∀ w ∈ V, z ≠ w → ¬ Adjacent z w)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) {z : Plane}
    (hz : z ∈ V) {e : Plane × Plane} (he : e ∈ incidentBonds D z) :
    edgeFactor (patchConfig hVD a σ) e =
      1 + dot (icoVector (a ⟨z, hz⟩)) (extendIcoSpins σ (otherEndpoint z e)) := by
  have heB : e ∈ internalBonds D := (Finset.mem_filter.mp he).1
  have heL := internalBond_left_mem heB
  have heR := internalBond_right_mem heB
  have htouch := (Finset.mem_filter.mp he).2
  have hnot := incident_other_not_V hInd hz he
  by_cases hs : e.1 = z
  · unfold edgeFactor
    rw [hs]
    have hout : e.2 ∉ V := by simpa [otherEndpoint, hs] using hnot
    rw [patch_extend_inside hVD a σ hz]
    rw [patch_extend_outside hVD a σ heR hout]
    simp [otherEndpoint, hs]
  · have ht : e.2 = z := htouch.resolve_left hs
    unfold edgeFactor
    rw [ht]
    have hout : e.1 ∉ V := by simpa [otherEndpoint, hs] using hnot
    rw [patch_extend_outside hVD a σ heL hout]
    rw [patch_extend_inside hVD a σ hz]
    rw [dot_comm]
    simp [otherEndpoint, hs]

private theorem incident_product_patch {D V : Finset Plane} (hVD : V ⊆ D)
    (hInd : ∀ z ∈ V, ∀ w ∈ V, z ≠ w → ¬ Adjacent z w)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) {z : Plane}
    (hz : z ∈ V) :
    (∏ e ∈ incidentBonds D z, edgeFactor (patchConfig hVD a σ) e) =
      localProduct (localField D z σ) (icoVector (a ⟨z, hz⟩)) := by
  let I := incidentBonds D z
  rw [← Finset.prod_coe_sort]
  calc
    (∏ e : I, edgeFactor (patchConfig hVD a σ) e) =
        ∏ j : Fin I.card, (1 + dot (icoVector (a ⟨z, hz⟩)) (localField D z σ j)) := by
      apply Fintype.prod_equiv I.equivFin
      intro e
      simpa [localField, I] using patch_edge_eq_local hVD hInd a σ hz e.property
    _ = localProduct (localField D z σ) (icoVector (a ⟨z, hz⟩)) := rfl

private theorem bondProduct_patch_factor {D V : Finset Plane} (hVD : V ⊆ D)
    (hInd : ∀ z ∈ V, ∀ w ∈ V, z ≠ w → ¬ Adjacent z w)
    (a : PlaneConfiguration V) (σ : PlaneConfiguration D) :
    bondProduct (patchConfig hVD a σ) =
      (∏ e ∈ restBonds D V, edgeFactor σ e) *
      ∏ z : V, localProduct (localField D z.val σ) (icoVector (a z)) := by
  have hsplit : bondProduct (patchConfig hVD a σ) =
      (∏ e ∈ touchedBonds D V, edgeFactor (patchConfig hVD a σ) e) *
        ∏ e ∈ untouchedBonds D V, edgeFactor (patchConfig hVD a σ) e := by
    unfold bondProduct touchedBonds untouchedBonds
    exact (Finset.prod_filter_mul_prod_filter_not (internalBonds D)
      (fun e => e.1 ∈ V ∨ e.2 ∈ V) (edgeFactor (patchConfig hVD a σ))).symm
  have htouched :
      (∏ e ∈ touchedBonds D V, edgeFactor (patchConfig hVD a σ) e) =
      ∏ z : V, localProduct (localField D z.val σ) (icoVector (a z)) := by
    rw [touching_eq_biUnion]
    rw [Finset.prod_biUnion (incident_pairwise_disjoint hInd)]
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro z hz
    exact incident_product_patch hVD hInd a σ z.property
  have hrest :
      (∏ e ∈ untouchedBonds D V, edgeFactor (patchConfig hVD a σ) e) =
      ∏ e ∈ restBonds D V, edgeFactor σ e := by
    apply Finset.prod_congr
    · ext e
      simp only [untouchedBonds, restBonds, Finset.mem_filter]
      tauto
    · intro e he
      have he' : e ∈ (internalBonds D).filter fun e => e.1 ∉ V ∧ e.2 ∉ V := by
        simpa [restBonds] using he
      have heB : e ∈ internalBonds D := (Finset.mem_filter.mp he').1
      have hnot := (Finset.mem_filter.mp he').2
      have h₁ : e.1 ∉ V := hnot.1
      have h₂ : e.2 ∉ V := hnot.2
      have hleft := patch_extend_outside hVD a σ (internalBond_left_mem heB) h₁
      have hright := patch_extend_outside hVD a σ (internalBond_right_mem heB) h₂
      simp [edgeFactor, hleft, hright]
  calc
    bondProduct (patchConfig hVD a σ) =
        (∏ e ∈ touchedBonds D V, edgeFactor (patchConfig hVD a σ) e) *
        ∏ e ∈ untouchedBonds D V, edgeFactor (patchConfig hVD a σ) e := hsplit
    _ = (∏ e ∈ restBonds D V, edgeFactor σ e) *
        ∏ z : V, localProduct (localField D z.val σ) (icoVector (a z)) := by
      rw [htouched, hrest]
      ac_rfl

private theorem survivor_originalLeg_source_false
    {G Y : Finset Plane} {x z : Plane} (hstep : RemovalStep G Y x)
    (hz : z ∈ survivors G Y x) {e : originalLegs G} (hsrc : e.val.1 = z) :
    False := by
  have hdepth := hstep.2.2
  have hzx := survivors_are_neighbours G Y x z hz
  have hmem : e.val ∈ originalLegs G := e.property
  unfold originalLegs at hmem
  rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, he⟩
  rcases Finset.mem_image.mp he with ⟨v, hv, heq⟩
  have hu' : u = z := by
    have := congrArg Prod.fst heq
    simpa [hsrc] using this
  have hv' : v = e.val.2 := by
    exact congrArg Prod.snd heq
  have hvN : v ∈ neighbours z := by
    have h := (Finset.mem_sdiff.mp hv).1
    simpa [hu'] using h
  have hvG : v ∉ G := by
    have h := (Finset.mem_sdiff.mp hv).2
    simpa [hu', hv'] using h
  have hdist : latticeDist x v ≤ 2 := by
    have h1 : latticeDist x z = 1 := neighbor_adjacent hzx
    have h2 : latticeDist z v = 1 := neighbor_adjacent hvN
    calc
      latticeDist x v ≤ latticeDist x z + latticeDist z v := latticeDist_triangle _ _ _
      _ = 2 := by omega
  exact hvG (depth_excludes_distance_le_two hdepth hdist)

private theorem localWeight_prod {D V : Finset Plane} (σ : PlaneConfiguration D)
    (a : PlaneConfiguration V) :
    (∏ z : V, localWeight D z.val σ (a z)) =
      (1 / 12 : ℝ) ^ V.card *
        ∏ z : V, localProduct (localField D z.val σ) (icoVector (a z)) := by
  simp [localWeight, Finset.prod_mul_distrib]

private theorem partWeight_cross
    {G Y : Finset Plane} {x : Plane} (hstep : RemovalStep G Y x)
    (pinned : Bool) (τ : PinAssignment G)
    (hInd : ∀ z ∈ survivors G Y x, ∀ w ∈ survivors G Y x, z ≠ w → ¬ Adjacent z w)
    (σ : PlaneConfiguration (G \ insert x Y))
    (a b : PlaneConfiguration (survivors G Y x)) :
    partWeight pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) a σ) *
        ∏ z : survivors G Y x,
          localWeight (G \ insert x Y) z.val σ (b z) =
      partWeight pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) b σ) *
        ∏ z : survivors G Y x,
          localWeight (G \ insert x Y) z.val σ (a z) := by
  let D := G \ insert x Y
  let V := survivors G Y x
  have hVD : V ⊆ D := by
    exact survivors_subset G Y x
  have hPins : ∀ c : PlaneConfiguration V,
      (∏ e ∈ (originalLegs G).attach, if pinned ∧ e.val.1 ∈ D then
        1 + dot (τ e).val (extendIcoSpins (patchConfig hVD c σ) e.val.1) else 1) =
      (∏ e ∈ (originalLegs G).attach, if pinned ∧ e.val.1 ∈ D then
        1 + dot (τ e).val (extendIcoSpins σ e.val.1) else 1) := by
    intro c
    apply Finset.prod_congr rfl
    intro e he
    by_cases hp : pinned ∧ e.val.1 ∈ D
    · have hsrc : e.val.1 ∉ V := by
        intro hsrc
        exact survivor_originalLeg_source_false hstep hsrc
          (e := e) rfl
      simp [hp, patch_extend_outside hVD c σ hp.2 hsrc]
    · simp [hp]
  have hWc (c : PlaneConfiguration V) :
      partWeight pinned G (insert x Y) τ (patchConfig hVD c σ) =
        ((12 : ℝ) ^ D.card)⁻¹ * bondProduct (patchConfig hVD c σ) *
          (∏ e : originalLegs G, if pinned ∧ e.val.1 ∈ D then
            1 + dot (τ e).val (extendIcoSpins σ e.val.1) else 1) := by
    dsimp [partWeight]
    have hp := hPins c
    dsimp [D] at hp
    rw [hp]
    simp [D, bondProduct, edgeFactor, Finset.mem_sdiff, Finset.mem_insert, mul_assoc]
  have hbA := bondProduct_patch_factor hVD hInd a σ
  have hbB := bondProduct_patch_factor hVD hInd b σ
  have hqA := localWeight_prod (D := D) (V := V) σ a
  have hqB := localWeight_prod (D := D) (V := V) σ b
  rw [hWc a, hWc b, hbA, hbB, hqA, hqB]
  ring

private theorem partLaw_cross
    {G Y : Finset Plane} {x : Plane} (hstep : RemovalStep G Y x)
    (pinned : Bool) (τ : PinAssignment G)
    (hInd : ∀ z ∈ survivors G Y x, ∀ w ∈ survivors G Y x, z ≠ w → ¬ Adjacent z w)
    (σ : PlaneConfiguration (G \ insert x Y))
    (a b : PlaneConfiguration (survivors G Y x)) :
    partLaw pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) a σ) *
        ∏ z : survivors G Y x,
          localWeight (G \ insert x Y) z.val σ (b z) =
      partLaw pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) b σ) *
        ∏ z : survivors G Y x,
          localWeight (G \ insert x Y) z.val σ (a z) := by
  let D := G \ insert x Y
  have hraw := partWeight_cross hstep pinned τ hInd σ a b
  unfold partLaw AKLT.Defs.normalize
  let Z := ∑ ω : PlaneConfiguration D, partWeight pinned G (insert x Y) τ ω
  calc
    (partWeight pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) a σ) / Z) *
        ∏ z : survivors G Y x, localWeight D z.val σ (b z) =
      (partWeight pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) a σ) *
        ∏ z : survivors G Y x, localWeight D z.val σ (b z)) / Z := by ring
    _ = (partWeight pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) b σ) *
        ∏ z : survivors G Y x, localWeight D z.val σ (a z)) / Z := by
      rw [hraw]
    _ = (partWeight pinned G (insert x Y) τ (patchConfig (survivors_subset G Y x) b σ) / Z) *
        ∏ z : survivors G Y x, localWeight D z.val σ (a z) := by ring

private def fibreEquiv {D V : Finset Plane} (hVD : V ⊆ D)
    (σ : PlaneConfiguration D) :
    {ω : PlaneConfiguration D // restEvent V σ ω} ≃ PlaneConfiguration V := by
  classical
  exact {
    toFun := fun ω z => ω.val ⟨z.val, hVD z.property⟩
    invFun := fun a => ⟨patchConfig hVD a σ, by
      intro z hz
      simp [patchConfig, hz]⟩
    left_inv := by
      intro ω
      apply Subtype.ext
      funext z
      by_cases hz : z.val ∈ V
      · simp [patchConfig, hz]
      · have hrest := ω.property z hz
        simp [patchConfig, hz, hrest]
    right_inv := by
      intro a
      funext z
      simp [patchConfig, z.property] }

private theorem fibre_sum_eq {D V : Finset Plane} (hVD : V ⊆ D)
    (σ : PlaneConfiguration D) [DecidablePred (restEvent V σ)]
    (f : PlaneConfiguration D → ℝ) :
    (∑ ω : PlaneConfiguration D, if restEvent V σ ω then f ω else 0) =
      ∑ a : PlaneConfiguration V, f (patchConfig hVD a σ) := by
  classical
  let P : PlaneConfiguration D → Prop := restEvent V σ
  have hsub :
      (∑ ω : {ω : PlaneConfiguration D // P ω}, f ω.val) =
        ∑ ω : PlaneConfiguration D, if P ω then f ω else 0 := by
    calc
      (∑ ω : {ω : PlaneConfiguration D // P ω}, f ω.val) =
          ∑ ω ∈ (Finset.univ.filter P), f ω := by
        symm
        exact Finset.sum_subtype (Finset.univ.filter P) (by intro ω; simp [P]) f
      _ = ∑ ω : PlaneConfiguration D, if P ω then f ω else 0 := by
        rw [Finset.sum_filter]
  calc
    (∑ ω : PlaneConfiguration D, if restEvent V σ ω then f ω else 0) =
        ∑ ω : {ω : PlaneConfiguration D // P ω}, f ω.val := hsub.symm
    _ = ∑ a : PlaneConfiguration V, f (patchConfig hVD a σ) := by
      symm
      apply Fintype.sum_equiv (fibreEquiv hVD σ).symm
      intro a
      rfl

private theorem productWeight_total {I : Type} [Fintype I] [DecidableEq I]
    (q : I → IcoLetter → ℝ) :
    (∑ a : I → IcoLetter, ∏ i, q i (a i)) =
      ∏ i, ∑ l : IcoLetter, q i l := by
  exact (Fintype.prod_sum q).symm

private theorem productWeight_single_sum {I : Type} [Fintype I] [DecidableEq I]
    (q : I → IcoLetter → ℝ) (z : I) (f : IcoLetter → ℝ) :
    (∑ a : I → IcoLetter, (∏ i, q i (a i)) * f (a z)) =
      (∑ l : IcoLetter, q z l * f l) *
        ∏ i ∈ Finset.univ.erase z, ∑ l : IcoLetter, q i l := by
  classical
  let r : I → IcoLetter → ℝ := fun i l => q i l * if i = z then f l else 1
  have hsum : ∀ a : I → IcoLetter,
      (∏ i, q i (a i)) * f (a z) = ∏ i, r i (a i) := by
    intro a
    symm
    change (∏ i, q i (a i) * (if i = z then f (a i) else 1)) = _
    rw [Finset.prod_mul_distrib]
    simp
  calc
    (∑ a : I → IcoLetter, (∏ i, q i (a i)) * f (a z)) =
        ∑ a : I → IcoLetter, ∏ i, r i (a i) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hsum a
    _ = ∏ i, ∑ l : IcoLetter, r i l := (Fintype.prod_sum r).symm
    _ = (∑ l : IcoLetter, q z l * f l) *
        ∏ i ∈ Finset.univ.erase z, ∑ l : IcoLetter, q i l := by
      let N := ∑ l : IcoLetter, q z l * f l
      let Z : I → ℝ := fun i => ∑ l : IcoLetter, q i l
      let R : I → ℝ := fun i => if i = z then N else Z i
      have hterms : ∀ i, (∑ l : IcoLetter, r i l) = R i := by
        intro i
        by_cases hi : i = z
        · subst i
          simp [r, R, N, Z]
        · simp [r, R, N, Z, hi]
      rw [Finset.prod_congr rfl (by intro i hi; exact hterms i)]
      have hp := Finset.prod_erase_mul (Finset.univ : Finset I) R (a := z) (by simp)
      have hrem :
          (∏ i ∈ Finset.univ.erase z, R i) =
            ∏ i ∈ Finset.univ.erase z, Z i := by
        apply Finset.prod_congr rfl
        intro i hi
        have hiz : i ≠ z := (Finset.mem_erase.mp hi).1
        simp [R, Z, hiz]
      calc
        (∏ i, R i) = (∏ i ∈ Finset.univ.erase z, R i) * R z := hp.symm
        _ = N * ∏ i ∈ Finset.univ.erase z, Z i := by
          rw [hrem]
          simp [R]
          ac_rfl

private theorem productWeight_pair_sum {I : Type} [Fintype I] [DecidableEq I]
    (q : I → IcoLetter → ℝ) (z w : I) (hzw : z ≠ w)
    (f g : IcoLetter → ℝ) :
    (∑ a : I → IcoLetter, (∏ i, q i (a i)) * f (a z) * g (a w)) =
      (∑ l : IcoLetter, q z l * f l) * (∑ l : IcoLetter, q w l * g l) *
        ∏ i ∈ (Finset.univ.erase z).erase w, ∑ l : IcoLetter, q i l := by
  classical
  let obs : I → IcoLetter → ℝ := fun i l =>
    if i = z then f l else if i = w then g l else 1
  let r : I → IcoLetter → ℝ := fun i l => q i l * obs i l
  let Nz : ℝ := ∑ l : IcoLetter, q z l * f l
  let Nw : ℝ := ∑ l : IcoLetter, q w l * g l
  let Z : I → ℝ := fun i => ∑ l : IcoLetter, q i l
  let R : I → ℝ := fun i => if i = z then Nz else if i = w then Nw else Z i
  have hobs : ∀ a : I → IcoLetter, (∏ i, obs i (a i)) = f (a z) * g (a w) := by
    intro a
    have hp := Finset.prod_erase_mul (Finset.univ : Finset I)
      (fun i => obs i (a i)) (a := z) (by simp)
    have hrem : (∏ i ∈ Finset.univ.erase z, obs i (a i)) = g (a w) := by
      have hcongr :
          (∏ i ∈ Finset.univ.erase z, obs i (a i)) =
            ∏ i ∈ Finset.univ.erase z, (if i = w then g (a i) else 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hiz : i ≠ z := (Finset.mem_erase.mp hi).1
        simp [obs, hiz]
      have hwmem : w ∈ Finset.univ.erase z := by
        apply Finset.mem_erase.mpr
        exact ⟨hzw.symm, Finset.mem_univ _⟩
      rw [hcongr, Finset.prod_ite_eq']
      simp [hwmem]
    calc
      (∏ i, obs i (a i)) =
          (∏ i ∈ Finset.univ.erase z, obs i (a i)) * obs z (a z) := hp.symm
      _ = g (a w) * f (a z) := by simp [hrem, obs, hzw]
      _ = f (a z) * g (a w) := by ring
  have hsum : ∀ a : I → IcoLetter,
      (∏ i, q i (a i)) * f (a z) * g (a w) = ∏ i, r i (a i) := by
    intro a
    calc
      (∏ i, q i (a i)) * f (a z) * g (a w) =
          (∏ i, q i (a i)) * (f (a z) * g (a w)) := by ring
      _ = (∏ i, q i (a i)) * (∏ i, obs i (a i)) := by rw [hobs a]
      _ = ∏ i, r i (a i) := by
        change (∏ i, q i (a i)) * (∏ i, obs i (a i)) = _
        rw [← Finset.prod_mul_distrib]
  have hterms : ∀ i, (∑ l : IcoLetter, r i l) = R i := by
    intro i
    by_cases hi : i = z
    · subst i
      simp [r, obs, Nz, Nw, Z, R, hzw]
    · by_cases hiw : i = w
      · subst i
        have hwz : w ≠ z := hzw.symm
        simp [r, obs, Nz, Nw, Z, R, hwz]
      · simp [r, obs, Nz, Nw, Z, R, hi, hiw]
  have hzwmem : w ∈ Finset.univ.erase z := by
    apply Finset.mem_erase.mpr
    exact ⟨hzw.symm, Finset.mem_univ _⟩
  have hpz := Finset.prod_erase_mul (Finset.univ : Finset I) R (a := z) (by simp)
  have hpw := Finset.prod_erase_mul (Finset.univ.erase z) R (a := w) hzwmem
  have hrem :
      (∏ i ∈ (Finset.univ.erase z).erase w, R i) =
        ∏ i ∈ (Finset.univ.erase z).erase w, Z i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiw : i ≠ w := (Finset.mem_erase.mp hi).1
    have hiz : i ≠ z := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp [R, Z, hiz, hiw]
  calc
    (∑ a : I → IcoLetter, (∏ i, q i (a i)) * f (a z) * g (a w)) =
        ∑ a : I → IcoLetter, ∏ i, r i (a i) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hsum a
    _ = ∏ i, ∑ l : IcoLetter, r i l := (Fintype.prod_sum r).symm
    _ = (∑ l : IcoLetter, q z l * f l) * (∑ l : IcoLetter, q w l * g l) *
        ∏ i ∈ (Finset.univ.erase z).erase w, ∑ l : IcoLetter, q i l := by
      rw [Finset.prod_congr rfl (by intro i hi; exact hterms i)]
      calc
        (∏ i, R i) = (∏ i ∈ Finset.univ.erase z, R i) * R z := hpz.symm
        _ = ((∏ i ∈ (Finset.univ.erase z).erase w, R i) * R w) * R z := by
          rw [← hpw]
        _ = Nz * Nw * ∏ i ∈ (Finset.univ.erase z).erase w, Z i := by
          rw [hrem]
          rw [show R z = Nz by simp [R, hzw], show R w = Nw by simp [R, hzw.symm]]
          ring

private theorem productWeight_total_pair_split {I : Type} [Fintype I] [DecidableEq I]
    (q : I → IcoLetter → ℝ) (z w : I) (hzw : z ≠ w) :
    (∑ a : I → IcoLetter, ∏ i, q i (a i)) =
      (∑ l : IcoLetter, q z l) * (∑ l : IcoLetter, q w l) *
        ∏ i ∈ (Finset.univ.erase z).erase w, ∑ l : IcoLetter, q i l := by
  classical
  rw [productWeight_total]
  let Z : I → ℝ := fun i => ∑ l : IcoLetter, q i l
  have hzwmem : w ∈ Finset.univ.erase z := by
    apply Finset.mem_erase.mpr
    exact ⟨hzw.symm, Finset.mem_univ _⟩
  have hpz := Finset.prod_erase_mul (Finset.univ : Finset I) Z (a := z) (by simp)
  have hpw := Finset.prod_erase_mul (Finset.univ.erase z) Z (a := w) hzwmem
  calc
    (∏ i, Z i) = (∏ i ∈ Finset.univ.erase z, Z i) * Z z := hpz.symm
    _ = ((∏ i ∈ (Finset.univ.erase z).erase w, Z i) * Z w) * Z z := by
      rw [← hpw]
    _ = Z z * Z w * ∏ i ∈ (Finset.univ.erase z).erase w, Z i := by ring

private theorem factorized_single_expectation {I : Type} [Fintype I] [DecidableEq I]
    (q : I → IcoLetter → ℝ) (z : I) (c : ℝ) (hc : c ≠ 0)
    (hq : ∀ i, 0 < ∑ l : IcoLetter, q i l) (f : IcoLetter → ℝ) :
    (∑ a : I → IcoLetter, c * (∏ i, q i (a i)) * f (a z)) /
      (c * ∏ i, ∑ l : IcoLetter, q i l) =
      (∑ l : IcoLetter, q z l * f l) / (∑ l : IcoLetter, q z l) := by
  classical
  let Z : I → ℝ := fun i => ∑ l : IcoLetter, q i l
  have hZz : Z z ≠ 0 := ne_of_gt (hq z)
  have hZrest : (∏ i ∈ Finset.univ.erase z, Z i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ne_of_gt (hq i)
  have hZall : (∏ i, Z i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ne_of_gt (hq i)
  have hprod : (∏ i, Z i) =
      (∏ i ∈ Finset.univ.erase z, Z i) * Z z :=
    (Finset.prod_erase_mul (Finset.univ : Finset I) Z (a := z) (by simp)).symm
  have hnum :
      (∑ a : I → IcoLetter, c * (∏ i, q i (a i)) * f (a z)) =
        c * ((∑ l : IcoLetter, q z l * f l) * ∏ i ∈ Finset.univ.erase z, Z i) := by
    calc
      _ = c * (∑ a : I → IcoLetter, (∏ i, q i (a i)) * f (a z)) := by
        calc
          _ = ∑ a : I → IcoLetter, c * ((∏ i, q i (a i)) * f (a z)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ = _ := by rw [productWeight_single_sum]
  rw [hnum, hprod]
  field_simp [Z, hc, hZz, hZrest]
  <;> ring

private theorem factorized_pair_expectation {I : Type} [Fintype I] [DecidableEq I]
    (q : I → IcoLetter → ℝ) (z w : I) (hzw : z ≠ w) (c : ℝ) (hc : c ≠ 0)
    (hq : ∀ i, 0 < ∑ l : IcoLetter, q i l)
    (f g : IcoLetter → ℝ) :
    (∑ a : I → IcoLetter,
        c * (∏ i, q i (a i)) * f (a z) * g (a w)) /
      (c * ∏ i, ∑ l : IcoLetter, q i l) =
      ((∑ l : IcoLetter, q z l * f l) * (∑ l : IcoLetter, q w l * g l)) /
        ((∑ l : IcoLetter, q z l) * (∑ l : IcoLetter, q w l)) := by
  classical
  let Z : I → ℝ := fun i => ∑ l : IcoLetter, q i l
  have hZz : Z z ≠ 0 := ne_of_gt (hq z)
  have hZw : Z w ≠ 0 := ne_of_gt (hq w)
  have hZrest :
      (∏ i ∈ (Finset.univ.erase z).erase w, Z i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ne_of_gt (hq i)
  have hZall : (∏ i, Z i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact ne_of_gt (hq i)
  have hprod : (∏ i, Z i) =
      Z z * Z w * ∏ i ∈ (Finset.univ.erase z).erase w, Z i := by
    calc
      (∏ i, Z i) = ∑ a : I → IcoLetter, ∏ i, q i (a i) :=
        (productWeight_total q).symm
      _ = _ := by
        simpa [Z] using productWeight_total_pair_split q z w hzw
  have hnum :
      (∑ a : I → IcoLetter,
        c * (∏ i, q i (a i)) * f (a z) * g (a w)) =
        c * ((∑ l : IcoLetter, q z l * f l) * (∑ l : IcoLetter, q w l * g l) *
          ∏ i ∈ (Finset.univ.erase z).erase w, Z i) := by
    calc
      _ = c * (∑ a : I → IcoLetter,
          (∏ i, q i (a i)) * f (a z) * g (a w)) := by
        calc
          _ = ∑ a : I → IcoLetter,
              c * ((∏ i, q i (a i)) * f (a z) * g (a w)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ = _ := by rw [productWeight_pair_sum q z w hzw f g]
  rw [hnum, hprod]
  field_simp [Z, hc, hZz, hZw, hZrest]
  <;> ring

theorem main : AKLT.Blueprint.Win.NeighbourFibresStatement := by
  intro hMom hThree G Y τ x hstep pinned
  classical
  intro σ hMass
  let D := G \ insert x Y
  let V := survivors G Y x
  have hVD : V ⊆ D := survivors_subset G Y x
  have hInd : ∀ z ∈ V, ∀ w ∈ V, z ≠ w → ¬ Adjacent z w := by
    intro z hz w hw hzw
    exact survivor_pair_not_adjacent hz hw hzw
  let patch : PlaneConfiguration V → PlaneConfiguration D :=
    fun a => patchConfig hVD a σ
  let p : Weight (PlaneConfiguration D) := partLaw pinned G (insert x Y) τ
  let q : V → IcoLetter → ℝ := fun z l => localWeight D z.val σ l
  have hq : ∀ z : V, 0 < ∑ l : IcoLetter, q z l := by
    intro z
    exact (localWeight_facts hThree hMom σ
      (incident_card_le_three hstep z.property)).1
  have hqNonzero : ∀ z : V, ∃ l : IcoLetter, q z l ≠ 0 := by
    intro z
    by_contra hn
    push_neg at hn
    have hs : (∑ l : IcoLetter, q z l) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      exact hn l
    linarith [hq z]
  let a0 : PlaneConfiguration V := fun z => Classical.choose (hqNonzero z)
  have ha0 : ∀ z : V, q z (a0 z) ≠ 0 := by
    intro z
    exact Classical.choose_spec (hqNonzero z)
  let Q : PlaneConfiguration V → ℝ := fun a => ∏ z : V, q z (a z)
  have hQ0 : Q a0 ≠ 0 := by
    dsimp [Q]
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    exact ha0 z
  let c : ℝ := p (patch a0) / Q a0
  have hcross (a b : PlaneConfiguration V) :
      p (patch a) * Q b = p (patch b) * Q a := by
    have hh := partLaw_cross hstep pinned τ hInd σ a b
    simpa [p, patch, Q, q, D, V] using hh
  have hFactor (a : PlaneConfiguration V) : p (patch a) = c * Q a := by
    have hh := hcross a a0
    dsimp [c]
    calc
      p (patch a) = (p (patch a) * Q a0) / Q a0 := by
        field_simp [hQ0]
      _ = (p (patch a0) * Q a) / Q a0 := by rw [hh]
      _ = (p (patch a0) / Q a0) * Q a := by ring
  have hMassReindex : eventMass p (restEvent V σ) =
      ∑ a : PlaneConfiguration V, p (patch a) := by
    unfold eventMass
    rw [fibre_sum_eq hVD σ (fun ω => p ω)]
  have hMassFactor : eventMass p (restEvent V σ) =
      c * ∏ z : V, ∑ l : IcoLetter, q z l := by
    rw [hMassReindex]
    calc
      (∑ a : PlaneConfiguration V, p (patch a)) =
          ∑ a : PlaneConfiguration V, c * Q a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hFactor]
      _ = c * ∑ a : PlaneConfiguration V, Q a := by rw [Finset.mul_sum]
      _ = c * ∏ z : V, ∑ l : IcoLetter, q z l := by
        simp only [Q]
        rw [productWeight_total]
  have hc : c ≠ 0 := by
    intro hcz
    have hzprod : 0 < ∏ z : V, ∑ l : IcoLetter, q z l :=
      Finset.prod_pos (fun z hz => hq z)
    rw [hMassFactor, hcz] at hMass
    simp at hMass
  have hmean (z : V) :
      fibreSpinMean p V σ z.val = fun i : Fin 3 =>
        (∑ l : IcoLetter, q z l * icoVector l i) /
          (∑ l : IcoLetter, q z l) := by
    funext i
    unfold fibreSpinMean fibreMean
    have hnum :
        (∑ ω : PlaneConfiguration D,
          if restEvent V σ ω then
            p ω * extendIcoSpins ω z.val i else 0) =
          ∑ a : PlaneConfiguration V,
            c * (∏ u : V, q u (a u)) * icoVector (a z) i := by
      calc
        _ = ∑ a : PlaneConfiguration V,
            p (patch a) * extendIcoSpins (patch a) z.val i := by
          rw [fibre_sum_eq hVD σ (fun ω => p ω * extendIcoSpins ω z.val i)]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hFactor]
          have hzD : z.val ∈ D := hVD z.property
          have hspin : extendIcoSpins (patch a) z.val i = icoVector (a z) i := by
            simp [extendIcoSpins, patch, patchConfig, hzD, z.property]
          rw [hspin]
    change
      (∑ ω : PlaneConfiguration D,
        if restEvent V σ ω then
          p ω * extendIcoSpins ω z.val i else 0) /
        eventMass p (restEvent V σ) = _
    rw [hnum, hMassFactor]
    exact factorized_single_expectation q z c hc hq (fun l => icoVector l i)
  refine ⟨?_, ?_⟩
  · intro z hz
    have hzV : z ∈ V := hz
    let z' : V := ⟨z, hzV⟩
    have hlocal := localWeight_facts hThree hMom σ
      (incident_card_le_three hstep hzV)
    rw [hmean z']
    simpa [q, z'] using hlocal.2
  · intro z hz w hw hzw
    let z' : V := ⟨z, hz⟩
    let w' : V := ⟨w, hw⟩
    have hneq : z' ≠ w' := by
      intro he
      exact hzw (congrArg Subtype.val he)
    have hpair :
        fibreMean p V σ (fun ω => dot (extendIcoSpins ω z) (extendIcoSpins ω w)) =
          dot (fibreSpinMean p V σ z) (fibreSpinMean p V σ w) := by
      -- The product fibre separates the two site observables coordinate by coordinate.
      unfold fibreMean
      have hnum :
          (∑ ω : PlaneConfiguration D,
            if restEvent V σ ω then
              p ω * dot (extendIcoSpins ω z) (extendIcoSpins ω w) else 0) =
            ∑ i : Fin 3, ∑ a : PlaneConfiguration V,
              c * (∏ u : V, q u (a u)) *
                icoVector (a z') i * icoVector (a w') i := by
        calc
          _ = ∑ a : PlaneConfiguration V,
              p (patch a) * dot (extendIcoSpins (patch a) z)
                (extendIcoSpins (patch a) w) := by
            rw [fibre_sum_eq hVD σ (fun ω =>
              p ω * dot (extendIcoSpins ω z) (extendIcoSpins ω w))]
          _ = _ := by
            calc
              (∑ a : PlaneConfiguration V,
                p (patch a) * dot (extendIcoSpins (patch a) z)
                  (extendIcoSpins (patch a) w)) =
                ∑ a : PlaneConfiguration V,
                  c * Q a * dot (icoVector (a z')) (icoVector (a w')) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [hFactor]
                have hzD : z ∈ D := hVD hz
                have hwD : w ∈ D := hVD hw
                have hpatchZ : patch a ⟨z, hzD⟩ = a z' := by
                  simpa [z'] using patch_inside hVD a σ (z := ⟨z, hzD⟩) hz
                have hpatchW : patch a ⟨w, hwD⟩ = a w' := by
                  simpa [w'] using patch_inside hVD a σ (z := ⟨w, hwD⟩) hw
                have hspinZ : extendIcoSpins (patch a) z = icoVector (a z') := by
                  simpa [extendIcoSpins, hzD] using congrArg icoVector hpatchZ
                have hspinW : extendIcoSpins (patch a) w = icoVector (a w') := by
                  simpa [extendIcoSpins, hwD] using congrArg icoVector hpatchW
                rw [hspinZ, hspinW]
              _ = ∑ i : Fin 3, ∑ a : PlaneConfiguration V,
                  c * (∏ u : V, q u (a u)) *
                    icoVector (a z') i * icoVector (a w') i := by
                simp only [dot, Q]
                calc
                  _ = ∑ a : PlaneConfiguration V, ∑ i : Fin 3,
                      (c * ∏ u : V, q u (a u)) *
                        icoVector (a z') i * icoVector (a w') i := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
                  _ = _ := by rw [Finset.sum_comm]
      change
        (∑ ω : PlaneConfiguration D,
          if restEvent V σ ω then
            p ω * dot (extendIcoSpins ω z) (extendIcoSpins ω w) else 0) /
          eventMass p (restEvent V σ) = _
      rw [hnum, hMassFactor]
      rw [dot, hmean z', hmean w']
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have hp := factorized_pair_expectation q z' w' hneq c hc hq
        (fun l => icoVector l i) (fun l => icoVector l i)
      have hqz : (∑ l : IcoLetter, q z' l) ≠ 0 := ne_of_gt (hq z')
      have hqw : (∑ l : IcoLetter, q w' l) ≠ 0 := ne_of_gt (hq w')
      calc
        (∑ a : PlaneConfiguration V,
          c * (∏ u : V, q u (a u)) * icoVector (a z') i * icoVector (a w') i) /
            (c * ∏ z : V, ∑ l : IcoLetter, q z l) =
            ((∑ l : IcoLetter, q z' l * icoVector l i) *
              (∑ l : IcoLetter, q w' l * icoVector l i)) /
                ((∑ l : IcoLetter, q z' l) * (∑ l : IcoLetter, q w' l)) := by
          exact hp
        _ = ((∑ l : IcoLetter, q z' l * icoVector l i) /
              (∑ l : IcoLetter, q z' l)) *
            ((∑ l : IcoLetter, q w' l * icoVector l i) /
              (∑ l : IcoLetter, q w' l)) := by
          field_simp [hqz, hqw]
    simpa [z', w'] using hpair

end AKLT.W.WIN053

#print axioms AKLT.W.WIN053.main
