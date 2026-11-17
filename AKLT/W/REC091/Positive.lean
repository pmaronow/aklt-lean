import AKLT.W.REC091.Spin

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC091

theorem hemisphere_avoid {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4)
    (b : ι → Vec3) (hb : ∀ i, normSq (b i) ≤ 1) :
    ∃ j : Fin 3 × Fin 2, ∀ i, 0 < 1 + dot (icoVector (hemisphereLetter j)) (b i) := by
  classical
  by_contra hn
  push Not at hn
  choose bad hbad using hn
  have heq (j : Fin 3 × Fin 2) : icoVector (hemisphereLetter j) = - b (bad j) := by
    have hd := (dot_bounds (ico_unit (hemisphereLetter j)).le (hb (bad j))).1
    exact eq_neg_of_dot_eq_neg_one (ico_unit _).le (hb _) (by linarith [hbad j])
  have hinj : Function.Injective bad := by
    intro i j hij
    apply hemisphere_injective
    change icoVector (hemisphereLetter i) = icoVector (hemisphereLetter j)
    rw [heq i, heq j, hij]
  have hc := Fintype.card_le_of_injective bad hinj
  norm_num [Fintype.card_prod] at hc
  omega

theorem originalLeg_neighbour {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.2 ∈ neighbours e.1 := by
  obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hx
  subst e
  exact (Finset.mem_sdiff.mp hz).1

/-- No site of the square lattice has more than four original legs. -/
theorem originalLegs_at_card (G : Finset Plane) (x : Plane) :
    ((originalLegs G).filter fun e => e.1 = x).card ≤ 4 := by
  classical
  let L := (originalLegs G).filter fun e => e.1 = x
  have hinj : Set.InjOn (fun e : Plane × Plane => e.2) L := by
    intro a ha b hb hab
    apply Prod.ext
    · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    · exact hab
  have hsub : L.image (fun e => e.2) ⊆ neighbours x := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    have hl := Finset.mem_filter.mp he
    rw [← hl.2]
    exact originalLeg_neighbour hl.1
  calc
    L.card = (L.image fun e => e.2).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (neighbours x).card := Finset.card_le_card hsub
    _ ≤ 4 := by
      unfold neighbours
      exact (Finset.card_image_le).trans (by decide)

theorem network_spins_ball {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spin_ball _
  · norm_num [normSq, dot]

/-- The summand of the frozen network partition, before inserting an observable. -/
def networkWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

theorem partition_eq_sum_weight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ n, networkWeight D τ b n * f (D.spins n) := by
  unfold Network.partition networkWeight
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem networkWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : 0 ≤ networkWeight D τ b n := by
  unfold networkWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg (fun x _ => spinWeight_nonneg _ _)
    · apply Finset.prod_nonneg
      intro e _
      have h := (dot_bounds (network_spins_ball D n e.1)
        (network_spins_ball D n e.2)).1
      linarith
  · apply Finset.prod_nonneg
    intro e _
    split_ifs
    · have h := (dot_bounds (τ e).property.le (network_spins_ball D n e.val.1)).1
      linarith
    · norm_num

theorem network_partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  rw [partition_eq_sum_weight]
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (networkWeight_nonneg D τ b n) zero_le_one)

/-- Positivity for every frozen Network, without extra consistency assumptions.
Choose a common open hemisphere to make all bonds positive, and at each site
avoid its at most four original pin antipodes. -/
theorem network_partition_pos {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : 0 < D.partition τ b (fun _ => 1) := by
  classical
  let L (x : Plane) := (originalLegs G).filter fun e => e.1 = x
  have hex (x : D.active) : ∃ j : Fin 3 × Fin 2,
      ∀ e : L x.val, 0 < 1 + dot (icoVector (hemisphereLetter j))
        (τ ⟨e.val, (Finset.mem_filter.mp e.property).1⟩).val := by
    apply hemisphere_avoid
    · simpa only [Fintype.card_coe] using originalLegs_at_card G x.val
    · intro e
      exact (τ ⟨e.val, (Finset.mem_filter.mp e.property).1⟩).property.le
  choose choice hchoice using hex
  let n : (x : D.active) → SpinLetter := fun x => some (hemisphereLetter (choice x))
  have hsp (x : Plane) (hx : x ∈ D.active) :
      D.spins n x = icoVector (hemisphereLetter (choice ⟨x, hx⟩)) := by
    simp only [Network.spins, dite_eq_left hx, n, spinVector]
  have hweight : 0 < networkWeight D τ b n := by
    unfold networkWeight
    apply mul_pos
    · apply mul_pos
      · apply Finset.prod_pos
        intro x _
        exact spinWeight_some_pos (Finset.mem_filter.mp x.property).2 _
      · apply Finset.prod_pos
        intro e he
        have hp := (Finset.mem_filter.mp he).2
        rw [hsp e.1 hp.1, hsp e.2 hp.2.1]
        exact hemisphere_bond_pos _ _
    · apply Finset.prod_pos
      intro e _
      split_ifs with he
      · rw [hsp e.val.1 he.2, dot_comm]
        exact hchoice ⟨e.val.1, he.2⟩
          ⟨e.val, Finset.mem_filter.mpr ⟨e.property, rfl⟩⟩
      · norm_num
  rw [partition_eq_sum_weight]
  apply Finset.sum_pos'
  · intro n _
    exact mul_nonneg (networkWeight_nonneg D τ b n) zero_le_one
  · exact ⟨n, Finset.mem_univ _, by simpa using hweight⟩

/-- Every canonical removed pair mean is between -1 and 1. -/
theorem removedPairMean_bounds {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y f g : Plane) :
    -1 ≤ removedPairMean D τ b y f g ∧ removedPairMean D τ b y f g ≤ 1 := by
  let E := removeSite D y
  have hp := network_partition_pos E τ b
  have hlo : - E.partition τ b (fun _ => 1) ≤
      E.partition τ b (fun n => dot (n f) (n g)) := by
    rw [partition_eq_sum_weight, partition_eq_sum_weight, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro n _
    have h := (dot_bounds (network_spins_ball E n f) (network_spins_ball E n g)).1
    have hw := networkWeight_nonneg E τ b n
    nlinarith
  have hhi : E.partition τ b (fun n => dot (n f) (n g)) ≤
      E.partition τ b (fun _ => 1) := by
    rw [partition_eq_sum_weight, partition_eq_sum_weight]
    apply Finset.sum_le_sum
    intro n _
    exact mul_le_mul_of_nonneg_left
      (dot_bounds (network_spins_ball E n f) (network_spins_ball E n g)).2
      (networkWeight_nonneg E τ b n)
  change -1 ≤ E.partition τ b (fun n => dot (n f) (n g)) /
      E.partition τ b (fun _ => 1) ∧
    E.partition τ b (fun n => dot (n f) (n g)) / E.partition τ b (fun _ => 1) ≤ 1
  constructor
  · exact (le_div_iff₀ hp).mpr (by simpa using hlo)
  · exact (div_le_iff₀ hp).mpr (by simpa using hhi)

theorem responseJ_pos {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y f g : Plane) : 0 < responseJ D τ b y f g := by
  have h := (removedPairMean_bounds D τ b y f g).1
  unfold responseJ
  linarith

end AKLT.W.REC091
