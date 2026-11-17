module
public import AKLT.W.REC022.Sum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC022

variable {G : Finset Plane}

def otherEnd (y : Plane) (e : Plane × Plane) : Plane :=
  if e.1 = y then e.2 else e.1

theorem otherEnd_inj (D : Network G) (y : Plane) (e e' : Plane × Plane)
    (he : e ∈ D.bonds) (he' : e' ∈ D.bonds)
    (hi : e.1 = y ∨ e.2 = y) (hi' : e'.1 = y ∨ e'.2 = y)
    (hh : otherEnd y e = otherEnd y e') : e = e' := by
  have hb := (Finset.mem_filter.mp he).1
  have hb' := (Finset.mem_filter.mp he').1
  have hn := internal_ne hb
  have hn' := internal_ne hb'
  rcases e with ⟨x,z⟩
  rcases e' with ⟨x',z'⟩
  dsimp only at hi hi' hn hn'
  rcases hi with hx | hz <;> rcases hi' with hx' | hz'
  · subst x; subst x'
    simpa [otherEnd] using hh
  · subst x; subst z'
    have hn' : x' ≠ y := hn'
    simp [otherEnd,hn'] at hh
    subst x'
    exact False.elim (internal_not_reverse hb hb')
  · subst z; subst x'
    have hn : x ≠ y := hn
    simp [otherEnd,hn] at hh
    subst z'
    exact False.elim (internal_not_reverse hb hb')
  · subst z; subst z'
    simpa [otherEnd,hn,hn'] using hh

theorem incident_product (D : Network G) (y : Plane) (q n : Plane → Vec3)
    (hqn : ∀ x, x ≠ y → q x = n x) :
    (∏ e ∈ D.bonds.filter (fun e => ¬ (e.1 ≠ y ∧ e.2 ≠ y)),
      (1 + dot (q e.1) (q e.2))) =
      ∏ z ∈ D.presentNeighbours y, (1 + dot (q y) (n z)) := by
  classical
  apply Finset.prod_bij (fun e _ => otherEnd y e)
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨he,hi⟩
    have hp := (Finset.mem_filter.mp he).2
    apply (mem_presentNeighbours D y _).mpr
    by_cases hx : e.1 = y
    · simpa [otherEnd,hx] using hp
    · have hz : e.2 = y := by tauto
      simpa [otherEnd,hx,hz] using present_symm hp
  · intro e he e' he' hh
    rcases Finset.mem_filter.mp he with ⟨he,hi⟩
    rcases Finset.mem_filter.mp he' with ⟨he',hi'⟩
    exact otherEnd_inj D y e e' he he' (by tauto) (by tauto) hh
  · intro z hz
    have hp := (mem_presentNeighbours D y z).mp hz
    have hyG := (Finset.mem_filter.mp hp.1).1
    have hzG := (Finset.mem_filter.mp hp.2.1).1
    have hn := adjacent_ne hp.2.2.1
    rcases internal_or_reverse hyG hzG hp.2.2.1 with hi | hi
    · refine ⟨(y,z), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_filter.mpr ⟨hi,hp⟩, by simp⟩
      · simp [otherEnd]
    · refine ⟨(z,y), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_filter.mpr ⟨hi,present_symm hp⟩, by simp⟩
      · simp [otherEnd,Ne.symm hn]
  · intro e he
    rcases Finset.mem_filter.mp he with ⟨he,hi⟩
    have hn := internal_ne (Finset.mem_filter.mp he).1
    by_cases hx : e.1 = y
    · have hz : e.2 ≠ y := by rw [hx] at hn; exact Ne.symm hn
      simp [otherEnd,hx,hqn _ hz]
    · have hz : e.2 = y := by tauto
      simp [otherEnd,hx,hz,hqn _ hx,dot_comm]

theorem bond_product_split (D : Network G) (y : Plane) (q n : Plane → Vec3)
    (hqn : ∀ x, x ≠ y → q x = n x) :
    (∏ e ∈ D.bonds, (1 + dot (q e.1) (q e.2))) =
      (∏ e ∈ (removeSite D y).bonds, (1 + dot (n e.1) (n e.2))) *
        ∏ z ∈ D.presentNeighbours y, (1 + dot (q y) (n z)) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not D.bonds
    (fun e => e.1 ≠ y ∧ e.2 ≠ y) (fun e => 1 + dot (q e.1) (q e.2)),
    incident_product D y q n hqn]
  congr 1
  rw [bonds_remove]
  apply Finset.prod_congr rfl
  intro e he
  have hn := (Finset.mem_filter.mp he).2
  rw [hqn _ hn.1,hqn _ hn.2]

theorem join_pins (D : Network G) (τ : PinAssignment G) (b : Bool)
    (y : Plane) (hy : y ∈ D.active) (hno : ∀ e ∈ originalLegs G, e.1 ≠ y)
    (p : SpinLetter × ((removeSite D y).active → SpinLetter)) :
    (∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins (joinSpin D y hy p) e.val.1) else 1) =
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ (removeSite D y).active then
        1 + dot (τ e).val ((removeSite D y).spins p.2 e.val.1) else 1 := by
  apply Finset.prod_congr rfl
  intro e _
  rw [join_spins]
  simp [active_remove,hno e.val e.property]

theorem join_netWeight (D : Network G) (τ : PinAssignment G) (b : Bool)
    (y : Plane) (hy : y ∈ D.active) (hno : ∀ e ∈ originalLegs G, e.1 ≠ y)
    (p : SpinLetter × ((removeSite D y).active → SpinLetter)) :
    netWeight D τ b (joinSpin D y hy p) =
      netWeight (removeSite D y) τ b p.2 * spinWeight (D.status y) p.1 *
        ∏ z ∈ D.presentNeighbours y,
          (1 + dot (spinVector p.1) ((removeSite D y).spins p.2 z)) := by
  have hq : ∀ x, x ≠ y → D.spins (joinSpin D y hy p) x =
      (removeSite D y).spins p.2 x := by
    intro x hx
    simp [join_spins,hx]
  unfold netWeight
  rw [join_weights, bond_product_split D y _ _ hq, join_pins D τ b y hy hno]
  simp only [join_spins,ite_true]
  ring

theorem integrate_site (D : Network G) (τ : PinAssignment G) (b : Bool)
    (y : Plane) (hy : y ∈ D.active) (hno : ∀ e ∈ originalLegs G, e.1 ≠ y) :
    D.partition τ b (fun _ => 1) =
      (removeSite D y).partition τ b (fun n => siteFunctional (D.status y)
        (fun v => ∏ z ∈ D.presentNeighbours y, (1 + dot v (n z)))) := by
  classical
  rw [partition_sum,partition_sum]
  simp only [mul_one]
  rw [← (splitSpin D y hy).symm.sum_comp (netWeight D τ b)]
  simp only [splitSpin_symm, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [siteFunctional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [join_netWeight D τ b y hy hno]
  ring

end AKLT.W.REC022
