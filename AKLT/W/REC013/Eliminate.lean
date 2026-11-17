module
public import AKLT.W.REC013.Split
public import AKLT.W.REC013.SpinFacts

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC013

theorem trace_partition_eq_remove {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y o : Plane) (hy : D.status y = .D) :
    (traceStep D y o).partition τ b (fun _ => 1) =
      (removeSite D y).partition τ b (fun _ => 1) := by
  let E : Network G :=
    { status := Function.update D.status y .X
      kept := (traceStep D y o).kept }
  have hstep : traceStep D y o = E := by
    dsimp only [E, traceStep]
    rw [hy]
    rfl
  have hb := trace_remove_bonds D y o hy
  rw [hstep] at hb ⊢
  unfold Network.partition
  rw [hb]
  rfl


theorem join_legs {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y : Plane) (hn : y ∉ protectedSites G)
    (j : SpinLetter) (n : (removeSite D y).active → SpinLetter) :
    (∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins (joinSpin D y j n) e.val.1) else 1) =
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ (removeSite D y).active then
        1 + dot (τ e).val ((removeSite D y).spins n e.val.1) else 1 := by
  apply Finset.prod_congr rfl
  intro e _
  have he : e.val.1 ≠ y := by
    intro h
    exact hn (h ▸ leg_origin_protected e)
  rw [join_spins_ne D y j n he]
  simp only [remove_active]
  by_cases hp : b = true ∧ e.val.1 ∈ D.active
  · rw [if_pos hp, if_pos ⟨hp.1,hp.2,he⟩]
  · rw [if_neg hp, if_neg (fun h => hp ⟨h.1,h.2.1⟩)]

theorem join_bonds {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : y ∈ D.active) (hs : D.presentNeighbours y = {o})
    (j : SpinLetter) (n : (removeSite D y).active → SpinLetter) :
    (∏ t ∈ D.bonds, (1 + dot (D.spins (joinSpin D y j n) t.1)
      (D.spins (joinSpin D y j n) t.2))) =
    (1 + dot (spinVector j) ((removeSite D y).spins n o)) *
      ∏ t ∈ (removeSite D y).bonds, (1 + dot ((removeSite D y).spins n t.1)
        ((removeSite D y).spins n t.2)) := by
  have ho : o ∈ D.presentNeighbours y := by rw [hs]; simp
  obtain ⟨e,he,hed⟩ := exists_selected_bond ho
  have hyo : y ≠ o := by
    rcases hed with h | h
    · have hh := (bond_facts he).1
      simpa only [h] using hh
    · have hh := (bond_facts he).1
      exact (show o ≠ y by simpa only [h] using hh).symm
  rw [← Finset.mul_prod_erase D.bonds (fun t =>
    1 + dot (D.spins (joinSpin D y j n) t.1) (D.spins (joinSpin D y j n) t.2)) he]
  rw [← remove_bonds_erase hs he hed]
  congr 1
  · rcases hed with rfl | rfl
    · rw [join_spins_y D y hy, join_spins_ne D y j n hyo.symm]
    · rw [join_spins_y D y hy, join_spins_ne D y j n hyo.symm, dot_comm]
  · apply Finset.prod_congr rfl
    intro t ht
    have hh := (remove_bonds D y t).1 ht
    rw [join_spins_ne D y j n hh.2.1, join_spins_ne D y j n hh.2.2]

/-- Direct finite summation over the unique one-bond D departure. -/
theorem d_partition_eq_remove {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y o : Plane) (hy : y ∈ D.active) (hn : y ∉ protectedSites G)
    (hD : D.status y = .D) (hs : D.presentNeighbours y = {o}) :
    D.partition τ b (fun _ => 1) = (removeSite D y).partition τ b (fun _ => 1) := by
  unfold Network.partition
  rw [sum_split D y hy]
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [join_weight D y hy, join_bonds D y o hy hs, join_legs D τ b y hn, hD]
  simp only [mul_one]
  let C : ℝ := (∏ x : (removeSite D y).active,
      spinWeight ((removeSite D y).status x.val) (n x)) *
    (∏ e ∈ (removeSite D y).bonds,
      (1 + dot ((removeSite D y).spins n e.1) ((removeSite D y).spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ (removeSite D y).active then
        1 + dot (τ e).val ((removeSite D y).spins n e.val.1) else 1
  calc
    _ = (∑ j : SpinLetter,
        spinWeight .D j * (1 + dot (spinVector j) ((removeSite D y).spins n o))) * C := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [C]
      ring
    _ = C := by rw [d_integral_one, one_mul]

end AKLT.W.REC013
