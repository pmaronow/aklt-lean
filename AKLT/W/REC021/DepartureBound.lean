module
public import AKLT.W.REC021.Conditioning

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem neighbor_active_removed (a : AKLT.Blueprint.Rec.Departure)
    (z : Plane) (hz : z ∈ a.D.presentNeighbors a.y) : z ∈ (removeSite a.D a.y).active := by
  have hp := (Finset.mem_filter.mp hz).2
  have hne : z ≠ a.y := by
    intro h
    have hh := hp.2.2.1
    rw [h] at hh
    simp [Adjacent, latticeDist] at hh
  rw [active_remove, Finset.mem_erase]
  exact ⟨hne, hp.2.1⟩

theorem responseI_pinned_lower_closed (a : AKLT.Blueprint.Rec.Departure)
    (f g : Plane) (hN : a.D.presentNeighbors a.y = {a.o, f, g})
    (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g) :
    (41 / 50 : ℝ) ≤ responseI a.D a.τ true a.y a.o f g := by
  have hf : f ∈ a.D.presentNeighbors a.y := by rw [hN]; simp
  have hg : g ∈ a.D.presentNeighbors a.y := by rw [hN]; simp
  have ho : a.o ∈ a.D.presentNeighbors a.y := a.present
  let E := removeSite a.D a.y
  let x : Fin 3 → E.active := ![⟨f, neighbor_active_removed a f hf⟩,
    ⟨g, neighbor_active_removed a g hg⟩, ⟨a.o, neighbor_active_removed a a.o ho⟩]
  have hinj : Function.Injective x := by
    intro i j hij
    have hh := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [x]
  have hmem (i : Fin 3) : (x i).val ∈ a.D.presentNeighbors a.y := by
    fin_cases i
    · exact hf
    · exact hg
    · exact ho
  have hnear (i : Fin 3) : (x i).val ∈ neighbors a.y :=
    (Finset.mem_filter.mp (hmem i)).1
  have hno : ∀ e ∈ E.bonds, ∀ i j, ¬ (e.1 = (x i).val ∧ e.2 = (x j).val) := by
    intro e he i j hh
    have hp := (Finset.mem_filter.mp he).2
    have hadj := hp.2.2.1
    apply neighbors_nonadjacent (hnear i) (hnear j)
    simpa [hh.1, hh.2] using hadj
  have hd (i : Fin 3) : (E.presentNeighbors (x i).val).card ≤ 3 :=
    removed_neighbor_degree a _ (hmem i)
  have hpin (e : originalLegs a.G) (i : Fin 3) : e.val.1 ≠ (x i).val :=
    originalLeg_no_neighbor a _ (hnear i) e
  have hl := network_three_pair_lower E a.τ true x hinj hno hd hpin
  change -(27 / 50 : ℝ) * E.partition a.τ true (fun _ => 1) ≤
    E.partition a.τ true (fun n => dot (n f) (n g) + dot (n f) (n a.o) +
      dot (n g) (n a.o)) at hl
  rw [partition_add, partition_add] at hl
  let Z := E.partition a.τ true (fun _ => 1)
  have hz : 0 ≤ Z := partition_nonneg E a.τ true
  by_cases hzero : Z = 0
  · simp [responseI, removedPairMean, Network.expectation, show
      (removeSite a.D a.y).partition a.τ true (fun _ => 1) = 0 from hzero]
    <;> norm_num
  · have hpos : 0 < Z := lt_of_le_of_ne hz (Ne.symm hzero)
    have hh := (le_div_iff₀ hpos).mpr hl
    rw [add_div, add_div] at hh
    dsimp [responseI, removedPairMean, Network.expectation]
    dsimp [Z, E] at hh
    linarith

#print axioms neighbor_active_removed
#print axioms responseI_pinned_lower_closed

end AKLT.W.REC021
