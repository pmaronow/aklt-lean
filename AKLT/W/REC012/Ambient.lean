module
public import AKLT.W.REC012.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
namespace AKLT.W.REC012

/-- Removed sites are padded by a single atom of mass one. -/
def paddedWeight (s : Status) (j : SpinLetter) : ℝ :=
  if s = .X then if j = none then 1 else 0 else spinWeight s j

def ambientSpins (G : Finset Plane) (n : G → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ G then spinVector (n ⟨x, h⟩) else 0

def pinProduct {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (v : Plane → Vec3) : ℝ :=
  ∏ e : originalLegs G, if e.val.1 ∈ D.active then 1 + dot (τ e).val (v e.val.1) else 1

def ambientTerm {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (n : G → SpinLetter) : ℝ :=
  (∏ x : G, paddedWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (ambientSpins G n e.1) (ambientSpins G n e.2))) *
    pinProduct D τ (ambientSpins G n)

def ambientPartition {G : Finset Plane} (D : Network G) (τ : PinAssignment G) : ℝ :=
  ∑ n : G → SpinLetter, ambientTerm D τ n

def completeSpins {G : Finset Plane} (D : Network G)
    (n : D.active → SpinLetter) : G → SpinLetter :=
  fun x => if h : x.val ∈ D.active then n ⟨x.val, h⟩ else none

lemma completeSpins_injective {G : Finset Plane} (D : Network G) :
    Function.Injective (completeSpins D) := by
  intro n m h
  funext x
  have hx : x.val ∈ G := (Finset.mem_filter.mp x.property).1
  have := congrFun h ⟨x.val, hx⟩
  simpa [completeSpins, x.property] using this

lemma ambient_complete {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter) :
    ambientSpins G (completeSpins D n) = D.spins n := by
  funext x
  by_cases hx : x ∈ D.active
  · have hG := (Finset.mem_filter.mp hx).1
    simp [ambientSpins, completeSpins, Network.spins, hx, hG]
  · by_cases hG : x ∈ G <;>
      simp [ambientSpins, completeSpins, Network.spins, hx, hG, spinVector]

lemma ambientTerm_complete {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (n : D.active → SpinLetter) :
    ambientTerm D τ (completeSpins D n) =
      (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
        (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) * pinProduct D τ (D.spins n) := by
  rw [ambientTerm, ambient_complete]
  congr 2
  let w : Plane → ℝ := fun x =>
    if h : x ∈ D.active then spinWeight (D.status x) (n ⟨x, h⟩) else 1
  calc
    (∏ x : G, paddedWeight (D.status x.val) (completeSpins D n x)) = ∏ x ∈ G, w x := by
      rw [← Finset.prod_coe_sort G w]
      apply Finset.prod_congr rfl
      intro x hx
      by_cases ha : x.val ∈ D.active
      · have hs := (Finset.mem_filter.mp ha).2
        simp [w, completeSpins, paddedWeight, ha, hs]
      · have hs : D.status x.val = .X := by
          simpa [Network.active, x.property] using ha
        simp [w, completeSpins, paddedWeight, ha, hs]
    _ = ∏ x ∈ D.active, w x :=
      (Finset.prod_subset (Finset.filter_subset _ _) (by intro x hx ha; change x ∉ D.active at ha; simp only [w, dite_eq_right ha])).symm
    _ = ∏ x : D.active, spinWeight (D.status x.val) (n x) := by
      rw [← Finset.prod_coe_sort D.active w]
      apply Finset.prod_congr rfl
      intro x hx
      simp [w, x.property]

lemma ambientTerm_zero {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (n : G → SpinLetter) (x : G) (hx : x.val ∉ D.active) (hn : n x ≠ none) :
    ambientTerm D τ n = 0 := by
  have hs : D.status x.val = .X := by simpa [Network.active, x.property] using hx
  have hw : (∏ z : G, paddedWeight (D.status z.val) (n z)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ x)
    simp [paddedWeight, hs, hn]
  unfold ambientTerm
  rw [hw]
  ring

lemma partition_eq_ambient {G : Finset Plane} (D : Network G) (τ : PinAssignment G) :
    D.partition τ true (fun _ => 1) = ambientPartition D τ := by
  classical
  unfold Network.partition ambientPartition
  simp only [mul_one, true_and]
  change (∑ n : D.active → SpinLetter,
    (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
      (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) * pinProduct D τ (D.spins n)) = _
  apply Finset.sum_bij_ne_zero (fun n _ _ => completeSpins D n)
  · intro n hn hne; exact Finset.mem_univ _
  · intro n hn hne m hm hme heq
    exact completeSpins_injective D heq
  · intro n hn hne
    let m : D.active → SpinLetter := fun x => n ⟨x.val, (Finset.mem_filter.mp x.property).1⟩
    have heq : completeSpins D m = n := by
      funext x
      by_cases hx : x.val ∈ D.active
      · simp [completeSpins, m, hx]
      · have hnone : n x = none := by
          by_contra h
          exact hne (ambientTerm_zero D τ n x hx h)
        simp [completeSpins, hx, hnone]
    refine ⟨m, Finset.mem_univ _, ?_, heq⟩
    rw [← ambientTerm_complete, heq]
    exact hne
  · intro n hn hne
    exact (ambientTerm_complete D τ n).symm

end AKLT.W.REC012
