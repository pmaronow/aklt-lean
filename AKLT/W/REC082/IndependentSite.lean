import AKLT.W.REC082.Partition
import AKLT.W.REC082.Trail

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

/-- Finite disintegration at a coordinate whose remaining factor does not
involve that coordinate. No measure-theoretic or positivity premise is needed. -/
theorem independent_site_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (w : ι → SpinLetter → ℝ) (F : (ι → SpinLetter) → ℝ)
    (hF : ∀ m n, (∀ x, x ≠ i → m x = n x) → F m = F n)
    (g : SpinLetter → ℝ) :
    (∑ n, (∏ x, w x (n x)) * F n * g (n i)) =
      (∑ n : {x : ι // x ≠ i} → SpinLetter,
        (∏ x : {x : ι // x ≠ i}, w x.val (n x)) *
          F ((Equiv.funSplitAt i SpinLetter).symm (none, n))) *
        ∑ j, w i j * g j := by
  classical
  let e := Equiv.funSplitAt i SpinLetter
  rw [← e.symm.sum_comp (fun n => (∏ x, w x (n x)) * F n * g (n i))]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hF' : F (e.symm (j, n)) = F (e.symm (none, n)) := by
    apply hF
    intro x hx
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hx]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i, hF']
  have hi : e.symm (j, n) i = j := by
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  have hprod :
      (∏ x : {x : ι // x ≠ i}, w x.val
        ((Equiv.funSplitAt i SpinLetter).symm (j, n) x.val)) =
        ∏ x : {x : ι // x ≠ i}, w x.val (n x) := by
    apply Finset.prod_congr rfl
    intro x _
    simp [Equiv.funSplitAt, Equiv.piSplitAt, x.property]
  rw [hi, hprod]
  ring

/-- A one-coordinate moment identity transfers through any independent factor. -/
theorem independent_site_moment {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (w : ι → SpinLetter → ℝ) (F : (ι → SpinLetter) → ℝ)
    (hF : ∀ m n, (∀ x, x ≠ i → m x = n x) → F m = F n)
    (g : SpinLetter → ℝ) (η : ℝ)
    (hmass : ∑ j, w i j = 1) (hmoment : ∑ j, w i j * g j = η) :
    (∑ n, (∏ x, w x (n x)) * F n * g (n i)) =
      η * ∑ n, (∏ x, w x (n x)) * F n := by
  rw [independent_site_sum i w F hF g, hmoment]
  have h := independent_site_sum i w F hF (fun _ => 1)
  simp only [mul_one, hmass] at h
  rw [h]
  ring

/-- All factors other than the one-site masses. -/
def interactionWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

theorem partitionWeight_eq {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) :
    partitionWeight D τ b n =
      (∏ x : D.active, spinWeight (D.status x.val) (n x)) * interactionWeight D τ b n := by
  unfold partitionWeight interactionWeight
  ring

theorem spins_eq_of_agree_away {G : Finset Plane} (D : Network G) (v x : Plane)
    (m n : (x : D.active) → SpinLetter)
    (hmn : ∀ i : D.active, i.val ≠ v → m i = n i) (hx : x ≠ v) :
    D.spins m x = D.spins n x := by
  unfold Network.spins
  split_ifs
  · rw [hmn _ hx]
  · rfl

theorem interactionWeight_independent {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (v : Plane)
    (hiso : D.presentNeighbours v = ∅) (hv : v ∉ protectedSites G)
    (m n : (x : D.active) → SpinLetter)
    (hmn : ∀ i : D.active, i.val ≠ v → m i = n i) :
    interactionWeight D τ b m = interactionWeight D τ b n := by
  classical
  unfold interactionWeight
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    have hp : D.Present e.1 e.2 := (Finset.mem_filter.mp he).2
    have h1 : e.1 ≠ v := by
      intro h
      have hmem := present_mem_neighbours hp
      rw [h, hiso] at hmem
      exact Finset.notMem_empty _ hmem
    have h2 : e.2 ≠ v := by
      intro h
      have hmem := present_mem_neighbours (present_symm hp)
      rw [h, hiso] at hmem
      exact Finset.notMem_empty _ hmem
    rw [spins_eq_of_agree_away D v e.1 m n hmn h1,
      spins_eq_of_agree_away D v e.2 m n hmn h2]
  · apply Finset.prod_congr rfl
    intro e _
    have h1 : e.val.1 ≠ v := by
      intro h
      have hmem : e.val ∈ (originalLegs G).filter (fun a => a.1 = v) :=
        Finset.mem_filter.mpr ⟨e.property, h⟩
      rw [no_originalLegs hv] at hmem
      exact Finset.notMem_empty _ hmem
    rw [spins_eq_of_agree_away D v e.val.1 m n hmn h1]

/-- A U site's squared norm is one on every summand of nonzero site weight. -/
theorem partition_norm_U {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (v : Plane) (hv : v ∈ D.active) (hs : D.status v = .U) :
    D.partition τ b (fun a => normSq (a v)) = D.partition τ b (fun _ => 1) := by
  classical
  rw [partition_eq_sum_weight, partition_eq_sum_weight]
  apply Finset.sum_congr rfl
  intro n _
  let i : D.active := ⟨v, hv⟩
  cases hj : n i with
  | none =>
    have hprod : (∏ x : D.active, spinWeight (D.status x.val) (n x)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      change spinWeight (D.status v) (n i) = 0
      rw [hs, hj]
      rfl
    rw [partitionWeight_eq, hprod]
    simp
  | some j =>
    have hnorm : normSq (D.spins n v) = 1 := by
      have hspin : D.spins n v = spinVector (n i) := by simp [Network.spins, hv, i]
      rw [hspin, hj]
      exact ico_unit j
    simp [hnorm]

/-- An isolated D site's squared norm has mean 3/5, even when the
partition function of the remaining network vanishes. -/
theorem partition_norm_D {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (v : Plane) (hv : v ∈ D.active) (hs : D.status v = .D)
    (hiso : D.presentNeighbours v = ∅) (hvp : v ∉ protectedSites G) :
    D.partition τ b (fun a => normSq (a v)) =
      (3 / 5) * D.partition τ b (fun _ => 1) := by
  classical
  let i : D.active := ⟨v, hv⟩
  let w : D.active → SpinLetter → ℝ := fun x => spinWeight (D.status x.val)
  let F := interactionWeight D τ b
  have hF : ∀ m n, (∀ x, x ≠ i → m x = n x) → F m = F n := by
    intro m n hmn
    apply interactionWeight_independent D τ b v hiso hvp
    intro x hx
    exact hmn x (fun h => hx (congrArg Subtype.val h))
  have hmass : ∑ j, w i j = 1 := by
    simpa only [w, i, hs, siteFunctional, mul_one] using site_mass .D (Or.inr rfl)
  have hmoment : ∑ j, w i j * normSq (spinVector j) = 3 / 5 := by
    simpa only [w, i, hs, siteFunctional] using d_norm_moment
  have h := independent_site_moment i w F hF (fun j => normSq (spinVector j))
    (3 / 5) hmass hmoment
  simpa only [partition_eq_sum_weight, partitionWeight_eq, mul_one,
    Network.spins, dite_eq_left hv, w, F, i] using h

end AKLT.W.REC082
