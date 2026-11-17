import AKLT.W.REC082.PE.Normalization

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC082.PE

/-- An omitted site can be represented on a fixed volume by a unit zero atom. -/
def paddedWeight (s : Status) (j : SpinLetter) : ℝ :=
  if s = .X then if j = none then 1 else 0 else spinWeight s j

/-- Spins indexed by the whole original volume. Removed sites will be forced
onto the zero atom by their padded weights. -/
def volumeSpins {G : Finset Plane} (n : (x : G) → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ G then spinVector (n ⟨x, h⟩) else 0

/-- A fixed-volume version of the partition functional. -/
def paddedPartition {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : (x : G) → SpinLetter,
    (∏ x : G, paddedWeight (D.status x.val) (n x)) * f (volumeSpins n) *
    (∏ e ∈ D.bonds, (1 + dot (volumeSpins n e.1) (volumeSpins n e.2))) *
      ∏ e : originalLegs G, if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (volumeSpins n e.val.1) else 1

private def extendLabels {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : G) : SpinLetter :=
  if h : x.val ∈ D.active then n ⟨x.val, h⟩ else none

private theorem extendLabels_injective {G : Finset Plane} (D : Network G) :
    Function.Injective (extendLabels D) := by
  intro n m he
  funext x
  have hxG := (Finset.mem_filter.mp x.property).1
  have h := congrFun he ⟨x.val, hxG⟩
  simpa [extendLabels, x.property] using h

private theorem volumeSpins_extend {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) : volumeSpins (extendLabels D n) = D.spins n := by
  funext x
  by_cases hxA : x ∈ D.active
  · have hxG := (Finset.mem_filter.mp hxA).1
    simp [volumeSpins, extendLabels, Network.spins, hxA, hxG]
  · by_cases hxG : x ∈ G
    · simp [volumeSpins, extendLabels, Network.spins, hxA, hxG, spinVector]
    · simp [volumeSpins, Network.spins, hxA, hxG]

private theorem padded_product_extend {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) :
    (∏ x : G, paddedWeight (D.status x.val) (extendLabels D n x)) =
      ∏ x : D.active, spinWeight (D.status x.val) (n x) := by
  classical
  symm
  apply Fintype.prod_of_injective
    (fun x : D.active => (⟨x.val, (Finset.mem_filter.mp x.property).1⟩ : G))
    (fun x y h => Subtype.ext (congrArg (fun z : G => z.val) h))
  · intro x hx
    have hnot : x.val ∉ D.active := by
      intro ha
      exact hx ⟨⟨x.val, ha⟩, rfl⟩
    have hs : D.status x.val = .X := by
      simpa only [Network.active, Finset.mem_filter, x.property, true_and, not_not] using hnot
    simp [extendLabels, hnot, paddedWeight, hs]
  · intro x
    have hs := (Finset.mem_filter.mp x.property).2
    simp [extendLabels, x.property, paddedWeight, hs]

private theorem padded_product_zero_off_range {G : Finset Plane} (D : Network G)
    (n : (x : G) → SpinLetter) (hn : n ∉ Set.range (extendLabels D)) :
    (∏ x : G, paddedWeight (D.status x.val) (n x)) = 0 := by
  classical
  have hex : ∃ x : G, x.val ∉ D.active ∧ n x ≠ none := by
    by_contra! hall
    apply hn
    refine ⟨fun x => n ⟨x.val, (Finset.mem_filter.mp x.property).1⟩, ?_⟩
    funext x
    by_cases ha : x.val ∈ D.active
    · simp [extendLabels, ha]
    · simp [extendLabels, ha, hall x ha]
  obtain ⟨x, hx, hj⟩ := hex
  have hs : D.status x.val = .X := by
    simpa only [Network.active, Finset.mem_filter, x.property, true_and, not_not] using hx
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  simp [paddedWeight, hs, hj]

/-- Padding removed sites with deterministic zero atoms changes no partition. -/
theorem partition_eq_padded {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) : D.partition τ b f = paddedPartition D τ b f := by
  classical
  unfold Network.partition paddedPartition
  apply Fintype.sum_of_injective (extendLabels D) (extendLabels_injective D)
  · intro n hn
    rw [padded_product_zero_off_range D n hn]
    ring
  · intro n
    rw [padded_product_extend, volumeSpins_extend]

end AKLT.W.REC082.PE
