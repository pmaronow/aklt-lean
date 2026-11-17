module
public import AKLT.W.REC011.Monotone

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC011

def fullSpins {G : Finset Plane} (n : G → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ G then spinVector (n ⟨x, h⟩) else 0

def extendConfig {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter) :
    G → SpinLetter := fun x => if h : x.val ∈ D.active then n ⟨x.val, h⟩ else none

lemma fullSpins_extend {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter) :
    fullSpins (extendConfig D n) = D.spins n := by
  funext x
  by_cases hx : x ∈ G
  · by_cases ha : x ∈ D.active <;> simp [fullSpins, extendConfig, Network.spins, hx, ha,
      spinVector]
  · have ha : x ∉ D.active := fun h => hx (Finset.mem_filter.mp h).1
    simp [fullSpins, Network.spins, hx, ha]

lemma lawProduct_extend {G : Finset Plane} (D : Network G) (n : D.active → SpinLetter) :
    (∏ x : G, lawWeight (D.status x) (extendConfig D n x)) =
      ∏ x : D.active, spinWeight (D.status x) (n x) := by
  classical
  symm
  apply Finset.prod_bij_ne_one
    (fun x _ _ => (⟨x.val, (Finset.mem_filter.mp x.property).1⟩ : G))
  · intros; exact Finset.mem_univ _
  · intro x _ _ y _ _ h
    exact Subtype.ext (congrArg (fun z : G => z.val) h)
  · intro x _ hx
    have ha : x.val ∈ D.active := by
      by_contra ha
      have hs : D.status x.val = .X := by simpa [Network.active, x.property] using ha
      simp [extendConfig, ha, lawWeight, hs] at hx
    refine ⟨⟨x.val, ha⟩, Finset.mem_univ _, ?_, ?_⟩
    · have hs := (Finset.mem_filter.mp ha).2
      simpa [extendConfig, ha, lawWeight, hs] using hx
    · rfl
  · intro x _ _
    have hs := (Finset.mem_filter.mp x.property).2
    simp [extendConfig, x.property, lawWeight, hs]

def fullFreePartition {G : Finset Plane} (D : Network G) : ℝ := by
  classical
  exact ∑ n : G → SpinLetter, (∏ x : G, lawWeight (D.status x) (n x)) *
    ∏ e ∈ D.bonds, (1 + dot (fullSpins n e.1) (fullSpins n e.2))

lemma freePartition_eq_full {G : Finset Plane} (D : Network G) (τ : PinAssignment G) :
    D.partition τ false (fun _ => 1) = fullFreePartition D := by
  classical
  simp only [Network.partition, Bool.false_eq_true, false_and, ite_false,
    Finset.prod_const_one, mul_one, fullFreePartition]
  apply Finset.sum_bij_ne_zero (fun n _ _ => extendConfig D n)
  · intros; exact Finset.mem_univ _
  · intro n _ _ m _ _ h
    funext x
    have he := congrFun h (⟨x.val, (Finset.mem_filter.mp x.property).1⟩ : G)
    simpa [extendConfig, x.property] using he
  · intro n _ hn
    let m : D.active → SpinLetter := fun x => n ⟨x.val, (Finset.mem_filter.mp x.property).1⟩
    have he : extendConfig D m = n := by
      funext x
      by_cases ha : x.val ∈ D.active
      · simp [extendConfig, ha, m]
      · have hs : D.status x.val = .X := by simpa [Network.active, x.property] using ha
        have hn0 : n x = none := by
          by_contra hnx
          have hw : lawWeight (D.status x) (n x) = 0 := by simp [lawWeight, hs, hnx]
          have hp : (∏ z : G, lawWeight (D.status z) (n z)) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ x) hw
          exact hn (by rw [hp, zero_mul])
        simp [extendConfig, ha, hn0]
    refine ⟨m, Finset.mem_univ _, ?_, he⟩
    intro hm
    apply hn
    rw [← he, lawProduct_extend, fullSpins_extend]
    exact hm
  · intro n _ _
    rw [lawProduct_extend, fullSpins_extend]

end AKLT.W.REC011
