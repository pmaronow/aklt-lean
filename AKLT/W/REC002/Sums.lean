module
public import AKLT.W.REC002.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC002

def extend (V : Finset Plane) (n : V → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ V then spinVector (n ⟨x, h⟩) else 0

def spinSum (V : Finset Plane) (s : Plane → Status)
    (F : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : V → SpinLetter, (∏ x : V, spinWeight (s x) (n x)) * F (extend V n)

def insConf (V : Finset Plane) (y : Plane) (j : SpinLetter) (n : V → SpinLetter)
    (x : (insert y V : Finset Plane)) : SpinLetter :=
  if h : x.val = y then j else n ⟨x.val, (Finset.mem_insert.mp x.property).resolve_left h⟩

def splitConf (V : Finset Plane) (y : Plane) (hy : y ∉ V) :
    (↥(insert y V) → SpinLetter) ≃ SpinLetter × (V → SpinLetter) where
  toFun n := (n ⟨y, Finset.mem_insert_self _ _⟩,
    fun x => n ⟨x.val, Finset.mem_insert_of_mem x.property⟩)
  invFun p := insConf V y p.1 p.2
  left_inv n := by
    funext x
    dsimp [insConf]
    split_ifs with h
    · congr 1; exact Subtype.ext h.symm
    · rfl
  right_inv p := by
    rcases p with ⟨j, n⟩
    apply Prod.ext
    · simp [insConf]
    · funext x
      change insConf V y j n ⟨x.val, _⟩ = n x
      have hxy : x.val ≠ y := fun h => hy (h ▸ x.property)
      simp [insConf, hxy]

theorem extend_ins (V : Finset Plane) (y : Plane) (_hy : y ∉ V)
    (j : SpinLetter) (n : V → SpinLetter) :
    extend (insert y V) (insConf V y j n) = Function.update (extend V n) y (spinVector j) := by
  funext x
  by_cases hxy : x = y
  · subst x; simp [extend, insConf]
  · by_cases hx : x ∈ V
    · simp [extend, insConf, hx, hxy]
    · simp [extend, hx, hxy]

theorem prod_ins (V : Finset Plane) (y : Plane) (hy : y ∉ V)
    (s : Plane → Status) (j : SpinLetter) (n : V → SpinLetter) :
    (∏ x : (insert y V : Finset Plane), spinWeight (s x) (insConf V y j n x)) =
      spinWeight (s y) j * ∏ x : V, spinWeight (s x) (n x) := by
  rw [← (Finset.subtypeInsertEquivOption hy).symm.prod_comp
    (fun x => spinWeight (s x) (insConf V y j n x))]
  simp only [Fintype.prod_option]
  congr 1
  · simp [Finset.subtypeInsertEquivOption, insConf]
  · apply Finset.prod_congr rfl
    intro x _
    have hxy : x.val ≠ y := fun h => hy (h ▸ x.property)
    simp [Finset.subtypeInsertEquivOption, insConf, hxy]

theorem spinSum_insert (V : Finset Plane) (y : Plane) (hy : y ∉ V)
    (s : Plane → Status) (F : (Plane → Vec3) → ℝ) :
    spinSum (insert y V) s F =
      ∑ n : V → SpinLetter, (∏ x : V, spinWeight (s x) (n x)) *
        siteFunctional (s y) (fun v => F (Function.update (extend V n) y v)) := by
  unfold spinSum
  rw [← (splitConf V y hy).symm.sum_comp
    (fun n => (∏ x : (insert y V : Finset Plane), spinWeight (s x) (n x)) *
      F (extend (insert y V) n))]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  unfold siteFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (∏ x : (insert y V : Finset Plane), spinWeight (s x) (insConf V y j n x)) *
    F (extend (insert y V) (insConf V y j n)) = _
  rw [prod_ins V y hy, extend_ins V y hy]
  ring

def bondProduct (B : Finset (Plane × Plane)) (n : Plane → Vec3) : ℝ :=
  ∏ e ∈ B, (1 + dot (n e.1) (n e.2))

def legProduct {G : Finset Plane} (V : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (n : Plane → Vec3) : ℝ :=
  ∏ e : originalLegs G,
    if pinned = true ∧ e.val.1 ∈ V then 1 + dot (τ e).val (n e.val.1) else 1

theorem partition_spinSum {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ pinned f = spinSum D.active D.status
      (fun n => f n * bondProduct D.bonds n * legProduct D.active τ pinned n) := by
  unfold Network.partition spinSum bondProduct legProduct
  apply Finset.sum_congr rfl
  intro n _
  change _ = (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (f (D.spins n) * (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
      ∏ e : originalLegs G, if pinned = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1)
  ring

end AKLT.W.REC002
