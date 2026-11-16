import AKLT.W.REC014.Trace
import AKLT.W.REC014.Sum

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC014

def extendSpins (A : Finset Plane) (n : A → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ A then spinVector (n ⟨x,h⟩) else 0

theorem extend_at (A : Finset Plane) (n : A → SpinLetter) (x : A) :
    extendSpins A n x.val = spinVector (n x) := by
  simp [extendSpins, x.property]

theorem extend_update_ne (A : Finset Plane) (n : A → SpinLetter) (y : A)
    (j : SpinLetter) (x : Plane) (hx : x ≠ y.val) :
    extendSpins A (Function.update n y j) x = extendSpins A n x := by
  unfold extendSpins
  split_ifs with h
  · rw [Function.update_of_ne (show (⟨x,h⟩ : A) ≠ y from
      fun he => hx (congrArg Subtype.val he))]
  · rfl

/-- Expose the finite site set as an explicit argument, so equal active sets
can be substituted before introducing the dependent assignment sum. -/
def partitionOn {G : Finset Plane} (A : Finset Plane) (s : Plane → Status)
    (B : Finset (Plane × Plane)) (τ : PinAssignment G) (b : Bool) : ℝ :=
  ∑ n : A → SpinLetter, (∏ x : A, spinWeight (s x.val) (n x)) *
    (∏ f ∈ B, (1 + dot (extendSpins A n f.1) (extendSpins A n f.2))) *
    ∏ l : originalLegs G, if b = true ∧ l.val.1 ∈ A then
      1 + dot (τ l).val (extendSpins A n l.val.1) else 1

theorem partition_on {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : D.partition τ b (fun _ => 1) =
      partitionOn D.active D.status D.bonds τ b := by
  simp only [Network.partition,partitionOn,Network.spins,extendSpins,mul_one]

theorem partition_collapse (a : AKLT.Blueprint.Rec.Departure)
    (hy : a.D.status a.y = .U) (hc : (a.D.presentNeighbours a.y).card = 1)
    (b : Bool) : (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
      a.D.partition a.τ b (fun _ => 1) := by
  classical
  obtain ⟨e,he,hform,hbonds,hrest⟩ := leaf_bonds a hy hc
  let A := a.D.active
  let y : A := ⟨a.y,a.start.1⟩
  have ho := (Finset.mem_filter.mp a.present).2.2.1
  let o : A := ⟨a.o,ho⟩
  have hyo : o ≠ y := by
    intro h
    exact (adjacent_ne (Finset.mem_filter.mp a.present).2.2.2.1)
      (congrArg Subtype.val h).symm
  let s : A → Status := fun x => a.D.status x.val
  let P (n : A → SpinLetter) := ∏ l : originalLegs a.G,
    if b = true ∧ l.val.1 ∈ A then
      1 + dot (a.τ l).val (extendSpins A n l.val.1) else 1
  let H (n : A → SpinLetter) :=
    (∏ f ∈ a.D.bonds.erase e,
      (1 + dot (extendSpins A n f.1) (extendSpins A n f.2))) * P n
  have hP (n : A → SpinLetter) (j : SpinLetter) : P (Function.update n y j) = P n := by
    apply Finset.prod_congr rfl
    intro l _
    have hl : l.val.1 ≠ y.val := by
      intro h
      apply a.start.2.1
      change l.val.1 = a.y at h
      rw [← h]
      exact leg_protected l
    rw [extend_update_ne A n y j l.val.1 hl]
  have hH (n : A → SpinLetter) (j : SpinLetter) : H (Function.update n y j) = H n := by
    dsimp only [H]
    rw [hP]
    congr 1
    apply Finset.prod_congr rfl
    intro f hf
    rw [extend_update_ne A n y j f.1 (hrest f hf).1,
      extend_update_ne A n y j f.2 (hrest f hf).2]
  have hbond (n : A → SpinLetter) :
      (∏ f ∈ a.D.bonds, (1 + dot (extendSpins A n f.1) (extendSpins A n f.2))) =
      (1 + dot (spinVector (n y)) (spinVector (n o))) *
        ∏ f ∈ a.D.bonds.erase e,
          (1 + dot (extendSpins A n f.1) (extendSpins A n f.2)) := by
    rw [← Finset.mul_prod_erase _ _ he]
    congr 1
    rcases hform with h | h
    · rw [h.1,h.2,extend_at A n y,extend_at A n o]
    · rw [h.1,h.2,extend_at A n y,extend_at A n o,dot_comm]
  have hbefore : a.D.partition a.τ b (fun _ => 1) =
      ∑ n : A → SpinLetter, (∏ x, spinWeight (s x) (n x)) * H n *
        (1 + dot (spinVector (n y)) (spinVector (n o))) := by
    rw [partition_on]
    change (∑ n : A → SpinLetter, (∏ x, spinWeight (s x) (n x)) *
      (∏ f ∈ a.D.bonds, (1 + dot (extendSpins A n f.1) (extendSpins A n f.2))) * P n) = _
    apply Finset.sum_congr rfl
    intro n _
    rw [hbond]
    dsimp [H]
    ring
  have hstatus (x : A) : (traceStep a.D a.y a.o).status x.val =
      (Function.update s y .D) x := by
    by_cases hx : x = y
    · subst x; simp [traceStep,hy,y]
    · have hval : x.val ≠ a.y := fun h => hx (Subtype.ext h)
      simp [traceStep,Function.update_of_ne hx,Function.update_of_ne hval,s]
  have hafter : (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
      ∑ n : A → SpinLetter,
        (∏ x, spinWeight ((Function.update s y .D) x) (n x)) * H n := by
    rw [partition_on,trace_active a.D a.y a.o hy,hbonds]
    change (∑ n : A → SpinLetter,
      (∏ x : A, spinWeight ((traceStep a.D a.y a.o).status x.val) (n x)) *
      (∏ f ∈ a.D.bonds.erase e,
        (1 + dot (extendSpins A n f.1) (extendSpins A n f.2))) * P n) = _
    simp_rw [hstatus]
    simp only [H,mul_assoc]
  rw [hbefore,hafter]
  exact (integrate_leaf s y o hyo hy H hH).symm

end AKLT.W.REC014
