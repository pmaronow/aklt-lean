module
public import AKLT.W.REC089.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

def joinSpins {ι : Type} (p : ι → Prop) [DecidablePred p]
    (inside : {x // p x} → SpinLetter) (outside : {x // ¬p x} → SpinLetter) :
    ι → SpinLetter :=
  (Equiv.piEquivPiSubtypeProd p (fun _ => SpinLetter)).symm (inside, outside)

/-- Disintegration is an unnormalized finite-sum identity, including zero fibers. -/
theorem finite_disintegration {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (w : ι → SpinLetter → ℝ)
    (F : (ι → SpinLetter) → ℝ) :
    (∑ σ : ι → SpinLetter, (∏ x, w x (σ x)) * F σ) =
      ∑ ω : {x // ¬p x} → SpinLetter, (∏ x, w x.val (ω x)) *
        ∑ η : {x // p x} → SpinLetter, (∏ x, w x.val (η x)) * F (joinSpins p η ω) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => SpinLetter)
  rw [← e.symm.sum_comp (fun σ => (∏ x, w x (σ x)) * F σ)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η _
  have hp := Fintype.prod_subtype_mul_prod_subtype p
    (fun x => w x ((e.symm (η, ω)) x))
  rw [← hp]
  have hin (x : {x // p x}) : e.symm (η, ω) x.val = η x := by
    simp [e, Equiv.piEquivPiSubtypeProd, x.property]
  have hout (x : {x // ¬p x}) : e.symm (η, ω) x.val = ω x := by
    simp [e, Equiv.piEquivPiSubtypeProd, x.property]
  simp_rw [hin, hout]
  change _ = (∏ x : {x // ¬p x}, w x.val (ω x)) *
    ((∏ x : {x // p x}, w x.val (η x)) * F (e.symm (η, ω)))
  ring

def localChart (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) (z : Plane) : Plane :=
  a.y + normalizeRotation incoming z

def localSites (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) : Finset Plane :=
  templateSites.image (localChart a incoming)

def insideTemplate (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (x : a.D.active) : Prop := x.val ∈ localSites a incoming

instance (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    DecidablePred (insideTemplate a incoming) := fun _ => Classical.propDecidable _

abbrev ExteriorSpins (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :=
  {x : a.D.active // ¬insideTemplate a incoming x} → SpinLetter

abbrev InteriorSpins (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :=
  {x : a.D.active // insideTemplate a incoming x} → SpinLetter

theorem centre_mem_localSites (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass) :
    a.y ∈ localSites a incoming := by
  have h0 : (0, 0) ∈ templateSites := by decide +kernel
  have hz : localChart a incoming (0, 0) = a.y := by
    cases incoming <;> simp [localChart, normalizeRotation]
  rw [← hz]
  exact Finset.mem_image_of_mem _ h0

theorem trace_active {G : Finset Plane} (D : Network G) (y o : Plane)
    (hU : D.status y = .U) : (traceStep D y o).active = D.active := by
  ext x
  by_cases hxy : x = y
  · subst x
    simp [Network.active, traceStep, hU]
  · simp [Network.active, traceStep, Function.update_of_ne hxy, hU]

/-- All bond and original-leg factors. The active coordinate set is fixed. -/
def commonFactors (a : AKLT.Blueprint.Rec.Departure) (next : Bool)
    (σ : a.D.active → SpinLetter) : ℝ :=
  let E := if next then traceStep a.D a.y a.o else a.D
  (∏ e ∈ E.bonds, (1 + dot (a.D.spins σ e.1) (a.D.spins σ e.2))) *
  ∏ e : originalLegs a.G,
    if e.val.1 ∈ a.D.active then 1 + dot (a.τ e).val (a.D.spins σ e.val.1) else 1

def commonStatus (a : AKLT.Blueprint.Rec.Departure) (next : Bool) (x : Plane) : Status :=
  (if next then traceStep a.D a.y a.o else a.D).status x

/-- The outside weight includes only site masses; all other factors stay in the fiber. -/
def exteriorMass (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) : ℝ := by
  classical
  exact ∏ x, spinWeight (a.D.status x.val.val) (ω x)

/-- The actual conditioned template sum, with the original bonds and pins unchanged. -/
def actualFibre (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) (next : Bool) : ℝ := by
  classical
  exact ∑ η : InteriorSpins a incoming,
    (∏ x, spinWeight (commonStatus a next x.val.val) (η x)) *
      commonFactors a next (joinSpins (insideTemplate a incoming) η ω)

theorem exteriorMass_nonneg (a : AKLT.Blueprint.Rec.Departure) (incoming : Compass)
    (ω : ExteriorSpins a incoming) : 0 ≤ exteriorMass a incoming ω := by
  classical
  unfold exteriorMass
  exact Finset.prod_nonneg fun x _ => spinWeight_nonneg _ _

def supportSpins (A : Finset Plane) (σ : A → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ A then spinVector (σ ⟨x, h⟩) else 0

def partitionOn {G : Finset Plane} (A : Finset Plane) (s : Plane → Status)
    (bonds : Finset (Plane × Plane)) (τ : PinAssignment G) : ℝ :=
  ∑ σ : A → SpinLetter, (∏ x : A, spinWeight (s x.val) (σ x)) *
    ((∏ e ∈ bonds, (1 + dot (supportSpins A σ e.1) (supportSpins A σ e.2))) *
      ∏ e : originalLegs G,
        if e.val.1 ∈ A then 1 + dot (τ e).val (supportSpins A σ e.val.1) else 1)

theorem partition_eq_partitionOn {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) :
    D.partition τ true (fun _ => 1) = partitionOn D.active D.status D.bonds τ := by
  simp [Network.partition, partitionOn, Network.spins, supportSpins, mul_assoc]

theorem common_partition (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (next : Bool) :
    (if next then traceStep a.D a.y a.o else a.D).partition a.τ true (fun _ => 1) =
      ∑ σ : a.D.active → SpinLetter,
        (∏ x, spinWeight (commonStatus a next x.val) (σ x)) * commonFactors a next σ := by
  have ha := trace_active a.D a.y a.o hU
  change _ = partitionOn a.D.active (commonStatus a next)
    (if next then traceStep a.D a.y a.o else a.D).bonds a.τ
  rw [partition_eq_partitionOn]
  cases next
  · rfl
  · simp only [Bool.true_eq, ite_true, ha]
    rfl

theorem partition_disintegration (a : AKLT.Blueprint.Rec.Departure)
    (hU : a.D.status a.y = .U) (incoming : Compass) (next : Bool) :
    (if next then traceStep a.D a.y a.o else a.D).partition a.τ true (fun _ => 1) =
      ∑ ω : ExteriorSpins a incoming, exteriorMass a incoming ω *
        actualFibre a incoming ω next := by
  classical
  rw [common_partition a hU next]
  rw [finite_disintegration (insideTemplate a incoming)]
  apply Finset.sum_congr rfl
  intro ω _
  unfold actualFibre exteriorMass
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  have hxy : x.val.val ≠ a.y := by
    intro he
    apply x.property
    change x.val.val ∈ localSites a incoming
    rw [he]
    exact centre_mem_localSites a incoming
  cases next <;> simp [commonStatus, traceStep, hxy]

#print axioms finite_disintegration
#print axioms partition_disintegration

end AKLT.W.REC089
