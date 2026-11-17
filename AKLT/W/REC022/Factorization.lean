module
public import AKLT.W.REC022.Trace
public import AKLT.W.REC022.Normalize

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC022

theorem three_integrated (a : Departure) (hU : a.D.status a.y = .U)
    (f g : Plane) (hn : a.D.presentNeighbours a.y = {a.o,f,g})
    (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g) (b : Bool) :
    a.D.partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun n => scalarI n a.o f g) ∧
    (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) =
      (removeSite a.D a.y).partition a.τ b (fun n => scalarJ n f g) := by
  have hno : ∀ e ∈ originalLegs a.G, e.1 ≠ a.y := by
    intro e he hh
    apply a.start.2.1
    rw [← hh]
    exact leg_protected he
  have hyo : a.y ≠ a.o :=
    adjacent_ne ((mem_presentNeighbours a.D a.y a.o).mp a.present).2.2.1
  constructor
  · rw [integrate_site a.D a.τ b a.y a.start.1 hno]
    apply congrArg ((removeSite a.D a.y).partition a.τ b)
    funext n
    rw [hU,hn]
    have hp : (fun v : Vec3 => ∏ z ∈ ({a.o,f,g} : Finset Plane),
        (1 + dot v (n z))) =
        (fun v => (1 + dot v (n f)) * (1 + dot v (n g)) * (1 + dot v (n a.o))) := by
      funext v
      simp [hof,hog,hfg]
      ring
    rw [hp,site_U_three]
    rfl
  · have hat : a.y ∈ (traceStep a.D a.y a.o).active := by
      rw [active_trace a.D a.y a.o hU]
      exact a.start.1
    have hnt : (traceStep a.D a.y a.o).presentNeighbours a.y = {f,g} := by
      rw [trace_neighbours a.D a.y a.o hU hyo,hn]
      simp [hof,hog]
    have hst : (traceStep a.D a.y a.o).status a.y = .D := by
      simp [traceStep,hU]
    rw [integrate_site (traceStep a.D a.y a.o) a.τ b a.y hat hno,
      remove_trace_partition]
    apply congrArg ((removeSite a.D a.y).partition a.τ b)
    funext n
    rw [hst,hnt]
    have hp : (fun v : Vec3 => ∏ z ∈ ({f,g} : Finset Plane),
        (1 + dot v (n z))) = (fun v => (1 + dot v (n f)) * (1 + dot v (n g))) := by
      funext v
      simp [hfg]
    rw [hp,site_D_two]
    rfl

/-- The finite-spin partition calculation, including the case of zero normalizers. -/
theorem three_factorization : ThreeFactorizationStatement := by
  intro a hU f g hn hof hog hfg b
  obtain ⟨hI,hJ⟩ := three_integrated a hU f g hn hof hog hfg b
  exact ⟨hI.trans (scalarI_partition a.D a.τ b a.y a.o f g),
    hJ.trans (scalarJ_partition a.D a.τ b a.y f g)⟩

theorem step_log_ratio (a : Departure) (hU : a.D.status a.y = .U)
    (f g : Plane) (hn : a.D.presentNeighbours a.y = {a.o,f,g})
    (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g) (b : Bool) :
    Real.log (stepRatio a.D a.τ b a.y a.o) =
      Real.log (responseJ a.D a.τ b a.y f g / responseI a.D a.τ b a.y a.o f g) := by
  obtain ⟨hI,hJ⟩ := three_factorization a hU f g hn hof hog hfg b
  by_cases hz : (removeSite a.D a.y).partition a.τ b (fun _ => 1) = 0
  · have hri : responseI a.D a.τ b a.y a.o f g = 1 := by
      simp [responseI,removedPairMean,Network.expectation,hz]
    have hrj : responseJ a.D a.τ b a.y f g = 1 := by
      simp [responseJ,removedPairMean,Network.expectation,hz]
    change Real.log ((traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) /
      a.D.partition a.τ b (fun _ => 1)) = _
    rw [hI,hJ,hz,hri,hrj]
    simp
  · congr 1
    change (traceStep a.D a.y a.o).partition a.τ b (fun _ => 1) /
      a.D.partition a.τ b (fun _ => 1) = _
    rw [hI,hJ]
    field_simp

end AKLT.W.REC022
