module
public import AKLT.W.REC043.Iteration
public import AKLT.W.REC043.Trails

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC043

attribute [local instance] Classical.propDecidable

private theorem word_vertices_head {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertices u w = u :: (List.range n).map (fun j => wordVertex u w (j + 1)) := by
  unfold wordVertices
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, word_vertex_zero, List.map_map, Function.comp_def]

@[simp] theorem trace_network_cons {G : Finset Plane} (D : Network G)
    {n : ℕ} (u : Plane) (d : Compass) (w : DirectionWord n) :
    traceNetwork D (wordVertices u (Fin.cons d w)) =
      traceNetwork (traceStep D u (u + d.step)) (wordVertices (u + d.step) w) := by
  rw [word_vertices_cons, word_vertices_head (u + d.step) w]
  rfl

@[simp] theorem trace_coefficient_cons {G : Finset Plane} {D : Network G}
    {n : ℕ} {u : Plane} (hu : D.AdmissibleStart u) (d : Compass) (w : DirectionWord n) :
    (traceCoefficient D (wordVertices u (Fin.cons d w)) : ℝ) =
      (if D.status u = .U then (1 / 3 : ℝ) else 1 / 5) *
        (traceCoefficient (traceStep D u (u + d.step))
          (wordVertices (u + d.step) w) : ℝ) := by
  rw [word_vertices_cons, word_vertices_head (u + d.step) w]
  simp only [traceCoefficient, Rat.cast_mul]
  rcases hu.2.2 with ⟨hs, _⟩ | ⟨hs, _⟩ <;> simp [hs]

private theorem compass_step_injective : Function.Injective Compass.step := by
  intro d e he
  cases d <;> cases e <;> simp_all [Compass.step]

private theorem sum_present_directions {G : Finset Plane} (D : Network G) (u : Plane)
    (f : Plane → ℝ) :
    (∑ d : Compass, if D.Present u (u + d.step) then f (u + d.step) else 0) =
      ∑ o ∈ D.presentNeighbors u, f o := by
  rw [Network.presentNeighbors, Finset.sum_filter, neighbors, Finset.sum_image]
  intro d hd e he hde
  exact compass_step_injective (add_left_cancel hde)

/-- One fixed length of the unnormalized stopped expansion. -/
def lengthTerm {G : Finset Plane} (D : Network G) (T : Finset Plane)
    (F : Network G → Plane → ℝ) (n : ℕ) (u : Plane) : ℝ :=
  ∑ w : DirectionWord n, if StoppedNetworkTrail D u T w then
    (traceCoefficient D (wordVertices u w) : ℝ) *
      F (traceNetwork D (wordVertices u w)) (wordVertex u w n) else 0

private theorem lengthTerm_zero {G : Finset Plane} (D : Network G) (T : Finset Plane)
    (F : Network G → Plane → ℝ) (u : Plane) :
    lengthTerm D T F 0 u = if u ∈ T then F D u else 0 := by
  classical
  have hi (w : DirectionWord 0) : Function.Injective (wordBond u w) := by
    intro i; exact Fin.elim0 i
  simp [lengthTerm, StoppedNetworkTrail, hi, wordVertices, traceCoefficient, traceNetwork]

private theorem lengthTerm_of_terminal {G : Finset Plane} (D : Network G)
    (T : Finset Plane) (F : Network G → Plane → ℝ) {u : Plane} (ht : u ∈ T) (n : ℕ) :
    lengthTerm D T F (n + 1) u = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro w hw
  have hn : ¬ StoppedNetworkTrail D u T w := by
    intro h
    have hh := (h.2.2.1 0 (by omega)).1
    exact hh (by simpa using ht)
  simp [hn]

/-- The finite stopped classes satisfy exactly the same first-step recursion
as the choice tree. Original legs play no role in this enumeration. -/
theorem lengthTerm_step {G : Finset Plane} {D : Network G} {u : Plane}
    (hu : D.AdmissibleStart u) {T : Finset Plane} (ht : u ∉ T)
    (F : Network G → Plane → ℝ) (n : ℕ) :
    lengthTerm D T F (n + 1) u =
      (if D.status u = .U then (1 / 3 : ℝ) else 1 / 5) *
        ∑ o ∈ D.presentNeighbors u, lengthTerm (traceStep D u o) T F n o := by
  classical
  unfold lengthTerm
  rw [sum_word_cons]
  let c : ℝ := if D.status u = .U then (1 / 3 : ℝ) else 1 / 5
  calc
    _ = ∑ d : Compass, c *
        (if D.Present u (u + d.step) then
          lengthTerm (traceStep D u (u + d.step)) T F n (u + d.step) else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp only [stopped_cons_iff hu ht, trace_coefficient_cons hu,
        trace_network_cons, word_vertex_cons]
      by_cases hp : D.Present u (u + d.step)
      · simp [hp, lengthTerm, c, Finset.mul_sum, mul_ite, mul_assoc]
      · simp [hp]
    _ = c * ∑ d : Compass, if D.Present u (u + d.step) then
        lengthTerm (traceStep D u (u + d.step)) T F n (u + d.step) else 0 := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_present_directions D u (fun o => lengthTerm (traceStep D u o) T F n o)]
      rfl

/-- The truncated direction-word sum; its bound is arbitrary during induction. -/
def boundedTrailSum {G : Finset Plane} (D : Network G) (T : Finset Plane)
    (F : Network G → Plane → ℝ) (m : ℕ) (u : Plane) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), lengthTerm D T F n u

private theorem boundedTrailSum_terminal {G : Finset Plane} (D : Network G)
    (T : Finset Plane) (F : Network G → Plane → ℝ) {u : Plane} (ht : u ∈ T) (m : ℕ) :
    boundedTrailSum D T F m u = F D u := by
  classical
  unfold boundedTrailSum
  rw [Finset.sum_eq_single 0]
  · simp [lengthTerm_zero, ht]
  · intro n hn hne
    cases n with
    | zero => exact (hne rfl).elim
    | succ n => exact lengthTerm_of_terminal D T F ht n
  · simp

/-- The actual finite trail enumeration equals the recursive choice tree,
for every terminal function. This proves the branch/trail bijection without
any hypothesis about partition functions or spin moments. -/
theorem branchSum_eq_boundedTrailSum {G : Finset Plane} (D : Network G)
    (hD : D.Auxiliary) (T : Finset Plane) (hT : protectedSites G ⊆ T)
    (F : Network G → Plane → ℝ) (m : ℕ) (u : Plane) (hu : u ∈ T ∨ D.AdmissibleStart u) :
    branchSum D T F m u = boundedTrailSum D T F m u := by
  classical
  induction m generalizing D u with
  | zero => simp [branchSum, boundedTrailSum, lengthTerm_zero]
  | succ m ih =>
    by_cases ht : u ∈ T
    · rw [boundedTrailSum_terminal D T F ht]
      simp [branchSum, ht]
    · have hstart := hu.resolve_left ht
      rw [branchSum, ite_eq_right ht]
      unfold boundedTrailSum
      rw [Finset.sum_range_succ']
      simp only [lengthTerm_zero, ht, ite_false, add_zero]
      simp_rw [lengthTerm_step hstart ht F]
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro o ho
      have hp := (Finset.mem_filter.mp ho).2
      apply ih (traceStep D u o) (traceStep_auxiliary hD hstart hp) o
      by_cases hterm : o ∈ T
      · exact Or.inl hterm
      · exact Or.inr (traceStep_start hD hp (fun hs => hterm (hT hs)))

end AKLT.W.REC043
