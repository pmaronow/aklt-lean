module
public import AKLT.W.REC082.PE.Trace

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082.PE

/-- Finite choice tree. Only terminal values of F are used. Fuel counts
available departures, and an exhausted nonterminal branch contributes zero. -/
def branchSum {G : Finset Plane} (D : Network G) (T : Finset Plane)
    (F : Network G → Plane → ℝ) : ℕ → Plane → ℝ
  | 0, u => if u ∈ T then F D u else 0
  | m + 1, u => if u ∈ T then F D u else
      (if D.status u = .U then (1 / 3 : ℝ) else 1 / 5) *
        ∑ o ∈ D.presentNeighbours u, branchSum (traceStep D u o) T F m o

/-- This residual is local: summing the departure spin first must implement
the proved U/D moment identities inside the dependent product partition. -/
def LocalPartitionResidual : Prop := CoordinateStepStatement

private theorem neighbours_empty_of_bonds_card_zero {G : Finset Plane}
    {D : Network G} (h : D.bonds.card = 0) (u : Plane) : D.presentNeighbours u = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro o ho
  have hp := (Finset.mem_filter.mp ho).2
  have hc := traceStep_bonds_card_lt hp
  omega

/-- Iteration of local unnormalized coordinate identities, including dead
branches. The induction uses only a finite fuel at least the current bond count. -/
theorem coordinate_eq_branchSum (hStep : LocalPartitionResidual)
    {G : Finset Plane} (τ : PinAssignment G) (b : Bool) (v : Plane) (k : Fin 3)
    (m : ℕ) (D : Network G) (hD : D.Auxiliary) (u : Plane)
    (hu : u ∈ insert v (protectedSites G) ∨ D.AdmissibleStart u)
    (hv : AdmissibleTarget D v) (hm : D.bonds.card ≤ m) :
    D.partition τ b (fun a => a u k * a v k) =
      branchSum D (insert v (protectedSites G))
        (fun E e => E.partition τ b (fun a => a e k * a v k)) m u := by
  induction m generalizing D u with
  | zero =>
    by_cases ht : u ∈ insert v (protectedSites G)
    · simp [branchSum, ht]
    · have hstart : D.AdmissibleStart u := hu.resolve_left ht
      have hne : u ≠ v := fun he => ht (he ▸ Finset.mem_insert_self _ _)
      have he := neighbours_empty_of_bonds_card_zero (by omega : D.bonds.card = 0) u
      rw [hStep G τ D hD u v hstart hv hne b k, he]
      simp [branchSum, ht]
  | succ m ih =>
    by_cases ht : u ∈ insert v (protectedSites G)
    · simp [branchSum, ht]
    · have hstart : D.AdmissibleStart u := hu.resolve_left ht
      have hne : u ≠ v := fun he => ht (he ▸ Finset.mem_insert_self _ _)
      rw [branchSum, if_neg ht, hStep G τ D hD u v hstart hv hne b k]
      congr 1
      apply Finset.sum_congr rfl
      intro o ho
      have hp : D.Present u o := (Finset.mem_filter.mp ho).2
      apply ih (traceStep D u o) (traceStep_auxiliary hD hstart hp) o
      · by_cases hterm : o ∈ insert v (protectedSites G)
        · exact Or.inl hterm
        · apply Or.inr
          apply traceStep_start hD hp
          exact fun hs => hterm (Finset.mem_insert_of_mem hs)
      · exact traceStep_target hv hne
      · have hc := traceStep_bonds_card_lt hp
        omega

end AKLT.W.REC082.PE
