module
public import AKLT.W.Q029.Ladder

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Blueprint.Q AKLT.Challenge

namespace AKLT.W.Q029

theorem pairU_on_diag_nat (m : ℕ) (hm : m < 9) :
    pairU (diagonalAdjointVector m) =
      if m = 0 then 0 else ((9 - m : ℕ) : ℂ) • diagonalAdjointVector (m - 1) := by
  cases m with
  | zero => simpa using pairU_zero
  | succ n =>
    have hn : n < 8 := by omega
    simpa [show 9 - (n + 1) = 8 - n by omega] using pairU_succ ⟨n, hn⟩

theorem pairD_on_diag_nat (m : ℕ) (hm : m < 9) :
    pairD (diagonalAdjointVector m) =
      ((m + 1 : ℕ) : ℂ) • diagonalAdjointVector (m + 1) :=
  pairD_on_diag ⟨m, hm⟩

theorem pairZ_on_diag_nat (m : ℕ) (hm : m < 9) :
    pairZ (diagonalAdjointVector m) =
      ((4 : ℂ) - (m : ℂ)) • diagonalAdjointVector m :=
  pairZ_on_diag ⟨m, hm⟩

/-- Each weighted diagonal coefficient vector has total spin four. -/
theorem diagonalAdjointVector_eigen (m : Fin 9) :
    diagonalAdjointVector m.val ∈ Module.End.eigenspace pairCasimir 20 := by
  rw [Module.End.mem_eigenspace_iff]
  change pairZ (pairZ (diagonalAdjointVector m.val)) + (1 / 2 : ℂ) •
    (pairU (pairD (diagonalAdjointVector m.val)) +
      pairD (pairU (diagonalAdjointVector m.val))) =
    (20 : ℂ) • diagonalAdjointVector m.val
  fin_cases m <;>
    norm_num [pairZ_on_diag_nat, pairD_on_diag_nat, pairU_on_diag_nat,
      diagonalAdjointVector_nine, map_smul, smul_smul, ← add_smul] <;> module

end AKLT.W.Q029
