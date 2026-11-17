module
public import AKLT.Blueprint.H1.NodesSector

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1M032

/-- The dimensions of a single, an exterior pair, and a symmetric pair. -/
def localDim (pair : Bool) (ext : Prop) [Decidable ext] : ℕ :=
  if pair then if ext then 1 else 3 else 2

/-- The displayed unnormalized integer vectors, in two spin coordinates.
The second coordinate is unused for a single. -/
def localVector (pair : Bool) (ext : Prop) [Decidable ext]
    (b : ℕ) (i j : Fin 2) : ℤ :=
  if pair then
    if ext then
      if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
    else if b = 0 then if i = 0 ∧ j = 0 then 1 else 0
    else if b = 1 then if i ≠ j then 1 else 0
    else if i = 1 ∧ j = 1 then 1 else 0
  else if i.val = b then 1 else 0

/-- The matrix induced by the sum of the identical one-spin actions.
On an exterior pair this is multiplication by the trace. -/
def localMatrix (pair : Bool) (ext : Prop) [Decidable ext]
    (A : Matrix (Fin 2) (Fin 2) ℂ) (c b : ℕ) : ℂ :=
  if pair then
    if ext then A 0 0 + A 1 1
    else if c = 0 then if b = 0 then 2 * A 0 0 else if b = 1 then 2 * A 0 1 else 0
    else if c = 1 then if b = 0 then A 1 0 else if b = 1 then A 0 0 + A 1 1 else A 0 1
    else if b = 0 then 0 else if b = 1 then 2 * A 1 0 else 2 * A 1 1
  else if c = 0 then if b = 0 then A 0 0 else A 0 1
    else if b = 0 then A 1 0 else A 1 1

theorem local_action (pair : Bool) (ext : Prop) [Decidable ext]
    (A : Matrix (Fin 2) (Fin 2) ℂ) (b : ℕ) (hb : b < localDim pair ext)
    (i j : Fin 2) :
    (∑ k : Fin 2, A i k * (localVector pair ext b k j : ℂ)) +
      (if pair then ∑ k : Fin 2, A j k * (localVector pair ext b i k : ℂ)
       else 0) =
    ∑ c ∈ Finset.range (localDim pair ext),
      localMatrix pair ext A c b * (localVector pair ext c i j : ℂ) := by
  have hd : localDim pair ext ≤ 3 := by
    cases pair <;> by_cases he : ext <;> simp [localDim, he]
  have hb' : b ≤ 2 := by omega
  interval_cases b <;> cases pair <;> by_cases he : ext
  all_goals simp [localDim, he] at hb
  all_goals
    fin_cases i <;> fin_cases j <;>
      simp [localVector, localMatrix, localDim, he,
        Fin.sum_univ_succ, Finset.sum_range_succ] <;> ring

end AKLT.W.H1M032
