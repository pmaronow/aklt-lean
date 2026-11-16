import AKLT.Blueprint.Rec.NodesWalk
open scoped BigOperators
open AKLT.Defs
example (u : Fin 2 → Vec3) (n : Vec3) (i : Fin 2) :
    (∏ j ∈ Finset.univ.erase i, (1 + dot n (u j))) =
      if i = 0 then 1 + dot n (u 1) else 1 + dot n (u 0) := by
  fin_cases i <;> simp [Finset.univ, Finset.erase, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Finset.prod_insert] <;> ring

example (u : Fin 3 → Vec3) (n : Vec3) (i : Fin 3) :
    (∏ j ∈ Finset.univ.erase i, (1 + dot n (u j))) =
      if i = 0 then (1 + dot n (u 1)) * (1 + dot n (u 2)) else
      if i = 1 then (1 + dot n (u 0)) * (1 + dot n (u 2)) else
        (1 + dot n (u 0)) * (1 + dot n (u 1)) := by
  fin_cases i <;> simp [Finset.univ, Finset.erase, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Finset.prod_insert] <;> ring
