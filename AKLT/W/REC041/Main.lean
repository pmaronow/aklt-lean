module
public import AKLT.Blueprint.Rec.NodesWalk
public import AKLT.W.REC041.Positivity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC041

private theorem traceRatio_list_telescope
    {G : Finset Plane} {n : ℕ} (D : Network G) (τ : PinAssignment G) (b : Bool)
    (l : List Plane) (hlen : l.length = n + 1) :
    traceRatio D τ b l =
      ∏ i : Fin n, stepRatio (traceNetwork D (l.take (i.val + 1))) τ b
        (l.get ⟨i.val, by omega⟩) (l.get ⟨i.val + 1, by omega⟩) := by
  induction n generalizing D l with
  | zero =>
      cases l with
      | nil => simp at hlen
      | cons y ys =>
          cases ys with
          | nil =>
              have hp := network_partition_pos D τ b
              simp [traceRatio, traceNetwork, ne_of_gt hp]
          | cons z zs => simp at hlen
  | succ n ih =>
      cases l with
      | nil => simp at hlen
      | cons y ys =>
          cases ys with
          | nil => simp at hlen
          | cons o rest =>
              have htail : (o :: rest).length = n + 1 := by
                simp only [List.length_cons] at hlen ⊢
                omega
              let D' := traceStep D y o
              have hrec := ih D' (o :: rest) htail
              have hden0 : D.partition τ b (fun _ => 1) ≠ 0 :=
                ne_of_gt (network_partition_pos D τ b)
              have hden1 : D'.partition τ b (fun _ => 1) ≠ 0 :=
                ne_of_gt (network_partition_pos D' τ b)
              have hquot :
                  traceRatio D τ b (y :: o :: rest) =
                    stepRatio D τ b y o * traceRatio D' τ b (o :: rest) := by
                simp only [traceRatio, traceNetwork, stepRatio]
                field_simp [hden0, hden1]
                simp [D']
                ring
              rw [hquot, hrec]
              simp only [Fin.prod_univ_succ]
              congr 1

/-- The normalizers are positive even for arbitrary intermediate networks;
the ratios therefore telescope, including the empty product. -/
theorem main : AKLT.Blueprint.Rec.TraceTelescopeStatement := by
  intro G τ D _ u _ T n w _ b
  have hlen : (wordVertices u w).length = n + 1 := by
    simp [wordVertices]
  have ht := traceRatio_list_telescope D τ b (wordVertices u w) hlen
  have hget (i : Fin (n + 1)) :
      (wordVertices u w).get ⟨i.val, by simpa [hlen] using i.isLt⟩ =
        wordVertex u w i.val := by
    simp [wordVertices]
  rw [ht]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [prefixNetwork]
  rw [hget ⟨i.val, by omega⟩, hget ⟨i.val + 1, by omega⟩]

#print axioms main

end AKLT.W.REC041
