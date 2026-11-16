import CertData.H3.Bridge.Interface

namespace AKLT.W.H3C014

open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs

private theorem fieldCheck_sound (G : Graph) (a : Nat)
    (h : fieldCheck G a = true) (d : Compass) :
    G.dest a (directionCode d) ≤ 3741 ∧
      (G.dest a (directionCode d) = 0 ↔ G.kind a (directionCode d) = 3) ∧
      (G.dest a (directionCode d) ≠ 0 → G.kind a (directionCode d) < 3) := by
  have hall : dirs.all (fun d => decide
      (G.dest a d ≤ 3741 ∧ (G.dest a d = 0 ↔ G.kind a d = 3) ∧
        (G.dest a d ≠ 0 → G.kind a d < 3))) = true := by
    simpa [fieldCheck] using h
  have hd : directionCode d ∈ dirs := by
    cases d <;> simp [directionCode, dirs]
  exact of_decide_eq_true ((List.all_eq_true.mp hall) _ hd)

theorem main : CertData.H3.Bridge.FieldCheckSoundLeaf := by
  intro G hbatch a d
  have hall : ∀ i < 3741, fieldCheck G i = true := by
    simpa [fieldBatch] using hbatch
  exact fieldCheck_sound G a.val (hall a.val a.isLt) d

#print axioms main

end AKLT.W.H3C014
