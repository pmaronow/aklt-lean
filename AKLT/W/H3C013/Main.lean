import CertData.H3.Bridge.Interface

namespace AKLT.W.H3C013

theorem main : CertData.H3.Bridge.RepresentativeBoundsLeaf := by
  intro G hbatch a
  change (List.range 3741).all
    (fun i => AKLT.Cert.H3.Production.representativeCheck G (0 + i)) = true at hbatch
  have hmem : a.val ∈ List.range 3741 := List.mem_range.mpr a.isLt
  have hcheck : AKLT.Cert.H3.Production.representativeCheck G a.val = true := by
    have hall := (List.all_eq_true.mp hbatch) a.val hmem
    simpa using hall
  change (decide (G.representative a.val < 1048576) && _) = true at hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcheck
  have hlt : G.representative a.val < 1048576 := hcheck.1
  have hp : (4 : Nat) ^ 10 = 1048576 := by norm_num
  rw [hp]
  exact hlt

end AKLT.W.H3C013

#print axioms AKLT.W.H3C013.main
