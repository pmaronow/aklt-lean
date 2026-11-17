module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C027

open AKLT.Cert.H1.Production

theorem find_some_mem_entries :
    ∀ (t : Catalogue) (x p : Nat),
      t.find x = some p → (x, p) ∈ t.entries := by
  intro t
  induction t with
  | empty =>
      intro x p h
      simp [Catalogue.find] at h
  | node key pid left right ihl ihr =>
      intro x p h
      by_cases heq : x = key
      · subst x
        simp [Catalogue.find] at h
        subst p
        simp [Catalogue.entries]
      · by_cases hlt : x < key
        · have hleft : left.find x = some p := by
            simpa [Catalogue.find, beq_iff_eq, heq, hlt] using h
          have hm := ihl x p hleft
          simp only [Catalogue.entries, List.mem_append]
          exact Or.inl (Or.inl hm)
        · have hright : right.find x = some p := by
            simpa [Catalogue.find, beq_iff_eq, heq, hlt] using h
          have hm := ihr x p hright
          simp only [Catalogue.entries, List.mem_append]
          exact Or.inr hm

theorem main : AKLT.Cert.H1.Production.Leaves.representativeLookup := by
  intro t rs hcheck key pid hfind
  have hentries : t.entries = rs.map (fun r => (r.key, r.pid)) := by
    simpa [AKLT.Cert.H1.Production.representativeCheck, beq_iff_eq] using hcheck
  have hmem : (key, pid) ∈ t.entries := find_some_mem_entries t key pid hfind
  rw [hentries] at hmem
  rcases List.mem_map.mp hmem with ⟨r, hr, hrEq⟩
  refine ⟨r, hr, ?_, ?_⟩
  · exact congrArg Prod.snd hrEq
  · exact congrArg Prod.fst hrEq

#print axioms main

end AKLT.W.H1C027
