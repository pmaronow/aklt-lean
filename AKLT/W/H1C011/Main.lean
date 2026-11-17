module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C011

open AKLT.Cert.H1.Production

private theorem bundlesAccepted_lookup (c : Case) :
    ∀ bs : List Bundle, BundlesAccepted c bs →
      ∀ b : Bundle, b ∈ bs → b.Accepted c := by
  intro bs
  induction bs with
  | nil =>
      intro h b hb
      cases hb
  | cons head tail ih =>
      intro h b hb
      change head.Accepted c ∧ BundlesAccepted c tail at h
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact h.1
      · exact ih h.2 b hb

theorem main : AKLT.Cert.H1.Production.Leaves.acceptedLookup := by
  intro c hc b hb
  exact bundlesAccepted_lookup c c.bundles hc b hb

end AKLT.W.H1C011
