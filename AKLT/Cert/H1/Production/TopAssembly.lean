import AKLT.Cert.H1.Production.TopLeaves

namespace AKLT.Cert.H1.Production.TopAssembly
open AKLT.Defs
open scoped BigOperators ComplexOrder
theorem integerCheck_of_leaves
    (h : TopLeaves.integerCheckPremises) : AKLT.Blueprint.Top.IntegerCheckStatement := by
  rcases h with ⟨hentries, hscale, hpositive, hsylvester, hbareiss⟩
  constructor
  · intro π hπ r I hI D₀ hD p q hp hq hratio ε
    exact ⟨hentries π hπ r I hI D₀ hD ε,
      hscale π hπ r I hI D₀ hD p q hp hq hratio ε,
      hpositive π hπ r I hI D₀ hD p q hp hq hratio ε⟩
  · intro n M hM
    exact ⟨hsylvester n M hM, hbareiss n M hM⟩

theorem certificate_of_leaves
    (h : TopLeaves.certificatePremises) : AKLT.Blueprint.Top.CertificateStatement := by
  rcases h with ⟨hentries, hbound⟩
  intro π hπ r I hI D₀ hD p q hp hq hratio hcert
  apply hbound π hπ r I hI D₀ hD p q hp hq hratio
  intro ε
  obtain ⟨t, index, g, d, S, L, _htri, hrows⟩ := hcert ε
  refine ⟨t, index, ?_⟩
  have hcur := (hentries π hπ r I hI D₀ hD ε false).1
  have hnext := (hentries π hπ r I hI D₀ hD ε true).1
  have hsym : (indexedSectorMatrix π r ε I D₀ p q index).IsSymm :=
    ((hcur.smul (5 * (q : ℤ))).sub (hnext.smul (3 * (p : ℤ)))).submatrix index
  obtain ⟨hg, hd, hS, hdd⟩ := hrows
  change (AKLT.Gen.Gram.castMatrix (indexedSectorMatrix π r ε I D₀ p q index) :
    Matrix (Fin t) (Fin t) ℂ).PosDef
  exact (AKLT.Gen.Gram.int_gram_residual_posDef hsym
    (by exact_mod_cast hg) (by exact_mod_cast hd) (by exact_mod_cast hS)
    (fun i => (hdd i).2)).2

/-- Both exact requested targets, conditional on the named closed mathematical leaves. -/
theorem targets_of_leaves
    (hI : TopLeaves.integerCheckPremises) (hC : TopLeaves.certificatePremises) :
    AKLT.Blueprint.Top.IntegerCheckStatement ∧ AKLT.Blueprint.Top.CertificateStatement :=
  ⟨integerCheck_of_leaves hI, certificate_of_leaves hC⟩


#print axioms integerCheck_of_leaves
#print axioms certificate_of_leaves
#print axioms targets_of_leaves
end AKLT.Cert.H1.Production.TopAssembly
