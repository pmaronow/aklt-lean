import CertData.H3.Bridge.Interface

namespace CertData.H3.Bridge
open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs

/-- Interface supplied by each generated case assembly after local refinement. -/
def CaseChecks (G : Graph) (T : Tables) (E : Exact) (r : PrefixResult)
    (X : PairType) (d₀ : Compass) : Prop :=
  (∀ (φ : Phase) (a : Fin 3741), planeCheck G T X d₀ (phaseKey (phaseCode φ) a.val)=true) ∧
  stationaryPrefixBound G.quotient X d₀ T.data=resultValue E r ∧
  ceilingCheck E r (stationaryPrefixCeiling X d₀)=true

def FamilyChecks (G : Graph) (C : PairType × Compass → Tables) (E : Exact)
    (R : PairType × Compass → PrefixResult) : Prop :=
  ∀ k∈stationaryCases, CaseChecks G (C k) E (R k) k.1 k.2

/-- Proved assembly for the complete finite family, independently of literal modules.
The three items of CaseChecks are obtained from the generated row, prefix and
summary modules through their closed refinement leaves. -/
theorem stationaryV2_from_family_checks (G : Graph) (C : PairType × Compass → Tables)
    (E : Exact) (R : PairType × Compass → PrefixResult)
    (hQ : G.quotient=Automaton10Data.supplied) (hcorrect : G.quotient.Correct)
    (hE : ExactValid E) (hs : SharedCaseLeaves)
    (hsquare : (square (0,0) certificateRadius).card=19881)
    (h : FamilyChecks G C E R) : AKLT.Blueprint.Top.StationaryCheckStatementV2 := by
  have hc : ∀ X d, (X,d)∈stationaryCases → CaseV2 X d := by
    intro X d hk
    have hd := h (X,d) hk
    exact caseV2_of_checks G (C (X,d)) E X d (R (X,d)) (stationaryPrefixCeiling X d)
      hQ hcorrect hk hd.1 hd.2.1 hE hd.2.2 rfl hs
  exact stationaryV2_of_cases hsquare
    (Eq.mp (congrArg (fun Q : MemoryQuotient 10 3741 => Q.Correct) hQ) hcorrect)
    (hc .B .north (by decide +kernel)) (hc .B .west (by decide +kernel))
    (hc .C .north (by decide +kernel)) (hc .C .west (by decide +kernel))
    (hc .C .south (by decide +kernel))

#print axioms stationaryV2_from_family_checks
end CertData.H3.Bridge
