module
public import AKLT.W.H1C031.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Fixed-width decoding and recovery of the effective template data. -/

namespace AKLT.W.H1C031

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

def orientedStatusDigits (π : PatternData) (reflect : Bool) : List Nat :=
  ringSites.map fun x =>
    let y := reflectPoint reflect x
    if patternDegree π y == 0 then 0 else statusDigit (π.statusAt y)

def orientedEdgeDigits (π : PatternData) (reflect : Bool) : List Nat :=
  templateEdges.map fun (a,b) =>
    (presentBond π (reflectPoint reflect a) (reflectPoint reflect b)).toNat

def orientedOutgoingDigit (π : PatternData) (reflect : Bool) : Nat :=
  if π.outgoing == .north then 1
  else if (π.outgoing == .east) != reflect then 0 else 2

theorem orientedCode_formula (π : PatternData) (reflect : Bool) :
    reflectedPatternCode π reflect =
      (encodeDigits 3 (orientedStatusDigits π reflect) * 65536 +
        encodeDigits 2 (orientedEdgeDigits π reflect)) * 3 +
          orientedOutgoingDigit π reflect := by
  rfl

theorem encodeDigits_lt_of_digits {base : Nat} (xs : List Nat)
    (h : ∀ a ∈ xs, a < base) : encodeDigits base xs < base ^ xs.length := by
  induction xs with
  | nil => simp [encodeDigits]
  | cons a as ih =>
      have ha : a < base := h a (by simp)
      have htail : ∀ b ∈ as, b < base := by
        intro b hb
        exact h b (by simp [hb])
      simp only [encodeDigits, List.length_cons]
      have hi := ih htail
      have hb : 0 < base := by omega
      have hstep : encodeDigits base as + 1 ≤ base ^ as.length := Nat.succ_le_of_lt hi
      have hmul := Nat.mul_le_mul_left base hstep
      have hpow : base * base ^ as.length = base ^ (as.length + 1) := by
        rw [pow_succ]
        exact Nat.mul_comm _ _
      calc
        a + base * encodeDigits base as < base * (encodeDigits base as + 1) := by
          rw [Nat.mul_add]
          omega
        _ ≤ base * base ^ as.length := hmul
        _ = base ^ (as.length + 1) := hpow

theorem encodeDigits_inj_fixed {base : Nat} (hb : 0 < base)
    {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hxs : ∀ a ∈ xs, a < base) (hys : ∀ a ∈ ys, a < base)
    (heq : encodeDigits base xs = encodeDigits base ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b bs => simp at hlen
  | cons a as ih =>
      cases ys with
      | nil => simp at hlen
      | cons b bs =>
          have hheadA : a < base := hxs a (by simp)
          have hheadB : b < base := hys b (by simp)
          have hhead : a = b := by
            have hm := congrArg (fun n => n % base) heq
            simp only [encodeDigits, Nat.add_mod, Nat.mul_mod_right,
              Nat.add_zero,
              Nat.mod_eq_of_lt hheadA, Nat.mod_eq_of_lt hheadB] at hm
            exact hm
          have htail : encodeDigits base as = encodeDigits base bs := by
            have h := heq
            simp only [encodeDigits] at h
            rw [hhead] at h
            have hmul : base * encodeDigits base as = base * encodeDigits base bs := by omega
            exact Nat.eq_of_mul_eq_mul_left hb hmul
          have hlen' : as.length = bs.length := by simpa using hlen
          have hxs' : ∀ x ∈ as, x < base := by
            intro x hx
            exact hxs x (by simp [hx])
          have hys' : ∀ x ∈ bs, x < base := by
            intro x hx
            exact hys x (by simp [hx])
          have htailEq := ih (ys := bs) hlen' hxs' hys' htail
          subst b
          simp [htailEq]

theorem statusDigits_bounded (π : PatternData) (f : Bool) :
    ∀ d ∈ orientedStatusDigits π f, d < 3 := by
  intro d hd
  simp only [orientedStatusDigits, List.mem_map] at hd
  rcases hd with ⟨x, -, rfl⟩
  split
  · norm_num
  · cases π.statusAt (reflectPoint f x) <;> norm_num [statusDigit]

theorem edgeDigits_bounded (π : PatternData) (f : Bool) :
    ∀ d ∈ orientedEdgeDigits π f, d < 2 := by
  intro d hd
  simp only [orientedEdgeDigits, List.mem_map] at hd
  rcases hd with ⟨e, -, rfl⟩
  cases presentBond π (reflectPoint f e.1) (reflectPoint f e.2) <;> simp

theorem statusDigit_getD {π : PatternData} {f : Bool} {i : Nat}
    (hi : i < ringSites.length) :
    (orientedStatusDigits π f).getD i 0 =
      (if patternDegree π (reflectPoint f (ringSites.getD i (0, 0))) == 0 then 0
        else statusDigit (π.statusAt (reflectPoint f (ringSites.getD i (0, 0))))) := by
  simp [orientedStatusDigits, hi]

theorem edgeDigit_getD {π : PatternData} {f : Bool} {i : Nat}
    (hi : i < templateEdges.length) :
    (orientedEdgeDigits π f).getD i 0 =
      (presentBond π
        (reflectPoint f (templateEdges.getD i ((0, 0), (0, 0))).1)
        (reflectPoint f (templateEdges.getD i ((0, 0), (0, 0))).2)).toNat := by
  simp [orientedEdgeDigits, hi]

theorem orientedCode_eq_digits {π ρ : PatternData} {f g : Bool}
    (h : reflectedPatternCode π f = reflectedPatternCode ρ g) :
    orientedStatusDigits π f = orientedStatusDigits ρ g ∧
    orientedEdgeDigits π f = orientedEdgeDigits ρ g ∧
    orientedOutgoingDigit π f = orientedOutgoingDigit ρ g := by
  rw [orientedCode_formula, orientedCode_formula] at h
  have heA := encodeDigits_lt_of_digits (orientedEdgeDigits π f)
    (edgeDigits_bounded π f)
  have heB := encodeDigits_lt_of_digits (orientedEdgeDigits ρ g)
    (edgeDigits_bounded ρ g)
  have heA' : encodeDigits 2 (orientedEdgeDigits π f) < 65536 := by
    simpa [orientedEdgeDigits, templateEdges] using heA
  have heB' : encodeDigits 2 (orientedEdgeDigits ρ g) < 65536 := by
    simpa [orientedEdgeDigits, templateEdges] using heB
  have hoA : orientedOutgoingDigit π f < 3 := by
    cases hdir : π.outgoing <;> cases f <;> simp [orientedOutgoingDigit, hdir]
  have hoB : orientedOutgoingDigit ρ g < 3 := by
    cases hdir : ρ.outgoing <;> cases g <;> simp [orientedOutgoingDigit, hdir]
  have hparts :
      encodeDigits 3 (orientedStatusDigits π f) * 65536 +
          encodeDigits 2 (orientedEdgeDigits π f) =
        encodeDigits 3 (orientedStatusDigits ρ g) * 65536 +
          encodeDigits 2 (orientedEdgeDigits ρ g) ∧
      orientedOutgoingDigit π f = orientedOutgoingDigit ρ g := by
    omega
  have hedges : encodeDigits 2 (orientedEdgeDigits π f) =
      encodeDigits 2 (orientedEdgeDigits ρ g) := by omega
  have hstatuses : encodeDigits 3 (orientedStatusDigits π f) =
      encodeDigits 3 (orientedStatusDigits ρ g) := by omega
  have hlenS : (orientedStatusDigits π f).length =
      (orientedStatusDigits ρ g).length := by simp [orientedStatusDigits]
  have hlenE : (orientedEdgeDigits π f).length =
      (orientedEdgeDigits ρ g).length := by simp [orientedEdgeDigits]
  have hS := encodeDigits_inj_fixed (base := 3) (by omega) hlenS
    (statusDigits_bounded π f) (statusDigits_bounded ρ g) hstatuses
  have hE := encodeDigits_inj_fixed (base := 2) (by omega) hlenE
    (edgeDigits_bounded π f) (edgeDigits_bounded ρ g) hedges
  exact ⟨hS, hE, hparts.2⟩

theorem outgoing_of_orientedDigits {π ρ : PatternData}
    (hπ : π.Covered) (hρ : ρ.Covered) {f g : Bool}
    (h : orientedOutgoingDigit π f = orientedOutgoingDigit ρ g) :
    (if f = g then π.outgoing = ρ.outgoing
      else π.outgoing.step = reflectPoint true ρ.outgoing.step) := by
  have hπs : π.outgoing ≠ .south := hπ.1
  have hρs : ρ.outgoing ≠ .south := hρ.1
  cases hdπ : π.outgoing <;> cases hdρ : ρ.outgoing <;>
    cases f <;> cases g <;>
    simp [orientedOutgoingDigit, reflectPoint, hdπ, hdρ] at h ⊢ <;> aesop

/-- Semantic recovery from equal fixed-width lists in the same orientation. -/
def Residual_sameTemplateRecovery : Prop :=
  ∀ π ρ : PatternData, π.Covered → ρ.Covered → ∀ f : Bool,
    orientedStatusDigits π f = orientedStatusDigits ρ f →
    orientedEdgeDigits π f = orientedEdgeDigits ρ f →
      π.bonds = ρ.bonds ∧
      ∀ x : Plane, 0 < patternDegree π x → π.statusAt x = ρ.statusAt x

/-- Reflected recovery of present bonds and live-site statuses. -/
def Residual_crossTemplateRecovery : Prop :=
  ∀ π ρ : PatternData, π.Covered → ρ.Covered → ∀ f g : Bool, f ≠ g →
    orientedStatusDigits π f = orientedStatusDigits ρ g →
    orientedEdgeDigits π f = orientedEdgeDigits ρ g →
      (∀ a b : Plane, presentBond π a b =
        presentBond ρ (reflectPoint true a) (reflectPoint true b)) ∧
      ∀ x : Plane, 0 < patternDegree π x →
        π.statusAt x = ρ.statusAt (reflectPoint true x)

theorem orientedEdgeDigits_eq_on {π ρ : PatternData} {f g : Bool}
    (h : orientedEdgeDigits π f = orientedEdgeDigits ρ g)
    {a b : Plane} (hab : (a, b) ∈ templateEdges) :
    presentBond π (reflectPoint f a) (reflectPoint f b) =
      presentBond ρ (reflectPoint g a) (reflectPoint g b) := by
  have he := List.map_inj_left.mp h (a, b) hab
  change (presentBond π (reflectPoint f a) (reflectPoint f b)).toNat =
    (presentBond ρ (reflectPoint g a) (reflectPoint g b)).toNat at he
  cases hp : presentBond π (reflectPoint f a) (reflectPoint f b) <;>
    cases hq : presentBond ρ (reflectPoint g a) (reflectPoint g b) <;>
    simp_all

theorem orientedPresentBond_eq {π ρ : PatternData} {f g : Bool}
    (h : orientedEdgeDigits π f = orientedEdgeDigits ρ g) (a b : Plane) :
    presentBond π (reflectPoint f a) (reflectPoint f b) =
      presentBond ρ (reflectPoint g a) (reflectPoint g b) := by
  by_cases ht : (a, b) ∈ templateEdges ∨ (b, a) ∈ templateEdges
  · rcases ht with ht | ht
    · exact orientedEdgeDigits_eq_on h ht
    · rw [presentBond_symm π, presentBond_symm ρ]
      exact orientedEdgeDigits_eq_on h ht
  · have absent (σ : PatternData) (k : Bool) :
        presentBond σ (reflectPoint k a) (reflectPoint k b) = false := by
      cases he : presentBond σ (reflectPoint k a) (reflectPoint k b)
      · rfl
      · have hm := reflect_templateEdge k (presentBond_templateEdge he)
        simp only [reflectPoint_involution] at hm
        exact (ht hm).elim
    rw [absent π f, absent ρ g]

theorem statusDigit_injective : Function.Injective statusDigit := by
  intro a b h
  cases a <;> cases b <;> simp_all [statusDigit]

theorem orientedStatusDigits_eq_live {π ρ : PatternData} {f g : Bool}
    (h : orientedStatusDigits π f = orientedStatusDigits ρ g)
    {x : Plane} (hm : x ∈ ringSites) (hx : 0 < patternDegree π x) :
    π.statusAt x = ρ.statusAt (reflectPoint g (reflectPoint f x)) := by
  have he := List.map_inj_left.mp h (reflectPoint f x) (reflect_ringSite f hm)
  change (if patternDegree π (reflectPoint f (reflectPoint f x)) == 0 then 0
      else statusDigit (π.statusAt (reflectPoint f (reflectPoint f x)))) =
    (if patternDegree ρ (reflectPoint g (reflectPoint f x)) == 0 then 0
      else statusDigit (ρ.statusAt (reflectPoint g (reflectPoint f x)))) at he
  have hnπ : patternDegree π x ≠ 0 := Nat.ne_of_gt hx
  simp only [reflectPoint_involution, beq_iff_eq, hnπ, ↓reduceIte] at he
  have hnstatus := (positiveDegree_site_status hx).2
  have hnonzero : statusDigit (π.statusAt x) ≠ 0 := by
    intro hz
    apply hnstatus
    apply statusDigit_injective
    exact hz
  by_cases hz : patternDegree ρ (reflectPoint g (reflectPoint f x)) = 0
  · simp only [hz, ↓reduceIte] at he
    exact (hnonzero he).elim
  · apply statusDigit_injective
    simpa only [beq_iff_eq, hz, ↓reduceIte] using he

theorem sameTemplateRecovery : Residual_sameTemplateRecovery := by
  intro π ρ hπ hρ f hs he
  have hb : ∀ a b, presentBond π a b = presentBond ρ a b := by
    intro a b
    have h := orientedPresentBond_eq he (reflectPoint f a) (reflectPoint f b)
    simpa only [reflectPoint_involution] using h
  refine ⟨bonds_eq_of_presentBond_eq hb, ?_⟩
  intro x hx
  rcases templateSite_cases (positiveDegree_site_status hx).1 with h0 | hm | ht
  · subst x
    exact hπ.2.1.trans hρ.2.1.symm
  · simpa only [reflectPoint_involution] using orientedStatusDigits_eq_live hs hm hx
  · exact (hπ.2.2.2.2.2.2.2.2.1 x ht).trans
      (hρ.2.2.2.2.2.2.2.2.1 x ht).symm

theorem crossTemplateRecovery : Residual_crossTemplateRecovery := by
  intro π ρ hπ hρ f g hfg hs he
  have hcomp (x : Plane) : reflectPoint g (reflectPoint f x) = reflectPoint true x := by
    cases f <;> cases g <;> simp_all [reflectPoint]
  constructor
  · intro a b
    have h := orientedPresentBond_eq he (reflectPoint f a) (reflectPoint f b)
    simpa only [reflectPoint_involution, hcomp] using h
  · intro x hx
    rcases templateSite_cases (positiveDegree_site_status hx).1 with h0 | hm | ht
    · subst x
      have h0 : reflectPoint true (0, 0) = (0, 0) := by
        norm_num [reflectPoint]
      rw [h0]
      exact hπ.2.1.trans hρ.2.1.symm
    · simpa only [hcomp] using orientedStatusDigits_eq_live hs hm hx
    · exact (hπ.2.2.2.2.2.2.2.2.1 x ht).trans
        (hρ.2.2.2.2.2.2.2.2.1 (reflectPoint true x) (reflect_tip true ht)).symm

theorem main_from_residuals
    (hs : Residual_sameTemplateRecovery) (hc : Residual_crossTemplateRecovery) :
    AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification := by
  intro π ρ hπ hρ hcode
  unfold effectivePatternCode at hcode
  by_cases hp : reflectedPatternCode π false ≤ reflectedPatternCode π true
  · by_cases hr : reflectedPatternCode ρ false ≤ reflectedPatternCode ρ true
    · have hselected : reflectedPatternCode π false = reflectedPatternCode ρ false := by
        simpa [Nat.min_eq_left hp, Nat.min_eq_left hr] using hcode
      have hd := orientedCode_eq_digits hselected
      rcases hd with ⟨hstatus, hrest⟩
      rcases hrest with ⟨hedge, hout⟩
      have hdata := hs π ρ hπ hρ false hstatus hedge
      exact Or.inl ⟨outgoing_of_orientedDigits hπ hρ hout, hdata.1, hdata.2⟩
    · have hselected : reflectedPatternCode π false = reflectedPatternCode ρ true := by
        simpa [Nat.min_eq_left hp, Nat.min_eq_right (Nat.le_of_not_ge hr)] using hcode
      have hd := orientedCode_eq_digits hselected
      rcases hd with ⟨hstatus, hrest⟩
      rcases hrest with ⟨hedge, hout⟩
      have hdata := hc π ρ hπ hρ false true (by decide) hstatus hedge
      exact Or.inr ⟨outgoing_of_orientedDigits hπ hρ hout, hdata.1, hdata.2⟩
  · by_cases hr : reflectedPatternCode ρ false ≤ reflectedPatternCode ρ true
    · have hselected : reflectedPatternCode π true = reflectedPatternCode ρ false := by
        simpa [Nat.min_eq_right (Nat.le_of_not_ge hp), Nat.min_eq_left hr] using hcode
      have hd := orientedCode_eq_digits hselected
      rcases hd with ⟨hstatus, hrest⟩
      rcases hrest with ⟨hedge, hout⟩
      have hdata := hc π ρ hπ hρ true false (by decide) hstatus hedge
      exact Or.inr ⟨outgoing_of_orientedDigits hπ hρ hout, hdata.1, hdata.2⟩
    · have hselected : reflectedPatternCode π true = reflectedPatternCode ρ true := by
        simpa [Nat.min_eq_right (Nat.le_of_not_ge hp), Nat.min_eq_right (Nat.le_of_not_ge hr)] using hcode
      have hd := orientedCode_eq_digits hselected
      rcases hd with ⟨hstatus, hrest⟩
      rcases hrest with ⟨hedge, hout⟩
      have hdata := hs π ρ hπ hρ true hstatus hedge
      exact Or.inl ⟨outgoing_of_orientedDigits hπ hρ hout, hdata.1, hdata.2⟩

theorem main : AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification :=
  main_from_residuals sameTemplateRecovery crossTemplateRecovery

end AKLT.W.H1C031

#print axioms AKLT.W.H1C031.orientedCode_formula
#print axioms AKLT.W.H1C031.encodeDigits_lt_of_digits
#print axioms AKLT.W.H1C031.encodeDigits_inj_fixed
#print axioms AKLT.W.H1C031.statusDigits_bounded
#print axioms AKLT.W.H1C031.edgeDigits_bounded
#print axioms AKLT.W.H1C031.statusDigit_getD
#print axioms AKLT.W.H1C031.edgeDigit_getD
#print axioms AKLT.W.H1C031.orientedCode_eq_digits
#print axioms AKLT.W.H1C031.outgoing_of_orientedDigits
#print axioms AKLT.W.H1C031.main_from_residuals
#print axioms AKLT.W.H1C031.orientedEdgeDigits_eq_on
#print axioms AKLT.W.H1C031.orientedPresentBond_eq
#print axioms AKLT.W.H1C031.statusDigit_injective
#print axioms AKLT.W.H1C031.orientedStatusDigits_eq_live
#print axioms AKLT.W.H1C031.sameTemplateRecovery
#print axioms AKLT.W.H1C031.crossTemplateRecovery
#print axioms AKLT.W.H1C031.main

#check (AKLT.W.H1C031.main : AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification)
