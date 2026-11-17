module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed

namespace AKLT.W.H3C027

private theorem neighbors_zero :
    neighbors (0, 0) = {(1, 0), (0, 1), (-1, 0), (0, -1)} := by
  classical
  ext x
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨d, rfl⟩
    cases d <;> simp [Compass.step]
  · rintro (hx | hx | hx | hx)
    · subst x; exact ⟨.east, by simp [Compass.step]⟩
    · subst x; exact ⟨.north, by simp [Compass.step]⟩
    · subst x; exact ⟨.west, by simp [Compass.step]⟩
    · subst x; exact ⟨.south, by simp [Compass.step]⟩

private def straightReward : ℚ :=
  (1116773137017776286053 : ℚ) / 1125899906842624000000

private def turnReward : ℚ :=
  (4353214527893414821959 : ℚ) / 4503599627370496000000

private theorem relaxedReward_straight (d : Compass) :
    relaxedReward (0, 0) d d ∅ = straightReward := by
  cases d <;> decide +kernel

private theorem relaxedReward_turn {a d : Compass} (hne : d ≠ a) (hrev : d ≠ a.reverse) :
    relaxedReward (0, 0) a d ∅ = turnReward := by
  cases a <;> cases d <;> simp_all [Compass.reverse] <;> decide +kernel

private theorem diagonalCeil (φ : Phase) (k : StepKind) :
    coefficientCeiling (phaseDiagonal φ k) = diagonal φ k := by
  cases φ <;> cases k <;>
    norm_num [coefficientCeiling, certificateCoefficientScale, phaseDiagonal,
      diagonal, qs, qt, q3, q5, passageFactor, localThreshold]

private theorem straightResponseCeil (a : Compass) :
    coefficientCeiling (passageFactor true * straightReward / 3) =
      response (directionCode a) (directionCode a) 4 := by
  cases a <;>
    norm_num [coefficientCeiling, certificateCoefficientScale, straightReward,
      response, responseTable, directionCode, passageFactor, localThreshold]

private theorem turnResponseCeil {a d : Compass} (hne : d ≠ a) (hrev : d ≠ a.reverse) :
    coefficientCeiling (passageFactor false * turnReward / 3) =
      response (directionCode a) (directionCode d) 4 := by
  cases a <;> cases d <;> simp_all [Compass.reverse] <;>
    norm_num [coefficientCeiling, certificateCoefficientScale, turnReward,
      response, responseTable, directionCode, passageFactor, localThreshold]

private theorem allowed_straight_arrival (G : Graph) (hQ : G.quotient.Correct)
    {a : Fin 3741} {d : Compass}
    (ha : G.quotient.allowed a d = true)
    (hk : G.quotient.kind a d = .straight) : d = G.quotient.arrival a := by
  let Q := G.quotient
  let w := Q.representative a
  have hrep := hQ.1 a
  have hstep := hQ.2 w hrep.1 d
  have hadm : WindowAdmissible w d := by
    apply hstep.1.mp
    change Q.allowed (Q.project w) d = true
    rw [hrep.2]
    exact ha
  have hkind : windowKind w d = .straight := by
    calc
      windowKind w d = Q.kind (Q.project w) d := (hstep.2 hadm).1.symm
      _ = .straight := by rw [hrep.2]; exact hk
  have harr : Q.arrival a = windowArrival w := by
    have hnonrev : windowKind w d ≠ .revisit := by rw [hkind]; decide
    calc
      Q.arrival a = Q.arrival (Q.project w) := by rw [hrep.2]
      _ = windowArrival w := (hstep.2 hadm).2.2 hnonrev
  have hd : d = windowArrival w := by
    by_cases hr : 0 < departureCount (0, 0) w 10 (wordVertex (0, 0) w 10)
    · simp [windowKind, hr] at hkind
    · have heq : (if d = windowArrival w then StepKind.straight else StepKind.turn) =
          StepKind.straight := by simpa [windowKind, hr] using hkind
      by_cases hd : d = windowArrival w
      · exact hd
      · simp [hd] at heq
  simpa [Q] using hd.trans harr.symm

private theorem allowed_turn_facts (G : Graph) (hQ : G.quotient.Correct)
    {a : Fin 3741} {d : Compass}
    (ha : G.quotient.allowed a d = true)
    (hk : G.quotient.kind a d = .turn) :
    d ≠ G.quotient.arrival a ∧ d ≠ (G.quotient.arrival a).reverse := by
  let Q := G.quotient
  let w := Q.representative a
  have hrep := hQ.1 a
  have hstep := hQ.2 w hrep.1 d
  have hadm : WindowAdmissible w d := by
    apply hstep.1.mp
    change Q.allowed (Q.project w) d = true
    rw [hrep.2]
    exact ha
  have hkind : windowKind w d = .turn := by
    calc
      windowKind w d = Q.kind (Q.project w) d := (hstep.2 hadm).1.symm
      _ = .turn := by rw [hrep.2]; exact hk
  have harr : Q.arrival a = windowArrival w := by
    have hnonrev : windowKind w d ≠ .revisit := by rw [hkind]; decide
    calc
      Q.arrival a = Q.arrival (Q.project w) := by rw [hrep.2]
      _ = windowArrival w := (hstep.2 hadm).2.2 hnonrev
  have hd : d ≠ windowArrival w := by
    intro he
    subst d
    by_cases hr : 0 < departureCount (0, 0) w 10 (wordVertex (0, 0) w 10)
    · simp [windowKind, hr] at hkind
    · simp [windowKind, hr] at hkind
  refine ⟨?_, ?_⟩
  · intro he
    exact hd (he.trans harr)
  · intro he
    apply hadm.1
    exact he.trans (congrArg Compass.reverse harr)

private theorem directionCode_direction (n : Nat) (hn : n < 4) :
    directionCode (direction n) = n := by
  interval_cases n <;> simp [directionCode, direction] at *

private def storedEdgeTerm (G : Graph) (T : Tables) (p a d : Nat) : Nat :=
  if !G.allowed a d then 0 else
    let t := G.next a d
    let k := G.kind a d
    diagonal (phase p) (stepKind k) * T.cap (phaseKey p t) +
      if (p = 0 ∧ k = 1) ∨ (p = 1 ∧ k = 0) then
        response (G.arrival a) d 4 * T.cap (phaseKey (if k = 1 then 2 else 3) t)
      else 0

private theorem phaseSum (f : Phase → Nat) :
    (∑ ψ : Phase, f ψ) = f .A + f .B + f .C + f .D := by
  classical
  have hu : (Finset.univ : Finset Phase) = {.A, .B, .C, .D} := by decide
  change (Finset.univ.sum f) = _
  rw [hu]
  simp [add_assoc]

private theorem compassSum (f : Compass → Nat) :
    (∑ d : Compass, f d) = f .east + f .north + f .west + f .south := by
  classical
  have hu : (Finset.univ : Finset Compass) = {.east, .north, .west, .south} := by decide
  change Finset.univ.sum f = _
  rw [hu]
  simp [add_assoc]

@[simp] private theorem coefficientCeiling_zero : coefficientCeiling 0 = 0 := by
  norm_num [coefficientCeiling, certificateCoefficientScale]

private theorem freeEdgeIdentity (G : Graph) (T : Tables) (hQ : G.quotient.Correct)
    (φ : Phase) (a : Fin 3741) (d : Compass) :
    (∑ ψ : Phase, coefficientCeiling
      (freeCoefficient G.quotient φ a d ψ) * T.capFn ψ (G.quotient.successor a d)) =
      storedEdgeTerm G T (phaseCode φ) a.val (directionCode d) := by
  classical
  let code := directionCode d
  let rawKind := G.kind a.val code
  have hsucc : (G.quotient.successor a d).val = G.next a.val code := by
    simp [Graph.quotient, Graph.next, finState, code, Nat.mod_mod]
  cases φ
  all_goals
    by_cases hdest : G.dest a.val code = 0
    · have hdest' : G.dest a.val (directionCode d) = 0 := by simpa [code] using hdest
      rw [phaseSum]
      simp [storedEdgeTerm, freeCoefficient, Graph.quotient, Graph.allowed,
        code, hdest', phaseCode, phase, Tables.capFn, phaseKey, Graph.next,
        finState, stepKind]
    · have hnonzero' : G.dest a.val (directionCode d) ≠ 0 := by simpa [code] using hdest
      have hallowed : G.quotient.allowed a d = true := by
        simp [Graph.quotient, Graph.allowed, code, hnonzero']
      by_cases hk0 : rawKind = 0
      · have hkind : G.quotient.kind a d = .straight := by
          simp [Graph.quotient, stepKind, code, rawKind, hk0]
        have harrival := allowed_straight_arrival G hQ hallowed hkind
        have hdir : direction (G.arrival a.val) = d := by
          simpa [Graph.quotient] using harrival.symm
        have hdirCode : directionCode d = G.arrival a.val := by
          rw [← hdir]
          exact directionCode_direction _ (by
            simp [Graph.arrival]
            exact Nat.mod_lt _ (by decide))
        have hreward : relaxedReward (0, 0) (direction (G.arrival a.val)) d ∅ = straightReward := by
          rw [hdir]
          exact relaxedReward_straight d
        have hresponse : coefficientCeiling (passageFactor true * straightReward / 3) =
            response (G.arrival a.val) (directionCode d) 4 := by
          simpa [hdirCode] using straightResponseCeil d
        rw [phaseSum]
        simp [storedEdgeTerm, freeCoefficient, Graph.quotient, Graph.allowed,
          code, hnonzero', rawKind, hk0, phaseCode, phase, hsucc, diagonalCeil,
          hreward, hresponse, relaxedReward_straight, phaseTransition,
          Tables.capFn, phaseKey, Graph.next, finState, stepKind]
      · by_cases hk1 : rawKind = 1
        · have hkind : G.quotient.kind a d = .turn := by
            simp [Graph.quotient, stepKind, code, rawKind, hk0, hk1]
          have hturn := allowed_turn_facts G hQ hallowed hkind
          have hturn' : d ≠ direction (G.arrival a.val) ∧
              d ≠ (direction (G.arrival a.val)).reverse := by
            simpa [Graph.quotient] using hturn
          have hreward : relaxedReward (0, 0) (direction (G.arrival a.val)) d ∅ = turnReward :=
            relaxedReward_turn hturn'.1 hturn'.2
          have harrivalCode : directionCode (direction (G.arrival a.val)) = G.arrival a.val := by
            apply directionCode_direction
            simp [Graph.arrival]
            exact Nat.mod_lt _ (by decide)
          have hresponse : coefficientCeiling (passageFactor false * turnReward / 3) =
              response (G.arrival a.val) (directionCode d) 4 := by
            simpa [harrivalCode] using turnResponseCeil hturn'.1 hturn'.2
          rw [phaseSum]
          simp [storedEdgeTerm, freeCoefficient, Graph.quotient, Graph.allowed,
            code, hnonzero', rawKind, hk0, hk1, phaseCode, phase, hsucc, diagonalCeil,
            hreward, hresponse, phaseTransition,
            Tables.capFn, phaseKey, Graph.next, finState, stepKind]
        · rw [phaseSum]
          simp [storedEdgeTerm, freeCoefficient, Graph.quotient, Graph.allowed,
            code, hnonzero', rawKind, hk0, hk1, phaseCode, phase, hsucc, diagonalCeil,
            phaseTransition, Tables.capFn, phaseKey, Graph.next, finState, stepKind]

private theorem freeRow_as_sum (G : Graph) (T : Tables) (p a : Nat) :
    freeRow G T p a =
      ∑ d : Compass, storedEdgeTerm G T p a (directionCode d) := by
  classical
  rw [compassSum]
  simp [freeRow, dirs, storedEdgeTerm, directionCode]
  ac_rfl

theorem main : CertData.H3.Bridge.FreeRowLeaf := by
  intro G T hQ φ a
  calc
    freeRow G T (phaseCode φ) a.val =
        ∑ d : Compass, storedEdgeTerm G T (phaseCode φ) a.val (directionCode d) :=
      freeRow_as_sum G T (phaseCode φ) a.val
    _ = ∑ d : Compass, ∑ ψ : Phase,
        coefficientCeiling (freeCoefficient G.quotient φ a d ψ) *
          T.capFn ψ (G.quotient.successor a d) := by
      apply Finset.sum_congr rfl
      intro d hd
      symm
      exact freeEdgeIdentity G T hQ φ a d

#print axioms main

end AKLT.W.H3C027
