module
public import AKLT.W.H1C020.Chain
public import AKLT.W.H1C020.Inversion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
The uncontracted local tensor at one ring position.  It factors as a left
edge factor, a site factor (center edge and group slots), and a right edge
factor.  Contracting its single internal spin gives exactly `rationalLocal`.
-/

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C020

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- Internal spin coordinate. -/
def sv (x : Plane) (k : Fin 3) : LPoly := MvPolynomial.X (.inl (x,k))

/-- Edge color `c` at a spin: `1` for color zero, otherwise one coordinate. -/
def spinB (x : Plane) (c : Nat) : LPoly :=
  if c = 1 then sv x 0 else if c = 2 then sv x 1 else if c = 3 then sv x 2 else 1

def spinM (x : Plane) (cs : List Nat) : LPoly := (cs.map (spinB x)).prod

def spinExp (x : Plane) (cs : List Nat) : LocalVariable →₀ ℕ :=
  Finsupp.single (.inl (x,0)) (countColor 1 cs) + Finsupp.single (.inl (x,1)) (countColor 2 cs) +
    Finsupp.single (.inl (x,2)) (countColor 3 cs)

/-- Vector polynomials viewed among the local variables. -/
abbrev liftV : MvPolynomial (Fin 20 × Fin 3) ℚ →ₐ[ℚ] LPoly :=
  MvPolynomial.rename (Sum.inr : Fin 20 × Fin 3 → LocalVariable)

lemma spinExp_nil (x : Plane) : spinExp x [] = 0 := by
  simp [spinExp, countColor]

lemma spinExp_cons (x : Plane) (c : Nat) (cs : List Nat) :
    spinExp x (c :: cs) = spinExp x [c] + spinExp x cs := by
  simp only [spinExp, countColor, add_zero, Finsupp.single_add]
  abel

lemma spinB_eq (x : Plane) (c : Nat) :
    spinB x c = MvPolynomial.monomial (spinExp x [c]) 1 := by
  unfold spinB sv
  by_cases h1 : c = 1
  · subst c; simp [spinExp, countColor, MvPolynomial.X]
  · by_cases h2 : c = 2
    · subst c; simp [spinExp, countColor, MvPolynomial.X]
    · by_cases h3 : c = 3
      · subst c; simp [spinExp, countColor, MvPolynomial.X]
      · have e1 : (c == 1) = false := by simpa using h1
        have e2 : (c == 2) = false := by simpa using h2
        have e3 : (c == 3) = false := by simpa using h3
        simp [h1, h2, h3, spinExp, countColor, e1, e2, e3]

lemma spinM_eq (x : Plane) : ∀ cs : List Nat,
    spinM x cs = MvPolynomial.monomial (spinExp x cs) 1
  | [] => by simp [spinM, spinExp_nil]
  | c :: cs => by
      rw [spinM, List.map_cons, List.prod_cons, ← spinM, spinM_eq x cs, spinB_eq,
        MvPolynomial.monomial_mul_monomial, ← spinExp_cons, mul_one]

lemma spinM_nil (x : Plane) : spinM x [] = 1 := by simp [spinM]

lemma spinM_single (x : Plane) (c : Nat) : spinM x [c] = spinB x c := by simp [spinM]

lemma spinM_append (x : Plane) (a b : List Nat) : spinM x (a ++ b) = spinM x a * spinM x b := by
  simp [spinM, List.map_append, List.prod_append]

lemma spinExp_inr (x : Plane) (cs : List Nat) (j : Fin 20 × Fin 3) : spinExp x cs (.inr j) = 0 := by
  simp [spinExp, Finsupp.single_apply]

lemma spinExp_exponent (x : Plane) (cs : List Nat) :
    (fun k : Fin 3 => spinExp x cs (.inl (x,k))) =
      colorExponent (countColor 1 cs) (countColor 2 cs) (countColor 3 cs) := by
  funext k
  fin_cases k <;> simp [spinExp, Finsupp.single_apply, colorExponent]

lemma momentWeight_spinExp (x : Plane) (st : Plane → Status) (cs : List Nat) :
    momentWeight {x} st (spinExp x cs) = rationalStatusMoment (st x)
      (colorExponent (countColor 1 cs) (countColor 2 cs) (countColor 3 cs)) := by
  unfold momentWeight
  rw [Finset.prod_singleton, spinExp_exponent]

/-- Contraction of a single-site spin monomial times a vector polynomial. -/
lemma contract_spin_vec (x : Plane) (st : Plane → Status) (a : ℚ) (cs : List Nat)
    (q : MvPolynomial (Fin 20 × Fin 3) ℚ) :
    contractSpins {x} st (MvPolynomial.C a * spinM x cs * liftV q) =
      MvPolynomial.C (a * rationalStatusMoment (st x)
        (colorExponent (countColor 1 cs) (countColor 2 cs) (countColor 3 cs))) * q := by
  rw [spinM_eq, MvPolynomial.C_mul_monomial, mul_one,
    contractSpins_monomial_rename {x} st _ a (spinExp_inr x cs) q, momentWeight_spinExp]

lemma varsIn_sv {A : Finset Plane} {x : Plane} (hx : x ∈ A) (k : Fin 3) : VarsIn A (sv x k) :=
  varsIn_X_inl hx k

lemma varsIn_spinB {A : Finset Plane} {x : Plane} (hx : x ∈ A) (c : Nat) : VarsIn A (spinB x c) := by
  unfold spinB
  split_ifs
  · exact varsIn_sv hx 0
  · exact varsIn_sv hx 1
  · exact varsIn_sv hx 2
  · exact varsIn_one A

lemma varsIn_spinM {A : Finset Plane} {x : Plane} (hx : x ∈ A) (cs : List Nat) :
    VarsIn A (spinM x cs) := by
  apply varsIn_listProd
  intro p hp
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hp
  exact varsIn_spinB hx c

lemma varsIn_liftV (A : Finset Plane) (q : MvPolynomial (Fin 20 × Fin 3) ℚ) : VarsIn A (liftV q) :=
  varsIn_rename_inr A q

/-! ### The local factors -/

def edgeOne (k : Nat) : LPoly := if k = 0 then 1 else 0

def leafScalar (s : SiteSpec) (k : Nat) : ℚ :=
  if k == 0 then 1 else (if s.inverted then -1 else 1) / (if s.diluted then 3 else 2)

/-- The replaced leaf on its single bond, carrying its own vector token. -/
def leafVal (i : Nat) (s : SiteSpec) (k : Nat) : LPoly :=
  MvPolynomial.C (leafScalar s k) * liftV (if k == 0 then 1 else vectorVariable (ringLeader i) k)

def Lf (i : Nat) (s : SiteSpec) (l : Nat) : LPoly :=
  if s.left then (if s.leaf then leafVal i s l else spinB (ptOf i) l) else edgeOne l

def Rf (i : Nat) (s : SiteSpec) (r : Nat) : LPoly :=
  if s.right then (if s.leaf then (if s.left then 1 else leafVal i s r) else spinB (ptOf i) r)
  else edgeOne r

def Cf (i : Nat) (s : SiteSpec) (v : Nat) : LPoly :=
  if s.center then (if s.leaf then 1 else spinB (ptOf i) v) else edgeOne v

def tipScalar (s : SiteSpec) (cs : List Nat) : ℚ :=
  if s.tip then if cs.headD 0 == 0 then 1 else 3/5 else 1

def signScalar (s : SiteSpec) (cs : List Nat) : ℚ :=
  if s.inverted && (cs.filter (· != 0)).length % 2 == 1 then -1 else 1

/-- The group slots of a non-leaf site. -/
def Gf (i : Nat) (s : SiteSpec) : LPoly :=
  if s.leaf then 1 else
  ((colorChoices s.nslots).map fun cs =>
    MvPolynomial.C (tipScalar s cs * signScalar s cs) * spinM (ptOf i) cs *
      liftV (vectorMonomial (ringLeader i) cs)).sum

def Mf (i : Nat) (s : SiteSpec) (v : Nat) : LPoly := Cf i s v * Gf i s

/-- The uncontracted local tensor. -/
def gLoc (i : Nat) (s : SiteSpec) (l r v : Nat) : LPoly := Lf i s l * Mf i s v * Rf i s r

lemma leafVal_zero (i : Nat) (s : SiteSpec) : leafVal i s 0 = 1 := by
  simp [leafVal, leafScalar]

lemma varsIn_leafVal (A : Finset Plane) (i : Nat) (s : SiteSpec) (k : Nat) :
    VarsIn A (leafVal i s k) :=
  (varsIn_C A _).mul (varsIn_liftV A _)

lemma varsIn_edgeOne (A : Finset Plane) (k : Nat) : VarsIn A (edgeOne k) := by
  unfold edgeOne
  split
  · exact varsIn_one A
  · exact varsIn_zero A

lemma varsIn_gLoc (i : Nat) (s : SiteSpec) (l r v : Nat) : VarsIn {ptOf i} (gLoc i s l r v) := by
  have hx : ptOf i ∈ ({ptOf i} : Finset Plane) := Finset.mem_singleton_self _
  have hL : VarsIn {ptOf i} (Lf i s l) := by
    unfold Lf; split_ifs
    · exact varsIn_leafVal _ i s l
    · exact varsIn_spinB hx l
    · exact varsIn_edgeOne _ l
  have hR : VarsIn {ptOf i} (Rf i s r) := by
    unfold Rf; split_ifs
    · exact varsIn_one _
    · exact varsIn_leafVal _ i s r
    · exact varsIn_spinB hx r
    · exact varsIn_edgeOne _ r
  have hC : VarsIn {ptOf i} (Cf i s v) := by
    unfold Cf; split_ifs
    · exact varsIn_one _
    · exact varsIn_spinB hx v
    · exact varsIn_edgeOne _ v
  have hG : VarsIn {ptOf i} (Gf i s) := by
    unfold Gf; split_ifs
    · exact varsIn_one _
    · apply varsIn_listSum
      intro p hp
      obtain ⟨cs, _, rfl⟩ := List.mem_map.mp hp
      exact ((varsIn_C _ _).mul (varsIn_spinM hx cs)).mul (varsIn_liftV _ _)
  exact (hL.mul (hC.mul hG)).mul hR

/-- Contracting the single internal spin of the local tensor gives the
checker's rational local tensor. -/
theorem contract_gLoc (i : Nat) (s : SiteSpec) (l r v : Nat) (st : Plane → Status)
    (hst : ∀ m, rationalStatusMoment (st (ptOf i)) m =
      rationalStatusMoment (if s.diluted then .D else .U) m) :
    contractSpins {ptOf i} st (gLoc i s l r v) = rationalLocal i s l r v := by
  unfold rationalLocal
  by_cases hbad : ((!s.left && l != 0) || (!s.right && r != 0) || (!s.center && v != 0)) = true
  · rw [if_pos hbad]
    have hz : gLoc i s l r v = 0 := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hbad
      unfold gLoc Mf Lf Rf Cf edgeOne
      rcases hbad with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩ <;> simp [h1, h2]
    rw [hz, contractSpins_zero']
  · rw [if_neg hbad]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
      not_or, not_and, Decidable.not_not] at hbad
    obtain ⟨⟨hl, hr⟩, hv⟩ := hbad
    have hC1 : s.leaf = true → Cf i s v = 1 := by
      intro hleaf
      unfold Cf edgeOne
      cases hc : s.center <;> simp [hleaf, hv, hc]
    by_cases hleaf : s.leaf = true
    · rw [if_pos hleaf]
      have hG : Gf i s = 1 := by simp [Gf, hleaf]
      cases hL : s.left
      · have hl0 := hl hL
        have hg : gLoc i s l r v = leafVal i s r := by
          unfold gLoc Mf
          rw [hC1 hleaf, hG]
          unfold Lf Rf edgeOne
          cases hR : s.right
          · have hr0 := hr hR
            simp [hL, hR, hl0, hr0, leafVal_zero]
          · simp [hL, hR, hleaf, hl0]
        rw [hg]
        simp only [leafVal, contractSpins_C_mul, contractSpins_rename, hL, Bool.false_eq_true,
          ↓reduceIte, leafScalar]
      · have hg : gLoc i s l r v = leafVal i s l := by
          unfold gLoc Mf
          rw [hC1 hleaf, hG]
          unfold Lf Rf edgeOne
          cases hR : s.right
          · have hr0 := hr hR
            simp [hL, hR, hleaf, hr0]
          · simp [hL, hR, hleaf]
        rw [hg]
        simp only [leafVal, contractSpins_C_mul, contractSpins_rename, hL, ↓reduceIte, leafScalar]
    · have hleaf' : s.leaf = false := by simpa using hleaf
      rw [if_neg hleaf]
      have hLf : Lf i s l = spinM (ptOf i) (if s.left then [l] else []) := by
        unfold Lf edgeOne
        cases hL : s.left
        · simp [hl hL, spinM_nil]
        · simp [hleaf', spinM_single]
      have hRf : Rf i s r = spinM (ptOf i) (if s.right then [r] else []) := by
        unfold Rf edgeOne
        cases hR : s.right
        · simp [hr hR, spinM_nil]
        · simp [hleaf', spinM_single]
      have hCf : Cf i s v = spinM (ptOf i) (if s.center then [v] else []) := by
        unfold Cf edgeOne
        cases hc : s.center
        · simp [hv hc, spinM_nil]
        · simp [hleaf', spinM_single]
      have hg : gLoc i s l r v = ((colorChoices s.nslots).map fun cs =>
          MvPolynomial.C (tipScalar s cs * signScalar s cs) *
            spinM (ptOf i) (siteColors s l r v cs) *
              liftV (vectorMonomial (ringLeader i) cs)).sum := by
        have hK : gLoc i s l r v = (spinM (ptOf i) (if s.left then [l] else []) *
            spinM (ptOf i) (if s.right then [r] else []) *
            spinM (ptOf i) (if s.center then [v] else [])) *
            ((colorChoices s.nslots).map fun cs =>
              MvPolynomial.C (tipScalar s cs * signScalar s cs) * spinM (ptOf i) cs *
                liftV (vectorMonomial (ringLeader i) cs)).sum := by
          unfold gLoc Mf Gf
          rw [hLf, hRf, hCf, if_neg hleaf]
          ring
        rw [hK, ← List.sum_map_mul_left]
        apply congrArg List.sum
        apply List.map_congr_left
        intro cs _
        simp only [siteColors, spinM_append]
        ring
      rw [hg, contractSpins_listSum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro cs _
      simp only [Function.comp_apply]
      rw [contract_spin_vec, hst]
      congr 2
      simp only [tipScalar, signScalar]
      ring

end AKLT.W.H1C020
