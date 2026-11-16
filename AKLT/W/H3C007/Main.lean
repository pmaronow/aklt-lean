import CertData.H3.Bridge.Interface
import AKLT.Cert.H2.Trails

open AKLT.Defs
open AKLT.Cert.H3
open AKLT.Cert.H3.Production
open CertData.H3.Bridge

namespace AKLT.W.H3C007

private theorem productionBond_comm (x y : Plane) :
    AKLT.Cert.H3.Production.bond x y = AKLT.Cert.H3.Production.bond y x := by
  classical
  unfold AKLT.Cert.H3.Production.bond
  by_cases hxy : x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
  · by_cases hyx : y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2)
    · have h : x = y := by
        apply Prod.ext
        · rcases hxy with hxy | ⟨hxy, _⟩ <;>
            rcases hyx with hyx | ⟨hyx, _⟩ <;> omega
        · rcases hxy with hxy | ⟨_, hxy⟩ <;>
            rcases hyx with hyx | ⟨_, hyx⟩ <;> omega
      subst y
      rfl
    · simp [hxy, hyx]
  · by_cases hyx : y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2)
    · simp [hxy, hyx]
    · have htotal : (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) ∨
          (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2)) := by
        by_cases h₁ : x.1 < y.1
        · exact Or.inl (Or.inl h₁)
        · by_cases h₂ : y.1 < x.1
          · exact Or.inr (Or.inl h₂)
          · have h₃ : x.1 = y.1 := by omega
            by_cases h₄ : x.2 ≤ y.2
            · exact Or.inl (Or.inr ⟨h₃, h₄⟩)
            · have h₅ : y.2 ≤ x.2 := by omega
              exact Or.inr (Or.inr ⟨h₃.symm, h₅⟩)
      exact False.elim (htotal.elim hxy hyx)

private theorem productionBond_set (x y : Plane) :
    ({(AKLT.Cert.H3.Production.bond x y).1,
       (AKLT.Cert.H3.Production.bond x y).2} : Finset Plane) = {x, y} := by
  unfold AKLT.Cert.H3.Production.bond
  split_ifs <;> simp [Finset.pair_comm]

private theorem productionBond_eq_iff_set_eq (x y z t : Plane)
    (hxy : x ≠ y) :
    AKLT.Cert.H3.Production.bond x y = AKLT.Cert.H3.Production.bond z t ↔
      ({x, y} : Finset Plane) = {z, t} := by
  classical
  constructor
  · intro h
    have h' := congrArg (fun p : Plane × Plane => ({p.1, p.2} : Finset Plane)) h
    rw [productionBond_set, productionBond_set] at h'
    exact h'
  · intro h
    have hx : x ∈ ({z, t} : Finset Plane) := by rw [← h]; simp
    have hy : y ∈ ({z, t} : Finset Plane) := by rw [← h]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exfalso
      exact hxy (hx.trans hy.symm)
    · subst z
      subst t
      rfl
    · subst t
      subst z
      exact productionBond_comm x y
    · exfalso
      exact hxy (hx.trans hy.symm)

private theorem advance_direction (p : Plane) (d : Compass) :
    AKLT.Cert.H3.Production.advance p (directionCode d) = p + d.step := by
  cases d <;> rfl

private theorem directionCode_direction (d : Fin 4) :
    directionCode (direction d.val) = d.val := by
  fin_cases d <;> rfl

private theorem vertex_succ_local {n : Nat} (w : DirectionWord n) (i : Fin n) :
    wordVertex (0, 0) w (i.val + 1) =
      wordVertex (0, 0) w i.val + (w i).step := by
  simpa using AKLT.Cert.H2.vertex_succ (0, 0) w i.val i.isLt

private theorem edge_endpoints_ne {n : Nat} (w : DirectionWord n) (i : Fin n) :
    wordVertex (0, 0) w i.val ≠ wordVertex (0, 0) w (i.val + 1) := by
  rw [vertex_succ_local]
  intro h
  have hv : (0 : Plane) = (w i).step := by
    have h' := congrArg (fun z : Plane => z - wordVertex (0, 0) w i.val) h
    simpa using h'
  have hstep : (w i).step ≠ (0 : Plane) := by
    cases w i <;> decide
  exact hstep hv.symm

private theorem legal_iff_no_old_bond (w : DirectionWord 10) (s : Walk)
    (hrep : WalkRepresents (0, 0) 0 w s) (d : Compass) :
    s.legal (directionCode d) = true ↔
      ∀ i : Fin 10,
        wordBond (0, 0) w i ≠
          {wordVertex (0, 0) w 10, wordVertex (0, 0) w 10 + d.step} := by
  rcases hrep with ⟨hdepth, hpos, hin, hcode, hdeparted, hused⟩
  have hcollision :
      s.used.contains (AKLT.Cert.H3.Production.bond
        (wordVertex (0, 0) w 10)
        (AKLT.Cert.H3.Production.advance (wordVertex (0, 0) w 10) (directionCode d))) = true ↔
      ∃ i : Fin 10, wordBond (0, 0) w i =
        {wordVertex (0, 0) w 10, wordVertex (0, 0) w 10 + d.step} := by
    rw [hused]
    simp only [List.contains_iff_mem, List.mem_reverse, List.mem_map, List.mem_finRange]
    constructor
    · rintro ⟨i, ⟨_, hi⟩⟩
      refine ⟨i, ?_⟩
      have hset := (productionBond_eq_iff_set_eq _ _ _ _ (edge_endpoints_ne w i)).1 hi
      simpa [advance_direction, vertex_succ_local, wordBond] using hset
    · rintro ⟨i, hi⟩
      refine ⟨i, ⟨trivial, ?_⟩⟩
      have hset : ({wordVertex (0, 0) w i.val,
          wordVertex (0, 0) w (i.val + 1)} : Finset Plane) =
          {wordVertex (0, 0) w 10,
            wordVertex (0, 0) w 10 + d.step} := by
        simpa [wordBond] using hi
      have hb := (productionBond_eq_iff_set_eq _ _ _ _ (edge_endpoints_ne w i)).2 hset
      simpa [advance_direction, vertex_succ_local] using hb
  unfold Walk.legal
  rw [hpos]
  constructor
  · intro hlegal i hi
    have hc := hcollision.mpr ⟨i, hi⟩
    rw [hc] at hlegal
    simp at hlegal
  · intro hfresh
    have hfalse : s.used.contains (AKLT.Cert.H3.Production.bond
        (wordVertex (0, 0) w 10)
        (AKLT.Cert.H3.Production.advance (wordVertex (0, 0) w 10) (directionCode d))) = false := by
      cases hc : s.used.contains (AKLT.Cert.H3.Production.bond
          (wordVertex (0, 0) w 10)
          (AKLT.Cert.H3.Production.advance (wordVertex (0, 0) w 10) (directionCode d))) with
      | false => rfl
      | true =>
        obtain ⟨i, hi⟩ := hcollision.mp hc
        exact False.elim (hfresh i hi)
    rw [hfalse]
    rfl

private theorem reverse_code (c : Compass) :
    rev (directionCode c) = directionCode c.reverse := by
  cases c <;> rfl

private theorem reversal_boolean_iff (d : Fin 4) (c : Compass) :
    (d.val != rev (directionCode c)) = true ↔ direction d.val ≠ c.reverse := by
  fin_cases d <;> cases c <;> norm_num [rev, direction, directionCode, Compass.reverse]

theorem main : CertData.H3.Bridge.LegalDirectionLeaf := by
  intro w s hraw hrep d
  rcases hrep with ⟨hdepth, hpos, hin, hcode, hdeparted, hused⟩
  have hin' : s.incoming = directionCode (windowArrival w) := by simpa using hin
  have hlegal := legal_iff_no_old_bond w s
    ⟨hdepth, hpos, hin', hcode, hdeparted, hused⟩ (direction d.val)
  rw [directionCode_direction] at hlegal
  have hreverse : (d.val != rev s.incoming) = true ↔
      direction d.val ≠ (windowArrival w).reverse := by
    rw [hin']
    exact reversal_boolean_iff d (windowArrival w)
  change ((d.val != rev s.incoming) && s.legal d.val) = true ↔
    (direction d.val ≠ (windowArrival w).reverse ∧
      ∀ i : Fin 10,
        wordBond (0, 0) w i ≠
          {wordVertex (0, 0) w 10,
            wordVertex (0, 0) w 10 + (direction d.val).step})
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hrev, hfresh⟩
    exact ⟨hreverse.mp hrev, (hlegal.mp hfresh)⟩
  · rintro ⟨hrev, hfresh⟩
    exact ⟨hreverse.mpr hrev, (hlegal.mpr hfresh)⟩

end AKLT.W.H3C007

#print axioms AKLT.W.H3C007.main
