import AKLT.W.REC043.Trace

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC043

@[simp] theorem word_vertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by simp [wordVertex]

@[simp] theorem word_vertex_cons {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) (j : ℕ) :
    wordVertex u (Fin.cons d w) (j + 1) = wordVertex (u + d.step) w j := by
  simp only [wordVertex, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Nat.zero_lt_succ, ite_true, Fin.val_succ, Nat.succ_lt_succ_iff]
  abel

@[simp] theorem word_bond_cons_zero {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) : wordBond u (Fin.cons d w) 0 = {u, u + d.step} := by
  simp [wordBond]

@[simp] theorem word_bond_cons_succ {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) (i : Fin n) :
    wordBond u (Fin.cons d w) i.succ = wordBond (u + d.step) w i := by
  simp [wordBond, Nat.add_assoc]

@[simp] theorem word_vertices_cons {n : ℕ} (u : Plane) (d : Compass)
    (w : DirectionWord n) :
    wordVertices u (Fin.cons d w) = u :: wordVertices (u + d.step) w := by
  unfold wordVertices
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, word_vertex_zero]
  congr 1
  apply List.map_congr_left
  intro j hj
  exact word_vertex_cons u d w j

/-- Prepending a choice splits a stopped trail exactly at its first consumed bond. -/
theorem stopped_cons_iff {G : Finset Plane} {D : Network G} {u : Plane}
    (hu : D.AdmissibleStart u) {T : Finset Plane} (ht : u ∉ T)
    {n : ℕ} (d : Compass) (w : DirectionWord n) :
    StoppedNetworkTrail D u T (Fin.cons d w) ↔
      D.Present u (u + d.step) ∧
        StoppedNetworkTrail (traceStep D u (u + d.step)) (u + d.step) T w := by
  constructor
  · rintro ⟨hi, hp, hstop, hlast⟩
    have hp0 : D.Present u (u + d.step) := by simpa using hp 0
    refine ⟨hp0, ?_, ?_, ?_, ?_⟩
    · intro i j he
      have he' : wordBond u (Fin.cons d w) i.succ =
          wordBond u (Fin.cons d w) j.succ := by simpa using he
      exact Fin.succ_injective _ (hi he')
    · intro i
      apply (traceStep_present_iff hu hp0 _ _).mpr
      refine ⟨by simpa using hp i.succ, ?_⟩
      intro he
      have he' : wordBond u (Fin.cons d w) i.succ =
          wordBond u (Fin.cons d w) 0 := by simpa [wordBond] using he
      have h := congrArg Fin.val (hi he')
      simp only [Fin.val_succ, Fin.val_zero] at h
      omega
    · intro j hj
      simpa using hstop (j + 1) (by omega)
    · simpa using hlast
  · rintro ⟨hp0, hi, hp, hstop, hlast⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro he; rfl
        · intro he
          have hne := ((traceStep_present_iff hu hp0 _ _).mp (hp j')).2
          exact (hne (by simpa [wordBond] using he.symm)).elim
      · refine Fin.cases ?_ (fun j' => ?_) j
        · intro he
          have hne := ((traceStep_present_iff hu hp0 _ _).mp (hp i')).2
          exact (hne (by simpa [wordBond] using he)).elim
        · intro he
          have htail : wordBond (u + d.step) w i' = wordBond (u + d.step) w j' := by
            simpa using he
          exact congrArg Fin.succ (hi htail)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp0
      · simpa using traceStep_present_subset D u (u + d.step) (hp j)
    · intro j hj
      cases j with
      | zero => simpa using And.intro ht hu.2.1
      | succ j => simpa using hstop j (by omega)
    · simpa using hlast

private def wordConsEquiv (n : ℕ) : Compass × DirectionWord n ≃ DirectionWord (n + 1) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, Fin.tail w)
  left_inv p := by simp
  right_inv w := Fin.cons_self_tail w

/-- Splitting the finite word enumeration into its first compass choice and tail. -/
theorem sum_word_cons {n : ℕ} (f : DirectionWord (n + 1) → ℝ) :
    (∑ w, f w) = ∑ d : Compass, ∑ w : DirectionWord n, f (Fin.cons d w) := by
  calc
    _ = ∑ p : Compass × DirectionWord n, f (Fin.cons p.1 p.2) :=
      (Equiv.sum_comp (wordConsEquiv n) f).symm
    _ = _ := Fintype.sum_prod_type _

end AKLT.W.REC043
