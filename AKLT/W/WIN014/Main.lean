import AKLT.Blueprint.Win.NodesTopology

noncomputable section
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN014

private def degree (c : EdgeChain) (x : Plane) : ZMod 2 :=
  c.sum (fun e a => if x ∈ e then a else 0)

private theorem degree_add (c d : EdgeChain) (x : Plane) :
    degree (c + d) x = degree c x + degree d x := by
  simpa [degree] using (Finsupp.sum_add_index'
    (f := c) (g := d)
    (h_zero := fun e => by split <;> simp)
    (h_add := fun e a b => by by_cases hx : x ∈ e <;> simp [hx]))

private theorem degree_zero (x : Plane) : degree (0 : EdgeChain) x = 0 := by
  simp [degree]

private theorem degree_edge (x y z : Plane) :
    degree (edge x y) z = (if z = x ∨ z = y then 1 else 0) := by
  simp [degree, edge, Finsupp.sum, Sym2.mem_iff]

private theorem one_add_one_zero : (1 : ZMod 2) + 1 = 0 := by
  calc
    (1 : ZMod 2) + 1 = 2 := by ring
    _ = 0 := ZMod.natCast_self 2

private theorem degree_triangle {x y z w : Plane} (hxy : x ≠ y) (hyz : y ≠ z)
    (hzx : z ≠ x) : degree (triangle x y z) w = 0 := by
  simp only [triangle, degree_add, degree_edge]
  by_cases hwx : w = x
  · subst w
    simp [hxy, hxy.symm, hyz, hyz.symm, hzx, hzx.symm, one_add_one_zero]
  · by_cases hwy : w = y
    · subst w
      simp [hxy, hxy.symm, hyz, hyz.symm, hzx, hzx.symm, one_add_one_zero]
    · by_cases hwz : w = z
      · subst w
        simp [hxy, hxy.symm, hyz, hyz.symm, hzx, hzx.symm, one_add_one_zero]
      · simp [hwx, hwy, hwz]

private theorem degree_finset_sum {α : Type*} (s : Finset α) (f : α → EdgeChain) (x : Plane) :
    degree (∑ a ∈ s, f a) x = ∑ a ∈ s, degree (f a) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degree]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, degree_add, ih]

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  unfold Adjacent latticeDist at *
  have h₁ : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by
    calc
      (y.1 - x.1).natAbs = (-(x.1 - y.1)).natAbs := by congr 1 <;> omega
      _ = (x.1 - y.1).natAbs := Int.natAbs_neg _
  have h₂ : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by
    calc
      (y.2 - x.2).natAbs = (-(x.2 - y.2)).natAbs := by congr 1 <;> omega
      _ = (x.2 - y.2).natAbs := Int.natAbs_neg _
  omega

private theorem star_symm {x y : Plane} (h : StarAdjacent x y) : StarAdjacent y x := by
  unfold StarAdjacent supDist at *
  have h₁ : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by
    calc
      (y.1 - x.1).natAbs = (-(x.1 - y.1)).natAbs := by congr 1 <;> omega
      _ = (x.1 - y.1).natAbs := Int.natAbs_neg _
  have h₂ : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by
    calc
      (y.2 - x.2).natAbs = (-(x.2 - y.2)).natAbs := by congr 1 <;> omega
      _ = (x.2 - y.2).natAbs := Int.natAbs_neg _
  simpa [h₁, h₂, max_comm] using h

private theorem star_of_adjacent {x y : Plane} (h : Adjacent x y) : StarAdjacent x y := by
  unfold Adjacent StarAdjacent latticeDist supDist at *
  have h₁ : (x.1 - y.1).natAbs ≤ 1 := by omega
  have h₂ : (x.2 - y.2).natAbs ≤ 1 := by omega
  have hmax : max (x.1 - y.1).natAbs (x.2 - y.2).natAbs = 1 := by
    apply le_antisymm
    · exact max_le h₁ h₂
    · by_cases ha : (x.1 - y.1).natAbs = 1
      · simp [ha]
      · have ha0 : (x.1 - y.1).natAbs = 0 := by omega
        have hb : (x.2 - y.2).natAbs = 1 := by omega
        simp [ha0, hb]
  exact hmax

private theorem diagonal_middle {x y : Plane} (h : StarAdjacent x y) (hn : ¬ Adjacent x y) :
    Adjacent x (x.1, y.2) ∧ Adjacent (x.1, y.2) y := by
  have hmax : max (x.1 - y.1).natAbs (x.2 - y.2).natAbs = 1 := by
    simpa [StarAdjacent, supDist] using h
  have hxle : (x.1 - y.1).natAbs ≤ 1 := by
    calc
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := Nat.le_max_left _ _
      _ = 1 := hmax
  have hyle : (x.2 - y.2).natAbs ≤ 1 := by
    calc
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := Nat.le_max_right _ _
      _ = 1 := hmax
  have hxne : (x.1 - y.1).natAbs ≠ 0 := by
    intro hx0
    have hy1 : (x.2 - y.2).natAbs = 1 := by simpa [hx0] using hmax
    apply hn
    unfold Adjacent latticeDist
    omega
  have hyne : (x.2 - y.2).natAbs ≠ 0 := by
    intro hy0
    have hx1 : (x.1 - y.1).natAbs = 1 := by simpa [hy0, max_comm] using hmax
    apply hn
    unfold Adjacent latticeDist
    omega
  have hx1 : (x.1 - y.1).natAbs = 1 := by omega
  have hy1 : (x.2 - y.2).natAbs = 1 := by omega
  constructor
  · unfold Adjacent latticeDist
    simp [hx1, hy1]
  · unfold Adjacent latticeDist
    simp [hx1, hy1]

private def diagonalSupport (c : EdgeChain) : Finset LatticeEdge :=
  c.support.filter fun e => ¬ Adjacent e.out.1 e.out.2

private def diagonalTriangle (e : LatticeEdge) : EdgeChain :=
  triangle e.out.1 (e.out.1.1, e.out.2.2) e.out.2

private theorem edge_eval (x y : Plane) (e : LatticeEdge) :
    edge x y e = if e = s(x, y) then 1 else 0 := by
  simp [edge, Finsupp.single_apply, eq_comm]

private theorem edge_eval_zero_of_adjacent {x y : Plane} (hxy : Adjacent x y)
    (e : LatticeEdge) (he : ¬ Adjacent e.out.1 e.out.2) : edge x y e = 0 := by
  rw [edge_eval]
  by_cases heq : e = s(x, y)
  · have hout : s(e.out.1, e.out.2) = e := by
      simpa only [Sym2.mk] using e.out_eq
    have hrep : s(e.out.1, e.out.2) = s(x, y) := hout.trans heq
    have hpairs := (Sym2.mk_eq_mk_iff (p := (e.out.1, e.out.2)) (q := (x, y))).mp hrep
    rcases hpairs with hp | hp
    · have hp' : e.out.1 = x ∧ e.out.2 = y := Prod.mk.inj hp
      exact (he (by simpa [hp'.1, hp'.2] using hxy)).elim
    · have hp' : e.out.1 = y ∧ e.out.2 = x := by
        change (e.out.1, e.out.2) = (y, x) at hp
        exact Prod.mk.inj hp
      exact (he (by simpa [hp'.1, hp'.2] using adjacent_symm hxy)).elim
  · simp [heq]

private theorem triangle_eval_diagonal {x m y : Plane} (hxm : Adjacent x m)
    (hmy : Adjacent m y) (e : LatticeEdge) (he : ¬ Adjacent e.out.1 e.out.2) :
    triangle x m y e = if e = s(x, y) then 1 else 0 := by
  unfold triangle
  rw [Finsupp.add_apply, Finsupp.add_apply]
  rw [edge_eval_zero_of_adjacent hxm e he, edge_eval_zero_of_adjacent hmy e he]
  simp [edge_eval, Sym2.eq_swap, eq_comm]

private theorem star_ne {x y : Plane} (h : StarAdjacent x y) : x ≠ y := by
  intro hxy
  subst y
  simp [StarAdjacent, supDist] at h

private theorem chainStar_out {c : EdgeChain} (hc : ChainStar c) {e : LatticeEdge}
    (he : e ∈ c.support) : StarAdjacent e.out.1 e.out.2 := by
  obtain ⟨x, y, hEq, hxy⟩ := hc e he
  have hout : s(e.out.1, e.out.2) = e := by
    simpa only [Sym2.mk] using e.out_eq
  have hrep : s(e.out.1, e.out.2) = s(x, y) := hout.trans hEq
  have hpairs := (Sym2.mk_eq_mk_iff (p := (e.out.1, e.out.2)) (q := (x, y))).mp hrep
  rcases hpairs with hp | hp
  · have hp' : e.out.1 = x ∧ e.out.2 = y := Prod.mk.inj hp
    simpa [hp'.1, hp'.2] using hxy
  · have hp' : e.out.1 = y ∧ e.out.2 = x := by
      change (e.out.1, e.out.2) = (y, x) at hp
      exact Prod.mk.inj hp
    simpa [hp'.1, hp'.2] using star_symm hxy

private theorem triangle_even {x y z : Plane} (h : IsTriangle x y z) (w : Plane) :
    degree (triangle x y z) w = 0 := by
  apply degree_triangle
  · exact star_ne h.1
  · exact star_ne h.2.1
  · exact star_ne h.2.2

private theorem diagonalTriangle_isTriangle {c : EdgeChain} (hc : ChainStar c)
    {e : LatticeEdge} (he : e ∈ diagonalSupport c) :
    IsTriangle e.out.1 (e.out.1.1, e.out.2.2) e.out.2 := by
  have hs := Finset.mem_filter.mp he
  have hstar := chainStar_out hc hs.1
  have hm := diagonal_middle hstar hs.2
  exact ⟨star_of_adjacent hm.1, ⟨star_of_adjacent hm.2, star_symm hstar⟩⟩

private theorem diagonalTriangle_even {c : EdgeChain} (hc : ChainStar c)
    {e : LatticeEdge} (he : e ∈ diagonalSupport c) (w : Plane) :
    degree (diagonalTriangle e) w = 0 := by
  exact triangle_even (diagonalTriangle_isTriangle hc he) w

private theorem diagonalTriangle_span {c : EdgeChain} (hc : ChainStar c)
    {e : LatticeEdge} (he : e ∈ diagonalSupport c) : diagonalTriangle e ∈ triangleSpan := by
  have ht := diagonalTriangle_isTriangle hc he
  exact Submodule.subset_span ⟨e.out.1, (e.out.1.1, e.out.2.2), e.out.2, ht, rfl⟩

private theorem diagonalTriangle_eval {c : EdgeChain} (hc : ChainStar c)
    {f : LatticeEdge} (hf : f ∈ diagonalSupport c) (e : LatticeEdge)
    (he : ¬ Adjacent e.out.1 e.out.2) :
    diagonalTriangle f e = if e = f then 1 else 0 := by
  have hs := Finset.mem_filter.mp hf
  have hm := diagonal_middle (chainStar_out hc hs.1) hs.2
  have hEval := triangle_eval_diagonal hm.1 hm.2 e he
  simpa [diagonalTriangle, f.out_eq] using hEval

private theorem sum_indicator_eq {α : Type*} [DecidableEq α] (s : Finset α) (e : α) :
    (∑ f ∈ s, if e = f then (1 : ZMod 2) else 0) = if e ∈ s then 1 else 0 := by
  classical
  by_cases he : e ∈ s
  · calc
      (∑ f ∈ s, if e = f then (1 : ZMod 2) else 0) = (if e = e then 1 else 0) :=
        Finset.sum_eq_single e (by
          intro f hf hfe
          simp [hfe.symm]) (by
          intro h
          exact (h he).elim)
      _ = if e ∈ s then 1 else 0 := by simp [he]
  · rw [Finset.sum_eq_zero]
    · simp [he]
    · intro f hf
      have hne : e ≠ f := by
        intro h
        exact he (h ▸ hf)
      simp [hne]

private theorem zmod_two_ne_zero_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

private theorem zmod_two_neg_self (a : ZMod 2) : -a = a := by
  fin_cases a
  · rfl
  · exact neg_eq_iff_add_eq_zero.mpr one_add_one_zero

private theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a
  · rfl
  · exact one_add_one_zero

private theorem zmod_two_sub_add (a b : ZMod 2) : a - (a + b) = b := by
  calc
    a - (a + b) = a + -(a + b) := sub_eq_add_neg _ _
    _ = a + (-a + -b) := congrArg (fun t : ZMod 2 => a + t) (neg_add a b)
    _ = a + (a + b) := by simp [zmod_two_neg_self]
    _ = (a + a) + b := by rw [← add_assoc]
    _ = b := by rw [zmod_two_add_self, zero_add]

theorem main : AKLT.Blueprint.Win.DiagonalEliminationStatement := by
  classical
  intro c hc hs
  let D : Finset LatticeEdge := diagonalSupport c
  let q : EdgeChain := ∑ e ∈ D, diagonalTriangle e
  let d : EdgeChain := c + q
  have hqspan : q ∈ triangleSpan := by
    change (∑ e ∈ D, diagonalTriangle e) ∈ triangleSpan
    apply Submodule.sum_mem
    intro e he
    exact diagonalTriangle_span hc (by simpa [D] using he)
  have hqdegree (x : Plane) : degree q x = 0 := by
    change degree (∑ e ∈ D, diagonalTriangle e) x = 0
    rw [degree_finset_sum]
    apply Finset.sum_eq_zero
    intro e he
    exact diagonalTriangle_even hc (by simpa [D] using he) x
  have hqeval {e : LatticeEdge} (he : ¬ Adjacent e.out.1 e.out.2) :
      q e = if e ∈ D then 1 else 0 := by
    calc
      q e = ∑ f ∈ D, diagonalTriangle f e := by simp [q, Finset.sum_apply]
      _ = ∑ f ∈ D, if e = f then (1 : ZMod 2) else 0 := by
        apply Finset.sum_congr rfl
        intro f hf
        exact diagonalTriangle_eval hc (by simpa [D] using hf) e he
      _ = if e ∈ D then 1 else 0 := sum_indicator_eq D e
  have hdNN : ChainNN d := by
    intro e he
    have hadj : Adjacent e.out.1 e.out.2 := by
      by_contra hnot
      have hdne : d e ≠ 0 := Finsupp.mem_support_iff.mp he
      by_cases hcmem : e ∈ c.support
      · have heD : e ∈ D := by simpa [D, diagonalSupport, hcmem, hnot]
        have hcval : c e = 1 := zmod_two_ne_zero_eq_one (Finsupp.mem_support_iff.mp hcmem)
        have hqval : q e = 1 := by simpa [heD] using hqeval hnot
        have hdval : d e = 0 := by
          change c e + q e = 0
          rw [hcval, hqval]
          exact one_add_one_zero
        exact hdne hdval
      · have hcval : c e = 0 := Finsupp.notMem_support_iff.mp hcmem
        have heD : e ∉ D := by
          intro hD
          change e ∈ diagonalSupport c at hD
          have : e ∈ c.support := (Finset.mem_filter.mp hD).1
          exact hcmem this
        have hdval : d e = 0 := by
          change c e + q e = 0
          rw [hcval, hqeval hnot]
          simp [heD]
        exact hdne hdval
    exact ⟨e.out.1, e.out.2, e.out_eq.symm, hadj⟩
  have hcdegree (x : Plane) : degree c x = 0 := by
    simpa [degree, Finsupp.sum] using hs x
  have hddegree (x : Plane) : degree d x = 0 := by
    change degree (c + q) x = 0
    rw [degree_add, hcdegree x, hqdegree x]
    simp
  have hdEven : ChainEven d := by
    intro x
    simpa [degree, Finsupp.sum] using hddegree x
  have hcd : c - d = q := by
    ext e
    change c e - (c e + q e) = q e
    exact zmod_two_sub_add _ _
  exact ⟨d, hdNN, hdEven, hcd ▸ hqspan⟩

end AKLT.W.WIN014
