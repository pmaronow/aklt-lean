import AKLT.W.REC004.FibreExpansion
import AKLT.W.REC002.Bonds

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC004

open AKLT.W.REC002 (spinSum extend bondProduct legProduct spinSum_insert bondProduct_remove
  partition_spinSum mem_presentNeighbours mem_remove_active)

/-- One-site integration, written again as a spin sum over the smaller volume. -/
lemma spinSum_insert' (V : Finset Plane) (y : Plane) (hy : y ∉ V)
    (s : Plane → Status) (F : (Plane → Vec3) → ℝ) :
    spinSum (insert y V) s F =
      spinSum V s (fun m => siteFunctional (s y) (fun v => F (Function.update m y v))) :=
  spinSum_insert V y hy s F

/-- The letter of a configuration, with the zero letter off its volume. -/
def letterOf (V : Finset Plane) (n : V → SpinLetter) (x : Plane) : SpinLetter :=
  if h : x ∈ V then n ⟨x, h⟩ else none

lemma extend_eq_letter (V : Finset Plane) (n : V → SpinLetter) (x : Plane) :
    extend V n x = spinVector (letterOf V n x) := by
  unfold extend letterOf
  split_ifs <;> rfl

/-- At most `k` incident factors can be listed as exactly `k` letters,
padding with the zero letter. -/
lemma pad_fields (φ : Plane → SpinLetter) :
    ∀ (k : ℕ) (S : Finset Plane), S.card ≤ k →
      ∃ a : Fin k → SpinLetter, ∀ h : SpinLetter → ℝ, h none = 1 →
        ∏ z ∈ S, h (φ z) = ∏ i, h (a i) := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨Fin.elim0, fun h _ => ?_⟩
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    simp [hS0]
  | succ k ih =>
    intro S hS
    by_cases hne : S.Nonempty
    · obtain ⟨z, hz⟩ := hne
      obtain ⟨a, ha⟩ := ih (S.erase z) (by rw [Finset.card_erase_of_mem hz]; omega)
      refine ⟨Fin.cons (φ z) a, fun h h0 => ?_⟩
      rw [Fin.prod_univ_succ, ← Finset.mul_prod_erase S _ hz, ha h h0]
      simp
    · refine ⟨fun _ => none, fun h h0 => ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp [h0]

lemma legProduct_update {G : Finset Plane} (V : Finset Plane) (τ : PinAssignment G)
    (b : Bool) (x : Plane) (hx : ∀ e : originalLegs G, e.val.1 ≠ x)
    (m : Plane → Vec3) (v : Vec3) :
    legProduct V τ b (Function.update m x v) = legProduct V τ b m := by
  unfold legProduct
  apply Finset.prod_congr rfl
  intro e _
  rw [Function.update_of_ne (hx e)]

/-- Remove three mutually nonadjacent sites from the bond product. -/
lemma bond_split3 {G : Finset Plane} (D : Network G) (f g o : Plane)
    (hgf : ∀ z ∈ (removeSite D o).presentNeighbours g, z ≠ f)
    (hof : ∀ z ∈ D.presentNeighbours o, z ≠ f)
    (hog : ∀ z ∈ D.presentNeighbours o, z ≠ g)
    (m : Plane → Vec3) (v1 v2 v3 : Vec3) :
    bondProduct D.bonds
        (Function.update (Function.update (Function.update m f v1) g v2) o v3) =
      bondProduct (removeSite (removeSite (removeSite D o) g) f).bonds m *
        (∏ z ∈ (removeSite (removeSite D o) g).presentNeighbours f, (1 + dot v1 (m z))) *
        (∏ z ∈ (removeSite D o).presentNeighbours g, (1 + dot v2 (m z))) *
        (∏ z ∈ D.presentNeighbours o, (1 + dot v3 (m z))) := by
  rw [bondProduct_remove D o, bondProduct_remove (removeSite D o) g,
    bondProduct_remove (removeSite (removeSite D o) g) f]
  have h2 : (∏ z ∈ (removeSite D o).presentNeighbours g,
      (1 + dot v2 (Function.update m f v1 z))) =
      ∏ z ∈ (removeSite D o).presentNeighbours g, (1 + dot v2 (m z)) := by
    apply Finset.prod_congr rfl
    intro z hz
    rw [Function.update_of_ne (hgf z hz)]
  have h3 : (∏ z ∈ D.presentNeighbours o,
      (1 + dot v3 (Function.update (Function.update m f v1) g v2 z))) =
      ∏ z ∈ D.presentNeighbours o, (1 + dot v3 (m z)) := by
    apply Finset.prod_congr rfl
    intro z hz
    rw [Function.update_of_ne (hog z hz), Function.update_of_ne (hof z hz)]
  rw [h2, h3]

lemma remove_presentNeighbours_subset {G : Finset Plane} (D : Network G) (x z : Plane) :
    (removeSite D x).presentNeighbours z ⊆ D.presentNeighbours z := by
  intro w hw
  rw [mem_presentNeighbours] at hw ⊢
  exact ⟨((mem_remove_active D x z).1 hw.1).1, ((mem_remove_active D x w).1 hw.2.1).1,
    hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩

lemma adjacent_of_mem_pN {G : Finset Plane} {D : Network G} {x z : Plane}
    (h : z ∈ D.presentNeighbours x) : Adjacent x z := (Finset.mem_filter.1 h).2.2.2.1

lemma extend_ball (V : Finset Plane) (n : V → SpinLetter) (x : Plane) :
    normSq (extend V n x) ≤ 1 := by
  rw [extend_eq_letter]
  exact spin_ball _

lemma bondProduct_extend_nonneg (B : Finset (Plane × Plane)) (V : Finset Plane)
    (n : V → SpinLetter) : 0 ≤ bondProduct B (extend V n) := by
  unfold bondProduct
  exact Finset.prod_nonneg fun e _ => one_add_dot_nonneg (extend_ball V n _) (extend_ball V n _)

lemma legProduct_extend_nonneg {G : Finset Plane} (A V : Finset Plane) (τ : PinAssignment G)
    (b : Bool) (n : V → SpinLetter) : 0 ≤ legProduct A τ b (extend V n) := by
  unfold legProduct
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact one_add_dot_nonneg (le_of_eq (τ e).property) (extend_ball V n _)
  · norm_num

/-- The algebra of one outside configuration: three nested site integrals of a
product integrand are one constant times a product-fibre sum. -/
lemma config_identity (sf sg so : Status) (Wt B L : ℝ)
    (Pf Pg Po : Vec3 → ℝ) (af ag ao : Fin 3 → SpinLetter)
    (hPf : ∀ x, Pf (spinVector x) = localProduct (fun k => spinVector (af k)) (spinVector x))
    (hPg : ∀ x, Pg (spinVector x) = localProduct (fun k => spinVector (ag k)) (spinVector x))
    (hPo : ∀ x, Po (spinVector x) = localProduct (fun k => spinVector (ao k)) (spinVector x))
    (F : (Fin 3 → Vec3) → ℝ) :
    Wt * siteFunctional sf (fun v1 => siteFunctional sg (fun v2 => siteFunctional so
      (fun v3 => F ![v1, v2, v3] * (B * Pf v1 * Pg v2 * Po v3) * L))) =
    (Wt * B * L) * ∑ t : Fin 3 → SpinLetter,
      (∏ j, fibreDensity ![sf, sg, so] ![af, ag, ao] j (t j)) *
        F (fun j => spinVector (t j)) := by
  rw [sum_three]
  simp only [siteFunctional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  have hv : (fun j => spinVector (![x, y, z] j)) =
      ![spinVector x, spinVector y, spinVector z] := by
    funext j
    fin_cases j <;> rfl
  rw [hv, Fin.prod_univ_three, hPf x, hPg y, hPo z]
  simp only [fibreDensity, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The fibre expansion for any network and any three distinct, mutually
nonadjacent active sites with at most three present bonds and no original legs. -/
theorem expansion_general {G : Finset Plane} (D : Network G) (τ : PinAssignment G) (b : Bool)
    (f g o : Plane) (hfg : f ≠ g) (hfo : f ≠ o) (hgo : g ≠ o)
    (hfA : f ∈ D.active) (hgA : g ∈ D.active) (hoA : o ∈ D.active)
    (hfc : (D.presentNeighbours f).card ≤ 3) (hgc : (D.presentNeighbours g).card ≤ 3)
    (hoc : (D.presentNeighbours o).card ≤ 3)
    (ngf : ¬ Adjacent g f) (nof : ¬ Adjacent o f) (nog : ¬ Adjacent o g)
    (hlf : ∀ e : originalLegs G, e.val.1 ≠ f) (hlg : ∀ e : originalLegs G, e.val.1 ≠ g)
    (hlo : ∀ e : originalLegs G, e.val.1 ≠ o) :
    ∃ (N : ℕ) (C : Fin N → ℝ) (fields : Fin N → Fin 3 → Fin 3 → SpinLetter),
      (∀ r, 0 ≤ C r) ∧ ∀ F : (Fin 3 → Vec3) → ℝ,
        D.partition τ b (fun v => F ![v f, v g, v o]) =
          ∑ r, C r * ∑ t : Fin 3 → SpinLetter,
            (∏ j, fibreDensity ![D.status f, D.status g, D.status o] (fields r) j (t j)) *
              F (fun j => spinVector (t j)) := by
  obtain ⟨W, hWdef⟩ : ∃ W : Finset Plane, W = ((D.active.erase o).erase g).erase f :=
    ⟨_, rfl⟩
  have h1 : insert f W = (D.active.erase o).erase g := by
    rw [hWdef]
    exact Finset.insert_erase (Finset.mem_erase.2 ⟨hfg, Finset.mem_erase.2 ⟨hfo, hfA⟩⟩)
  have h2 : insert g ((D.active.erase o).erase g) = D.active.erase o :=
    Finset.insert_erase (Finset.mem_erase.2 ⟨hgo, hgA⟩)
  have h3 : insert o (D.active.erase o) = D.active := Finset.insert_erase hoA
  have nf : f ∉ W := by rw [hWdef]; exact Finset.notMem_erase f _
  have ng : g ∉ insert f W := by rw [h1]; exact Finset.notMem_erase g _
  have no : o ∉ insert g (insert f W) := by
    rw [h1, h2]; exact Finset.notMem_erase o _
  have hgf' : ∀ z ∈ (removeSite D o).presentNeighbours g, z ≠ f := by
    intro z hz hzf
    subst hzf
    exact ngf (adjacent_of_mem_pN hz)
  have hof' : ∀ z ∈ D.presentNeighbours o, z ≠ f := by
    intro z hz hzf
    subst hzf
    exact nof (adjacent_of_mem_pN hz)
  have hog' : ∀ z ∈ D.presentNeighbours o, z ≠ g := by
    intro z hz hzg
    subst hzg
    exact nog (adjacent_of_mem_pN hz)
  have hNf : ((removeSite (removeSite D o) g).presentNeighbours f).card ≤ 3 :=
    (Finset.card_le_card ((remove_presentNeighbours_subset _ g f).trans
      (remove_presentNeighbours_subset D o f))).trans hfc
  have hNg : ((removeSite D o).presentNeighbours g).card ≤ 3 :=
    (Finset.card_le_card (remove_presentNeighbours_subset D o g)).trans hgc
  choose af haf using fun n : W → SpinLetter =>
    pad_fields (letterOf W n) 3 ((removeSite (removeSite D o) g).presentNeighbours f) hNf
  choose ag hag using fun n : W → SpinLetter =>
    pad_fields (letterOf W n) 3 ((removeSite D o).presentNeighbours g) hNg
  choose ao hao using fun n : W → SpinLetter =>
    pad_fields (letterOf W n) 3 (D.presentNeighbours o) hoc
  let C : (W → SpinLetter) → ℝ := fun n =>
    (∏ x : W, spinWeight (D.status x) (n x)) *
      bondProduct (removeSite (removeSite (removeSite D o) g) f).bonds (extend W n) *
      legProduct D.active τ b (extend W n)
  let fields : (W → SpinLetter) → Fin 3 → Fin 3 → SpinLetter := fun n => ![af n, ag n, ao n]
  let e := Fintype.equivFin (W → SpinLetter)
  refine ⟨Fintype.card (W → SpinLetter), fun r => C (e.symm r), fun r => fields (e.symm r),
    ?_, ?_⟩
  · intro r
    exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun x _ => spin_weight_nonneg _ _)
      (bondProduct_extend_nonneg _ _ _)) (legProduct_extend_nonneg _ _ _ _ _)
  · intro F
    rw [e.symm.sum_comp (fun n => C n * ∑ t : Fin 3 → SpinLetter,
      (∏ j, fibreDensity ![D.status f, D.status g, D.status o] (fields n) j (t j)) *
        F (fun j => spinVector (t j)))]
    rw [partition_spinSum]
    have hA : spinSum D.active D.status
        (fun n => F ![n f, n g, n o] * bondProduct D.bonds n * legProduct D.active τ b n) =
        spinSum (insert o (insert g (insert f W))) D.status
        (fun n => F ![n f, n g, n o] * bondProduct D.bonds n * legProduct D.active τ b n) := by
      rw [h1, h2, h3]
    rw [hA, spinSum_insert' _ o no, spinSum_insert' _ g ng, spinSum_insert' _ f nf]
    unfold spinSum
    apply Finset.sum_congr rfl
    intro n _
    simp only [Function.update_self, Function.update_of_ne hfo, Function.update_of_ne hfg,
      Function.update_of_ne hgo, bond_split3 D f g o hgf' hof' hog',
      legProduct_update D.active τ b o hlo, legProduct_update D.active τ b g hlg,
      legProduct_update D.active τ b f hlf]
    have h0 : ∀ x : SpinLetter, (fun l : SpinLetter => 1 + dot (spinVector x) (spinVector l))
        none = 1 := by
      intro x
      show 1 + dot (spinVector x) 0 = 1
      rw [dot_zero_right]
      ring
    have hPf : ∀ x : SpinLetter,
        (∏ z ∈ (removeSite (removeSite D o) g).presentNeighbours f,
          (1 + dot (spinVector x) (extend W n z))) =
        localProduct (fun k => spinVector (af n k)) (spinVector x) := by
      intro x
      simp only [extend_eq_letter]
      exact haf n (fun l => 1 + dot (spinVector x) (spinVector l)) (h0 x)
    have hPg : ∀ x : SpinLetter,
        (∏ z ∈ (removeSite D o).presentNeighbours g,
          (1 + dot (spinVector x) (extend W n z))) =
        localProduct (fun k => spinVector (ag n k)) (spinVector x) := by
      intro x
      simp only [extend_eq_letter]
      exact hag n (fun l => 1 + dot (spinVector x) (spinVector l)) (h0 x)
    have hPo : ∀ x : SpinLetter,
        (∏ z ∈ D.presentNeighbours o, (1 + dot (spinVector x) (extend W n z))) =
        localProduct (fun k => spinVector (ao n k)) (spinVector x) := by
      intro x
      simp only [extend_eq_letter]
      exact hao n (fun l => 1 + dot (spinVector x) (spinVector l)) (h0 x)
    exact config_identity (D.status f) (D.status g) (D.status o)
      (∏ x : W, spinWeight (D.status x) (n x))
      (bondProduct (removeSite (removeSite (removeSite D o) g) f).bonds (extend W n))
      (legProduct D.active τ b (extend W n))
      (fun v => ∏ z ∈ (removeSite (removeSite D o) g).presentNeighbours f,
        (1 + dot v (extend W n z)))
      (fun v => ∏ z ∈ (removeSite D o).presentNeighbours g, (1 + dot v (extend W n z)))
      (fun v => ∏ z ∈ D.presentNeighbours o, (1 + dot v (extend W n z)))
      (af n) (ag n) (ao n) hPf hPg hPo F

/-- The residual of `FibreExpansion.lean`, proved. -/
theorem fibreExpansion : Residual_FibreExpansion := by
  intro a hU f g hN hof hog hfg b
  have hfN : f ∈ a.D.presentNeighbours a.y := by rw [hN]; simp
  have hgN : g ∈ a.D.presentNeighbours a.y := by rw [hN]; simp
  have hoN : a.o ∈ a.D.presentNeighbours a.y := a.present
  have aF := adjacent_of_mem_pN hfN
  have aG := adjacent_of_mem_pN hgN
  have aO := adjacent_of_mem_pN hoN
  obtain ⟨hfA, hfS⟩ := neighbour_survives hfN
  obtain ⟨hgA, hgS⟩ := neighbour_survives hgN
  obtain ⟨hoA, hoS⟩ := neighbour_survives hoN
  obtain ⟨N, C, fields, hC, hE⟩ := expansion_general (removeSite a.D a.y) a.τ b f g a.o
    hfg hof.symm hog.symm hfA hgA hoA
    (neighbour_removed_card a.auxiliary hfN) (neighbour_removed_card a.auxiliary hgN)
    (neighbour_removed_card a.auxiliary hoN)
    (neighbours_nonadjacent a.y g f aG aF) (neighbours_nonadjacent a.y a.o f aO aF)
    (neighbours_nonadjacent a.y a.o g aO aG)
    (fun e => no_leg_at_neighbour a.start hfN e.val e.property)
    (fun e => no_leg_at_neighbour a.start hgN e.val e.property)
    (fun e => no_leg_at_neighbour a.start hoN e.val e.property)
  refine ⟨N, C, ![(removeSite a.D a.y).status f, (removeSite a.D a.y).status g,
    (removeSite a.D a.y).status a.o], fields, hC, ?_, hE⟩
  intro j
  fin_cases j
  · simpa using hfS
  · simpa using hgS
  · simpa using hoS

end AKLT.W.REC004
