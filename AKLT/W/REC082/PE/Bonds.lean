module
public import AKLT.W.REC082.PE.Trace

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC082.PE

private theorem positive_not_reverse {x y : Plane} (h : y ∈ positiveNeighbors x) :
    x ∉ positiveNeighbors y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [positiveNeighbors, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at *
  omega

private theorem bond_positive {G : Finset Plane} {D : Network G} {e : Plane × Plane}
    (h : e ∈ D.bonds) : e.2 ∈ positiveNeighbors e.1 := by
  obtain ⟨hi, _⟩ := Finset.mem_filter.mp h
  obtain ⟨x, hx, he⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp he
  subst e
  exact (Finset.mem_inter.mp hy).1

private def canonicalBond (u o : Plane) : Plane × Plane :=
  if o ∈ positiveNeighbors u then (u, o) else (o, u)

private theorem canonicalBond_mem {G : Finset Plane} {D : Network G} {u o : Plane}
    (h : D.Present u o) : canonicalBond u o ∈ D.bonds := by
  rcases present_mem_bonds h with hb | hb
  · simp [canonicalBond, bond_positive hb, hb]
  · have ho := positive_not_reverse (bond_positive hb)
    simp [canonicalBond, ho, hb]

private theorem canonicalBond_injective (u : Plane) : Function.Injective (canonicalBond u) := by
  intro o p h
  have hh (o : Plane) : (if (canonicalBond u o).1 = u then
      (canonicalBond u o).2 else (canonicalBond u o).1) = o := by
    by_cases ho : o ∈ positiveNeighbors u
    · simp [canonicalBond, ho]
    · by_cases hou : o = u <;> simp [canonicalBond, ho, hou]
  have he := congrArg (fun e : Plane × Plane => if e.1 = u then e.2 else e.1) h
  simpa only [hh] using he

/-- Nonincident bond factors, which are common to all choices at u. -/
def exteriorBonds {G : Finset Plane} (D : Network G) (u : Plane) : Finset (Plane × Plane) :=
  D.bonds.filter (fun e => ¬ (e.1 = u ∨ e.2 = u))

/-- Split off all factors incident to a distinguished site, counting each
unoriented present bond once in both enumerations. -/
theorem bond_product_split {G : Finset Plane} (D : Network G) (u : Plane)
    (f : Plane → Plane → ℝ) (hf : ∀ x y, f x y = f y x) :
    (∏ e ∈ D.bonds, f e.1 e.2) =
      (∏ o ∈ D.presentNeighbors u, f u o) *
        ∏ e ∈ exteriorBonds D u, f e.1 e.2 := by
  classical
  have hi : (∏ o ∈ D.presentNeighbors u, f u o) =
      ∏ e ∈ D.bonds.filter (fun e => e.1 = u ∨ e.2 = u), f e.1 e.2 := by
    apply Finset.prod_bij (fun o _ => canonicalBond u o)
    · intro o ho
      refine Finset.mem_filter.mpr ⟨canonicalBond_mem (Finset.mem_filter.mp ho).2, ?_⟩
      simp only [canonicalBond]
      split_ifs <;> simp
    · intro o ho p hp he
      exact canonicalBond_injective u he
    · intro e he
      obtain ⟨hb, he⟩ := Finset.mem_filter.mp he
      have hp := (Finset.mem_filter.mp hb).2
      rcases e with ⟨x, y⟩
      rcases he with rfl | rfl
      · refine ⟨y, mem_presentNeighbors hp, ?_⟩
        simp [canonicalBond, bond_positive hb]
      · refine ⟨x, mem_presentNeighbors (present_symm hp), ?_⟩
        simp [canonicalBond, positive_not_reverse (bond_positive hb)]
    · intro o ho
      dsimp [canonicalBond]
      split_ifs
      · rfl
      · exact hf _ _
  rw [hi]
  exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm

/-- A step cannot affect the factors with neither endpoint at its departure. -/
theorem exteriorBonds_step {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) :
    exteriorBonds (traceStep D u o) u = exteriorBonds D u := by
  ext e
  simp only [exteriorBonds, Network.bonds, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, he⟩, hne⟩
    exact ⟨⟨hi, traceStep_present_subset D u o he⟩, hne⟩
  · rintro ⟨⟨hi, he⟩, hne⟩
    refine ⟨⟨hi, (traceStep_present_iff hu hp _ _).mpr ⟨he, ?_⟩⟩, hne⟩
    intro hb
    have hm : u ∈ ({e.1, e.2} : Finset Plane) := by rw [hb]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hne (hm.imp Eq.symm Eq.symm)

/-- Exactly the out-neighbor disappears from the departure neighbor set. -/
theorem departureNeighbors_step {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) :
    (traceStep D u o).presentNeighbors u = (D.presentNeighbors u).erase o := by
  ext x
  simp only [Network.presentNeighbors, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hn, hh⟩
    refine ⟨?_, hn, traceStep_present_subset D u o hh⟩
    intro he
    subst x
    exact traceStep_not_present D u o hh
  · rintro ⟨hxo, hn, hh⟩
    refine ⟨hn, (traceStep_present_iff hu hp _ _).mpr ⟨hh, ?_⟩⟩
    intro he
    have hm : o ∈ ({u, x} : Finset Plane) := by rw [he]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hou | hox
    · have hne : u ≠ o := by
        intro h; subst o
        simpa [Adjacent, latticeDist] using hp.2.2.1
      exact hne hou.symm
    · exact hxo hox.symm

end AKLT.W.REC082.PE
