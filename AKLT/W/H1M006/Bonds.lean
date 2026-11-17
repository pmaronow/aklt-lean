module
public import AKLT.W.H1M006.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M006

theorem dot_symm (a b : Vec3) : dot a b = dot b a := by
  simp only [dot, mul_comm]

@[simp] theorem dot_zero_right (a : Vec3) : dot a 0 = 0 := by simp [dot]
@[simp] theorem dot_zero_left (a : Vec3) : dot 0 a = 0 := by simp [dot]

def bondFactor (π : PatternData) (next : Bool) (N : Plane → Vec3)
    (e : Plane × Plane) : ℝ :=
  if next ∧ ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step} then 1
  else 1 + dot (N e.1) (N e.2)

def bondProduct (π : PatternData) (next : Bool) (N : Plane → Vec3) : ℝ :=
  ∏ e ∈ π.bonds, bondFactor π next N e

def remainingBondProduct (π : PatternData) (N : Plane → Vec3) : ℝ :=
  ∏ e ∈ π.bonds, if e.1 = (0, 0) ∨ e.2 = (0, 0) then 1
    else 1 + dot (N e.1) (N e.2)

def slotProduct (π : PatternData) (m : Fin 20 → UnitVector) (N : Plane → Vec3) : ℝ :=
  ∏ j : Fin 20, if π.statusAt (externalSlot j).1 = .X then 1
    else 1 + dot (m j).val (N (externalSlot j).1)

def localPassageFactor (next : Bool) (z a b o : Vec3) : ℝ :=
  (1 + dot z a) * (1 + dot z b) * (if next then 1 else 1 + dot z o)

theorem out_edge_incident (π : PatternData) (e : Plane × Plane)
    (h : ({e.1, e.2} : Finset Plane) = {(0, 0), π.outgoing.step}) :
    e.1 = (0, 0) ∨ e.2 = (0, 0) := by
  have : (0, 0) ∈ ({e.1, e.2} : Finset Plane) := by rw [h]; simp
  simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using this

theorem split_bond_product (π : PatternData) (hπ : π.Covered) (next : Bool)
    (N : Plane → Vec3) (hzero : ∀ x, π.statusAt x = .X → N x = 0) :
    bondProduct π next N = remainingBondProduct π N *
      ∏ e ∈ passageEdges, bondFactor π next N e := by
  classical
  have hsplit : bondProduct π next N = remainingBondProduct π N *
      ∏ e ∈ π.bonds, if e.1 = (0, 0) ∨ e.2 = (0, 0) then bondFactor π next N e else 1 := by
    unfold bondProduct remainingBondProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e he
    by_cases hi : e.1 = (0, 0) ∨ e.2 = (0, 0)
    · simp only [hi, ↓reduceIte, one_mul]
    · have hout : ({e.1, e.2} : Finset Plane) ≠ {(0, 0), π.outgoing.step} :=
        fun h => hi (out_edge_incident π e h)
      simp [bondFactor, hi, hout]
  rw [hsplit, ← Finset.prod_filter, covered_incident_edges π hπ]
  congr 1
  apply Finset.prod_filter_of_ne
  intro e he hne
  by_contra hs
  push Not at hs
  have hz : N e.1 = 0 ∨ N e.2 = 0 := by
    by_cases h1 : π.statusAt e.1 = .X
    · exact Or.inl (hzero _ h1)
    · exact Or.inr (hzero _ (hs h1))
  apply hne
  rcases hz with hz | hz <;> simp [bondFactor, hz]

theorem origin_pair_eq (x o : Plane) (hx : x ≠ (0, 0)) :
    ({(0, 0), x} : Finset Plane) = {(0, 0), o} ↔ x = o := by
  constructor
  · intro h
    have : x ∈ ({(0, 0), o} : Finset Plane) := by rw [← h]; simp
    simpa [hx] using this
  · rintro rfl
    rfl

theorem passage_edges_product (π : PatternData) (next : Bool) (N : Plane → Vec3)
    (f g : Plane) (hn : PassageNeighbors π f g) :
    (∏ e ∈ passageEdges, bondFactor π next N e) =
      localPassageFactor next (N (0, 0)) (N f) (N g) (N π.outgoing.step) := by
  classical
  have hprod : (∏ e ∈ passageEdges, bondFactor π next N e) =
      ∏ x ∈ passageSites, if next ∧ x = π.outgoing.step then 1
        else 1 + dot (N (0, 0)) (N x) := by
    have hw : ({(-1, 0), (0, 0)} : Finset Plane) = {(0, 0), π.outgoing.step} ↔
        (-1, 0) = π.outgoing.step := by
      rw [Finset.pair_comm (-1, 0) (0, 0)]
      exact origin_pair_eq _ _ (by decide)
    simp [passageEdges, passageSites, bondFactor, origin_pair_eq,
      hw, dot_symm (N (-1, 0))]
  rw [hprod, show passageSites = {π.outgoing.step, f, g} from hn.1.symm]
  have hof := hn.2.1
  have hog := hn.2.2.1
  have hfg := hn.2.2.2
  simp [localPassageFactor, hof, hog, hfg, Ne.symm hof, Ne.symm hog,
    mul_comm]

theorem factor_bonds (π : PatternData) (hπ : π.Covered) (next : Bool)
    (N : Plane → Vec3) (hzero : ∀ x, π.statusAt x = .X → N x = 0)
    (f g : Plane) (hn : PassageNeighbors π f g) :
    bondProduct π next N = remainingBondProduct π N *
      localPassageFactor next (N (0, 0)) (N f) (N g) (N π.outgoing.step) := by
  rw [split_bond_product π hπ next N hzero, passage_edges_product π next N f g hn]

end AKLT.W.H1M006
