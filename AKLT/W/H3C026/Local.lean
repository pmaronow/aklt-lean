module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed

namespace AKLT.W.H3C026

theorem case_not_east (X : PairType) (d₀ : Compass)
    (h : (X,d₀) ∈ stationaryCases) : d₀ ≠ .east := by
  cases X <;> cases d₀ <;> simp_all [stationaryCases]

theorem known_sites_distinct (d₀ : Compass) :
    kernelStart ≠ kernelStart + d₀.step := by
  cases d₀ <;> decide +kernel

theorem known_forward_edge (d₀ d : Compass) :
    ({kernelStart, kernelStart + d.step} : Finset Plane) =
      {kernelStart, kernelStart + d₀.step} ↔ d = d₀ := by
  cases d₀ <;> cases d <;> decide +kernel

theorem known_reverse_edge (d₀ d : Compass) :
    ({kernelStart + d₀.step, kernelStart + d₀.step + d.step} : Finset Plane) =
      {kernelStart, kernelStart + d₀.step} ↔ d = d₀.reverse := by
  cases d₀ <;> cases d <;> decide +kernel

theorem correct_edge {m q : Nat} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (a : Fin q) (d : Compass) (ha : Q.allowed a d = true)
    (hn : Q.kind a d ≠ .revisit) :
    d ≠ (Q.arrival a).reverse ∧ (Q.kind a d = .straight ↔ d = Q.arrival a) := by
  have hr := hQ.1 a
  have he := hQ.2 (Q.representative a) hr.1 d
  rw [hr.2] at he
  have hadm := he.1.mp ha
  have hk := (he.2 hadm).1
  have hkn : windowKind (Q.representative a) d ≠ .revisit := by
    rwa [←hk]
  have har := (he.2 hadm).2.2 hkn
  refine ⟨?_, ?_⟩
  · simpa [har] using hadm.1
  · rw [hk, har]
    unfold windowKind at hkn ⊢
    split_ifs <;> simp_all

theorem tables_extended (T : Tables) (φ : Phase) (a : Fin 3741) (x : Plane) :
    T.data.extended φ a x = valueAt T.planeFn T.capFn φ a x := by
  change (if x ∈ square (0,0) certificateRadius then
    lane (T.planeFn φ a) 80 (siteIndex x) else T.capFn φ a) = _
  simp only [mem_square_iff, valueAt]

theorem tables_centre (T : Tables) (hT : CertData.H3.Bridge.TableBounds T)
    (φ : Phase) (a : Fin 3741) : T.data.extended φ a kernelCentre = 0 := by
  rw [tables_extended]
  simpa [valueAt, inBox, kernelCentre] using (hT φ a).2.2.2

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.case_not_east
#print axioms AKLT.W.H3C026.known_sites_distinct
#print axioms AKLT.W.H3C026.known_forward_edge
#print axioms AKLT.W.H3C026.known_reverse_edge
#print axioms AKLT.W.H3C026.correct_edge
#print axioms AKLT.W.H3C026.tables_extended
#print axioms AKLT.W.H3C026.tables_centre
