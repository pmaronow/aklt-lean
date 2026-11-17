module
public import AKLT.W.H1C013.Codec
public import AKLT.W.H1C013.Compiler

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
The accepted weight/parity list is identified with the unnormalized central
exchange basis through its mixed-radix coordinates.
-/
namespace AKLT.W.H1C013

open AKLT.Cert.H1.Production
open AKLT.Cert.H1 (PackedSite)
open AKLT.Defs

/-- The checked list of basis coordinates is exactly the selected weight and
parity fiber. -/
theorem basisCheck_coordinates
    (ss : List AKLT.Cert.H1.PackedSite) (parity : Nat) (weight : Int) (indices : List Nat)
    (h : basisCheck ss parity weight indices = true) :
    weight = AKLT.Cert.H1.Production.centralWeight ss ∧ parity ∈ exchangeParities ss ∧
      indices = sectorIndices ss parity weight ∧ indices ≠ [] := by
  have hs : ((weight = AKLT.Cert.H1.Production.centralWeight ss ∧
      parity ∈ exchangeParities ss) ∧
      indices = sectorIndices ss parity weight) ∧ indices ≠ [] := by
    simpa [basisCheck, List.contains_iff_mem] using h
  rcases hs with ⟨⟨⟨hw, hp⟩, hi⟩, hn⟩
  exact ⟨hw, hp, hi, hn⟩

/-- Extract the list and length facts carried by `Bundle.LayoutAccepted`. -/
theorem layout_coordinates
    (c : Case) (b : Bundle) (h : b.LayoutAccepted c) :
    b.block.indices = sectorIndices c.network b.block.parity b.block.weight ∧
    b.block.indices.length = b.block.M.length := by
  unfold Bundle.LayoutAccepted at h
  rcases h with ⟨hcheck, _hsector, _hremap, hlen, _hmapped⟩
  have hfacts := basisCheck_coordinates c.network b.block.parity b.block.weight
    b.block.indices hcheck
  exact ⟨hfacts.2.2.1, hlen⟩

/-- The production basis enumeration, with its literal checked list order. -/
theorem main : AKLT.Cert.H1.Production.Leaves.basisIndexing := by
  intro c hc b hb ε hpar
  have hg := checked_coordinates c.input hc.1 c.network hc.2.1
  rcases hb with ⟨hcheck, _hsector, _hremap, hlen, _hmapped⟩
  obtain ⟨hw,_hp,hi,_hne⟩ := basisCheck_coordinates c.network b.block.parity
    b.block.weight b.block.indices hcheck
  have hindices : b.block.indices = sectorIndices c.network
      (exchangeParity (inputPattern c.input) (inputRepresentation c.input) ε)
      (AKLT.Cert.H1.Production.centralWeight c.network) := by
    rw [hi, hpar, hw]
  obtain ⟨index,hcode⟩ := codec_of_geometry (inputPattern c.input)
    (inputRepresentation c.input) c.network hg ε b.block.indices hindices
  let cast : Fin b.block.M.length ≃ Fin b.block.indices.length := {
    toFun := fun i => Fin.cast hlen.symm i
    invFun := fun i => Fin.cast hlen i
    left_inv := by intro i; apply Fin.ext; rfl
    right_inv := by intro i; apply Fin.ext; rfl }
  refine ⟨cast.trans index, ?_⟩
  intro i
  exact hcode (Fin.cast hlen.symm i)

end AKLT.W.H1C013

#print axioms AKLT.W.H1C013.basisCheck_coordinates
#print axioms AKLT.W.H1C013.layout_coordinates
#print axioms AKLT.W.H1C013.main
