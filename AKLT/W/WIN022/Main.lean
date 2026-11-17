module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN022

private def edgeBoundary (e : LatticeEdge) : Plane →₀ ZMod 2 :=
  Sym2.lift ⟨fun a b => Finsupp.single a 1 + Finsupp.single b 1, by
    intro a b
    exact add_comm _ _⟩ e

private def edgeBoundaryMap (e : LatticeEdge) : ZMod 2 →ₗ[ZMod 2] (Plane →₀ ZMod 2) where
  toFun a := a • edgeBoundary e
  map_add' a b := by simp [add_smul]
  map_smul' a b := by simp [mul_smul]

private def chainBoundary : EdgeChain →ₗ[ZMod 2] (Plane →₀ ZMod 2) :=
  Finsupp.lsum (ZMod 2) edgeBoundaryMap

private theorem chainBoundary_edge (x y : Plane) :
    chainBoundary (edge x y) = Finsupp.single x 1 + Finsupp.single y 1 := by
  simp [chainBoundary, edge, edgeBoundaryMap, edgeBoundary, Sym2.lift_mk]

private theorem edgeBoundary_apply_of_ne {e : LatticeEdge} {x : Plane}
    (he : ∃ a b, e = s(a, b) ∧ a ≠ b) :
    edgeBoundary e x = if x ∈ e then 1 else 0 := by
  obtain ⟨a, b, rfl, hab⟩ := he
  rw [edgeBoundary, Sym2.lift_mk]
  simp only [Finsupp.add_apply, Finsupp.single_apply, Sym2.mem_iff]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [eq_comm]

private theorem chainBoundary_apply (c : EdgeChain) (x : Plane) :
    chainBoundary c x = ∑ e ∈ c.support, c e * edgeBoundary e x := by
  simp only [chainBoundary, Finsupp.lsum_apply]
  simp only [Finsupp.sum_apply, edgeBoundaryMap]
  simp [Finsupp.sum, mul_comm]

private theorem chainEven_of_boundary_zero (c : EdgeChain)
    (hc : ChainStar c) (hb : ∀ x, chainBoundary c x = 0) : ChainEven c := by
  intro x
  calc
    (∑ e ∈ c.support, if x ∈ e then c e else 0) =
        ∑ e ∈ c.support, c e * edgeBoundary e x := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨a, b, hab, hstar⟩ := hc e he
      have hne : a ≠ b := by
        intro h
        subst b
        simp [StarAdjacent, supDist] at hstar
      rw [edgeBoundary_apply_of_ne ⟨a, b, hab, hne⟩]
      by_cases hxe : x ∈ e <;> simp [hxe]
    _ = chainBoundary c x := (chainBoundary_apply c x).symm
    _ = 0 := hb x

private inductive FiniteWalk (R : Plane → Plane → Prop) : Plane → Plane → Type
  | refl (x : Plane) : FiniteWalk R x x
  | snoc {x y z : Plane} : FiniteWalk R x y → R y z → FiniteWalk R x z

private theorem reflTransGen_hasWalk {R : Plane → Plane → Prop} {x y : Plane}
    (h : Relation.ReflTransGen R x y) : Nonempty (FiniteWalk R x y) := by
  induction h with
  | refl => exact ⟨FiniteWalk.refl _⟩
  | tail h hstep ih =>
      rcases ih with ⟨w⟩
      exact ⟨FiniteWalk.snoc w hstep⟩

private def walkChain {R : Plane → Plane → Prop} : {x y : Plane} →
    FiniteWalk R x y → EdgeChain
  | _, _, FiniteWalk.refl _ => 0
  | _, _, @FiniteWalk.snoc _ _ b c w _ => walkChain w + edge b c

private theorem chainStar_add {c d : EdgeChain} (hc : ChainStar c) (hd : ChainStar d) :
    ChainStar (c + d) := by
  intro e he
  have hmem : e ∈ c.support ∨ e ∈ d.support := by
    by_contra hn
    push Not at hn
    have hcz : c e = 0 := Finsupp.notMem_support_iff.mp hn.1
    have hdz : d e = 0 := Finsupp.notMem_support_iff.mp hn.2
    exact (Finsupp.mem_support_iff.mp he) (by simp [hcz, hdz])
  rcases hmem with hmem | hmem
  · exact hc e hmem
  · exact hd e hmem

private theorem chainStar_edge {x y : Plane} (hxy : StarAdjacent x y) :
    ChainStar (edge x y) := by
  intro e he
  have heq : e = s(x, y) := by simpa [edge] using he
  exact ⟨x, y, heq, hxy⟩

private theorem walkChain_star {R : Plane → Plane → Prop}
    (hR : ∀ a b, R a b → StarAdjacent a b) {x y : Plane} (w : FiniteWalk R x y) :
    ChainStar (walkChain w) := by
  induction w with
  | refl => simp [walkChain, ChainStar]
  | snoc w hab ih =>
      rw [walkChain]
      exact chainStar_add ih (chainStar_edge (hR _ _ hab))

private theorem walkChain_boundary {R : Plane → Plane → Prop} {x y : Plane}
    (w : FiniteWalk R x y) :
    chainBoundary (walkChain w) = Finsupp.single x 1 + Finsupp.single y 1 := by
  induction w with
  | refl =>
      rw [walkChain]
      have hs : Finsupp.single x (1 : ZMod 2) + Finsupp.single x 1 = 0 := by
        ext z
        by_cases hz : z = x <;> simp [hz, CharTwo.add_self_eq_zero]
      rw [chainBoundary.map_zero, hs]
  | @snoc prev mid w hab ih =>
      rw [walkChain, chainBoundary.map_add, ih, chainBoundary_edge]
      have hs : Finsupp.single prev (1 : ZMod 2) + Finsupp.single prev 1 = 0 := by
        ext z
        by_cases hz : z = prev <;> simp [hz, CharTwo.add_self_eq_zero]
      calc
        (Finsupp.single x (1 : ZMod 2) + Finsupp.single prev 1) +
            (Finsupp.single prev 1 + Finsupp.single mid 1) =
          (Finsupp.single x 1 +
            (Finsupp.single prev 1 + Finsupp.single prev 1)) + Finsupp.single mid 1 := by
              ac_rfl
        _ = (Finsupp.single x 1 + 0) + Finsupp.single mid 1 := by simp [hs]
        _ = Finsupp.single x 1 + Finsupp.single mid 1 := by simp

private theorem walkChain_coeff_zero {S : Set Plane}
    {R : Plane → Plane → Prop} (hR : ∀ a b, R a b → a ∈ S ∧ b ∈ S)
    {x y : Plane} (w : FiniteWalk R x y) (g : LatticeEdge)
    (hno : ∀ a b, a ∈ S → b ∈ S → s(a, b) ≠ g) : walkChain w g = 0 := by
  induction w with
  | refl => simp [walkChain]
  | snoc w hab ih =>
      have hends := hR _ _ hab
      simp [walkChain, ih, edge, hno _ _ hends.1 hends.2]

private theorem starBall_sup_le_one {x y : Plane} (hy : y ∈ starBall x) :
    supDist x y ≤ 1 := by
  rcases Finset.mem_product.mp hy with ⟨h1, h2⟩
  simp only [Finset.mem_Icc] at h1 h2
  have hx : x.1 - y.1 = -1 ∨ x.1 - y.1 = 0 ∨ x.1 - y.1 = 1 := by omega
  have hy' : x.2 - y.2 = -1 ∨ x.2 - y.2 = 0 ∨ x.2 - y.2 = 1 := by omega
  rcases hx with hx | hx | hx <;> rcases hy' with hy | hy | hy <;>
    simp [supDist, hx, hy]

private theorem cutEdge_repr {A : Finset Plane} {e : LatticeEdge} (he : e ∈ cutEdges A) :
    ∃ x y : Plane, x ∈ A ∧ y ∉ A ∧ e = s(x, y) ∧ StarAdjacent x y := by
  classical
  simp only [cutEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_sdiff] at he
  obtain ⟨x, hx, y, hy, rfl⟩ := he
  have hsup : supDist x y ≤ 1 := starBall_sup_le_one hy.1
  have hne : x ≠ y := by
    intro h
    subst y
    exact hy.2 hx
  have hnezero : supDist x y ≠ 0 := by
    intro hz
    apply hne
    apply Prod.ext
    · have hleft : (x.1 - y.1).natAbs = 0 := by
        have hle : (x.1 - y.1).natAbs ≤ supDist x y := Nat.le_max_left _ _
        simpa [hz] using hle
      exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hleft)
    · have hright : (x.2 - y.2).natAbs = 0 := by
        have hle : (x.2 - y.2).natAbs ≤ supDist x y := Nat.le_max_right _ _
        simpa [hz] using hle
      exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp hright)
  refine ⟨x, y, hx, hy.2, rfl, ?_⟩
  unfold StarAdjacent
  omega

private theorem cutEdge_not_internal {A : Finset Plane} {g : LatticeEdge}
    (hg : g ∈ cutEdges A) {a b : Plane} (ha : a ∈ A) (hb : b ∈ A) :
    s(a, b) ≠ g := by
  obtain ⟨x, y, hx, hy, rfl, _⟩ := cutEdge_repr hg
  intro h
  have hmem : y ∈ s(x, y) := Sym2.mem_mk_right _ _
  have hmem' : y ∈ s(a, b) := h.symm ▸ hmem
  rcases Sym2.mem_iff.mp hmem' with hya | hyb
  · exact hy (hya ▸ ha)
  · exact hy (hyb ▸ hb)

private theorem cutEdge_not_external {A : Finset Plane} {g : LatticeEdge}
    (hg : g ∈ cutEdges A) {a b : Plane} (ha : a ∉ A) (hb : b ∉ A) :
    s(a, b) ≠ g := by
  obtain ⟨x, y, hx, hy, rfl, _⟩ := cutEdge_repr hg
  intro h
  have hmem : x ∈ s(x, y) := Sym2.mem_mk_left _ _
  have hmem' : x ∈ s(a, b) := h.symm ▸ hmem
  rcases Sym2.mem_iff.mp hmem' with hxa | hxb
  · exact ha (hxa ▸ hx)
  · exact hb (hxb ▸ hx)

private theorem single_edge_star {e : LatticeEdge} (he : ∃ a b, e = s(a, b) ∧ StarAdjacent a b) :
    ChainStar (Finsupp.single e 1) := by
  intro g hg
  have hge : g = e := by simpa using hg
  obtain ⟨a, b, rfl, hab⟩ := he
  exact ⟨a, b, hge, hab⟩

theorem main : AKLT.Blueprint.Win.TwoCrossingCycleStatement := by
  classical
  intro A hA hAc e he f hf hef
  obtain ⟨a, b, ha, hb, heq, hab⟩ := cutEdge_repr he
  obtain ⟨a', b', ha', hb', hfeq, ha'b'⟩ := cutEdge_repr hf
  let Rin : Plane → Plane → Prop := fun x y => x ∈ (A : Set Plane) ∧ y ∈ (A : Set Plane) ∧ StarAdjacent x y
  let Rout : Plane → Plane → Prop := fun x y => x ∈ {z : Plane | z ∉ A} ∧ y ∈ {z : Plane | z ∉ A} ∧ StarAdjacent x y
  have hin : Relation.ReflTransGen Rin a a' := by
    exact hA.2 a ha a' ha'
  have hout : Relation.ReflTransGen Rout b' b := by
    exact hAc.2 b' hb' b hb
  let wi := Classical.choice (reflTransGen_hasWalk hin)
  let wo := Classical.choice (reflTransGen_hasWalk hout)
  let c : EdgeChain := (walkChain wi + Finsupp.single f 1) +
    (walkChain wo + Finsupp.single e 1)
  have hstar : ChainStar c := by
    apply chainStar_add
    · apply chainStar_add
      · exact walkChain_star (fun _ _ h => h.2.2) wi
      · exact single_edge_star ⟨a', b', hfeq, ha'b'⟩
    · apply chainStar_add
      · exact walkChain_star (fun _ _ h => h.2.2) wo
      · exact single_edge_star ⟨a, b, heq, hab⟩
  have hbi : chainBoundary (walkChain wi) = Finsupp.single a 1 + Finsupp.single a' 1 :=
    walkChain_boundary wi
  have hbo : chainBoundary (walkChain wo) = Finsupp.single b' 1 + Finsupp.single b 1 :=
    walkChain_boundary wo
  have hcrossF : chainBoundary (Finsupp.single f 1) = Finsupp.single a' 1 + Finsupp.single b' 1 := by
    have heqchain : Finsupp.single f 1 = edge a' b' := by rw [hfeq]; rfl
    rw [heqchain, chainBoundary_edge]
  have hcrossE : chainBoundary (Finsupp.single e 1) = Finsupp.single a 1 + Finsupp.single b 1 := by
    have heqchain : Finsupp.single e 1 = edge a b := by rw [heq]; rfl
    rw [heqchain, chainBoundary_edge]
  have hboundary : chainBoundary c = 0 := by
    dsimp [c]
    rw [chainBoundary.map_add, chainBoundary.map_add, chainBoundary.map_add,
      hbi, hcrossF, hbo, hcrossE]
    ext z
    simp [Finsupp.add_apply, add_left_comm, add_comm, CharTwo.add_self_eq_zero]
  have heven : ChainEven c := chainEven_of_boundary_zero c hstar (fun z => by
    simpa using congrArg (fun d : Plane →₀ ZMod 2 => d z) hboundary)
  refine ⟨c, hstar, heven, ?_⟩
  intro g hg
  have hpi : walkChain wi g = 0 :=
    walkChain_coeff_zero (fun _ _ h => ⟨h.1, h.2.1⟩) wi g
      (fun a b ha hb => cutEdge_not_internal hg (by simpa using ha) (by simpa using hb))
  have hpo : walkChain wo g = 0 :=
    walkChain_coeff_zero (fun _ _ h => ⟨h.1, h.2.1⟩) wo g
      (fun a b ha hb => cutEdge_not_external hg (by simpa using ha) (by simpa using hb))
  by_cases hge : g = e
  · subst g
    simp [c, hpi, hpo, hef]
  · by_cases hgf : g = f
    · subst g
      simp [c, hpi, hpo, hef]
    · simp [c, hpi, hpo, hge, hgf]

#print axioms main

end AKLT.W.WIN022
