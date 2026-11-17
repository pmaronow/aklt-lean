module
public import AKLT.Blueprint.Rec.NodesRecursion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC082

/-- A removed center is never an active site. -/
theorem removed_not_active {G : Finset Plane} (D : Network G) {c : Plane}
    (hc : D.status c = .X) : c ∉ D.active := by
  simp [Network.active, hc]

/-- Erasing a kept flag directed at a removed site changes no present bond. -/
theorem normalizeStart_present {G : Finset Plane} (D : Network G) (u c x y : Plane)
    (hc : D.status c = .X) :
    (normalizeStart D u c).Present x y ↔ D.Present x y := by
  classical
  have ha : (normalizeStart D u c).active = D.active := rfl
  have hkept (z t : Plane) (ht : t ∈ D.active) :
      t ∈ (normalizeStart D u c).kept z ↔ t ∈ D.kept z := by
    have htc : t ≠ c := by
      intro h
      exact removed_not_active D hc (h ▸ ht)
    dsimp [normalizeStart]
    split_ifs <;> simp [htc]
  constructor
  · rintro ⟨hx, hy, hxy, hky, hkx⟩
    rw [ha] at hx hy
    exact ⟨hx, hy, hxy, (hkept x y hy).mp hky, (hkept y x hx).mp hkx⟩
  · rintro ⟨hx, hy, hxy, hky, hkx⟩
    exact ⟨ha.symm ▸ hx, ha.symm ▸ hy, hxy,
      (hkept x y hy).mpr hky, (hkept y x hx).mpr hkx⟩

theorem normalizeStart_bonds {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) : (normalizeStart D u c).bonds = D.bonds := by
  classical
  ext e
  simp only [Network.bonds, Finset.mem_filter]
  rw [normalizeStart_present D u c e.1 e.2 hc]

theorem normalizeStart_presentNeighbours {G : Finset Plane} (D : Network G)
    (u c x : Plane) (hc : D.status c = .X) :
    (normalizeStart D u c).presentNeighbours x = D.presentNeighbours x := by
  classical
  ext y
  simp only [Network.presentNeighbours, Finset.mem_filter]
  rw [normalizeStart_present D u c x y hc]

/-- The normalization changes no spin law, bond factor, or original pin factor. -/
theorem normalizeStart_partition {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    (normalizeStart D u c).partition τ b f = D.partition τ b f := by
  unfold Network.partition
  rw [normalizeStart_bonds D u c hc]
  rfl

theorem normalizeStart_expectation {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) :
    (normalizeStart D u c).expectation τ b f = D.expectation τ b f := by
  simp only [Network.expectation, normalizeStart_partition D u c hc]

/-- Normalization preserves the auxiliary local restrictions. -/
theorem normalizeStart_auxiliary {G : Finset Plane} (D : Network G) (u c : Plane)
    (hc : D.status c = .X) (hD : D.Auxiliary) :
    (normalizeStart D u c).Auxiliary := by
  classical
  rcases hD with ⟨⟨hout, hkept, hDdeg, hdeg⟩, hprotected⟩
  refine ⟨⟨hout, ?_, ?_, ?_⟩, hprotected⟩
  · intro x z hz
    apply hkept x
    dsimp [normalizeStart] at hz
    split_ifs at hz with h
    · exact Finset.mem_of_mem_erase hz
    · exact hz
  · intro x hx hs
    simpa only [normalizeStart_presentNeighbours D u c x hc] using hDdeg x hx hs
  · intro x hx
    simpa only [normalizeStart_presentNeighbours D u c x hc] using hdeg x hx

/-- The pair assumptions provide ordinary local rules without any further leaves. -/
theorem pair_auxiliary (p : PairData) : p.D.Auxiliary :=
  ⟨p.pair.1.1.1, fun x hx => (p.pair.1.1.2 x hx).1⟩

theorem pair_c_removed (p : PairData) : p.D.status p.c = .X :=
  p.pair.2.2.2.2.1

theorem pair_u_active (p : PairData) : p.u ∈ p.D.active := p.pair.2.1

theorem pair_v_active (p : PairData) : p.v ∈ p.D.active := p.pair.2.2.1

/-- The target factor is unaffected because normalization changes only kept flags. -/
theorem normalized_targetFactor (p : PairData) :
    targetFactor p.normalized p.v = targetFactor p.D p.v := rfl

theorem normalized_auxiliary (p : PairData) : p.normalized.Auxiliary :=
  normalizeStart_auxiliary p.D p.u p.c (pair_c_removed p) (pair_auxiliary p)

theorem normalized_expectation (p : PairData) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    p.normalized.expectation p.τ b f = p.D.expectation p.τ b f :=
  normalizeStart_expectation p.D p.u p.c (pair_c_removed p) p.τ b f

end AKLT.W.REC082
