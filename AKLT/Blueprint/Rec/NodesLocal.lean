import AKLT.Blueprint.Rec.NodesLogMean

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `l:local`, §6 lines 574–605. An actual tip has at most three external
fields. Replace it by a U tip with the same mean, multiplying both sums
by the same positive normalizer. This is the exact single-tip identity. -/
def TipReplacementStatement : Prop :=
  ∀ s : Status, s = .U ∨ s = .D → ∀ k : ℕ, k ≤ 3 →
    ∀ b : Fin k → Vec3, (∀ i, normSq (b i) ≤ 1) →
    ∃ a : Fin 3 → UnitVector, ∃ scale : ℝ, 0 < scale ∧
      ∀ v : Vec3,
        siteFunctional .U (fun n => (1 + dot n v) * ∏ i, (1 + dot n (a i).val)) =
          scale * siteFunctional s (fun n => (1 + dot n v) * ∏ i, (1 + dot n (b i)))

/-- `l:local`, §6 lines 607–623. Resolve a ball field into two antipodal
unit fields; b=0 fills an absent slot. Both weights are nonnegative. -/
def BallSlotConvexityStatement : Prop :=
  ∀ b : Vec3, normSq b ≤ 1 → ∃ e : UnitVector, ∃ t : ℝ,
    0 ≤ t ∧ t ≤ 1 ∧ ∀ n : Vec3,
      1 + dot n b = t * (1 + dot n e.val) + (1 - t) * (1 + dot n (-e.val))

/-- `l:local`, §6 lines 555–646. Disintegrate over the finite outside
spins, replace four tips, and resolve all eight corner slots. The common
nonnegative mixture represents both partitions, including original legs.
This is the final gluing step, after the one-tip and one-slot reductions. -/
def LocalMixtureStatement : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ incoming outgoing : Compass,
    a.o = a.y + outgoing.step → CoveredDepartureV2 a.D a.y incoming outgoing →
    ∃ k : ℕ, ∃ π : Fin k → PatternData, ∃ m : Fin k → (Fin 20 → UnitVector),
      ∃ weight : Fin k → ℝ,
      (∀ i, 0 ≤ weight i ∧ (π i).Covered ∧
        ((π i).outgoing = .north ↔ outgoing = incoming)) ∧
      a.D.partition a.τ true (fun _ => 1) = ∑ i, weight i * patternCurrent (π i) (m i) ∧
      (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) =
        ∑ i, weight i * patternNext (π i) (m i)

/-- `l:local`, §6 lines 625–651. Apply H1 to each term of the common
mixture, then divide positive normalizers. V2 admits boundary corners. -/
def CoveredRatioStatement : Prop :=
  Top.H1Statement → ∀ a : Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
      CoveredDepartureV2 a.D a.y incoming outgoing →
      stepRatio a.D a.τ true a.y a.o ≤ (passageFactor (decide (outgoing = incoming)) : ℝ)

/-- `l:response-typed`, §7 lines 419–429 and 462–506. Translate the local
partition inequality into I^τ≥cJ^τ (or I₂^τ≥c). The denominator J is positive. -/
def CoveredIntegratedLowerStatement : Prop :=
  Top.H1Statement → ∀ a : Departure, a.D.status a.y = .U →
    ∀ incoming outgoing : Compass, a.o = a.y + outgoing.step →
      CoveredDepartureV2 a.D a.y incoming outgoing →
      let c : ℝ := localThreshold (decide (outgoing = incoming))
      (∀ f : Plane, a.D.presentNeighbours a.y = {a.o, f} → a.o ≠ f →
        c ≤ responseI₂ a.D a.τ true a.y a.o f) ∧
      ∀ f g : Plane, a.D.presentNeighbours a.y = {a.o, f, g} →
        a.o ≠ f → a.o ≠ g → f ≠ g →
        c * responseJ a.D a.τ true a.y f g ≤ responseI a.D a.τ true a.y a.o f g

/-- `l:response-typed`, §7 lines 497–506. This two-variable analytic
comparison uses only monotonicity of the positive logarithmic mean. -/
def BetaPrimeAnalyticStatement : Prop :=
  ∀ c It I₀ : ℝ, 0 < c → c ≤ It → 1 ≤ I₀ →
    1 / (3 * logarithmicMean It I₀) ≤ reciprocalLogMean c / 3

/-- `l:response-typed`, §7 lines 480–493. Use I^τ≥cJ^τ, I^0≥J^0,
J^τ≥116/125 and J^0≥1, then monotonicity. -/
def BetaAnalyticStatement : Prop :=
  ∀ c It I₀ Jt J₀ : ℝ, 3 / 5 ≤ c → c ≤ 1 →
    c * Jt ≤ It → J₀ ≤ I₀ → 116 / 125 ≤ Jt → 1 ≤ J₀ →
    1 / (3 * logarithmicMean It I₀) ≤ reciprocalLogMean ((116 / 125) * c) / 3

/-- `l:response-typed`, §7 lines 480–493. Preserve the subtraction term
when lowering I to cJ, then apply monotonicity of G_c to both J arguments. -/
def AlphaAnalyticStatement : Prop :=
  ∀ c It I₀ Jt J₀ : ℝ, 3 / 5 ≤ c → c ≤ 1 →
    c * Jt ≤ It → J₀ ≤ I₀ → 116 / 125 ≤ Jt → 1 ≤ J₀ →
    1 / (3 * logarithmicMean It I₀) - 1 / (5 * logarithmicMean Jt J₀) ≤
      reciprocalLogMean ((116 / 125) * c) / 3 - reciprocalLogMean (116 / 125) / 5

/-- Old exact matching implies V2 matching: every actual kept set is contained in G. -/
theorem coveredDeparture_to_v2 {G : Finset Plane} {D : Network G} (hD : D.Auxiliary)
    {y : Plane} {a o : Compass} (h : CoveredDeparture D y a o) :
    CoveredDepartureV2 D y a o := by
  obtain ⟨π, hπ, ho, hm⟩ := h
  refine ⟨π, hπ, ho, ?_⟩
  intro z hz
  obtain ⟨hs, hk⟩ := hm z hz
  refine ⟨hs, fun hX => ?_⟩
  rw [hk hX]
  exact Finset.inter_eq_left.mpr (fun x hx => (Finset.mem_inter.mp (hD.1.2.1 _ hx)).2)

end AKLT.Blueprint.Rec
