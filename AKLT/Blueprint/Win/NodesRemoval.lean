module
public import AKLT.Blueprint.Win.Defs

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Win

/-- `l:finitefacts`, sec5-window.tex:175–177,278–279. Reindex G\Y by Fin n, orient each bond once, and use FiniteFactsStatement for the U network. Zero U atoms disappear; the empty product equals one. -/
def OriginalPositivityStatement : Prop :=
  AKLT.Blueprint.Top.FiniteFactsStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G,
    0 < pinnedSum G Y τ (fun _ => 1) ∧ 0 < freeSum G Y (fun _ => 1)

/-- `l:finitefacts`, sec5-window.tex:276–301. Move the positive scalar normalizer through the finite sum. This identifies partMean with expectation under its actual normalized product weight. -/
def PartLawBridgeStatement : Prop :=
  AKLT.Blueprint.Top.MomentsStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ pinned : Bool,
    0 < partSum pinned G Y τ (fun _ => 1) →
    Probability (partLaw pinned G Y τ) ∧
    ∀ f : (Plane → Vec3) → ℝ,
      partMean pinned G Y τ f =
        expectation (partLaw pinned G Y τ) (fun σ => f (extendIcoSpins σ))

/-- `l:removal`, sec5-window.tex:248–255. Injectivity identifies each prefix update with insertion of the next site. The original-depth bound keeps all prefixes outside S(G); predecessor adjacency supplies the missing bond after the seed. -/
def EnumerationStepsStatement : Prop :=
  ∀ G X : Finset Plane, X ⊆ G → (∀ x ∈ X, 3 ≤ boundaryDepth G x) →
    ∀ e : RemovalEnumeration X,
    removedPrefix e 0 = ∅ ∧ removedPrefix e (e.last + 1) = X ∧
    ∀ j : Fin (e.last + 1),
      removedPrefix e (j.val + 1) = insert (e.site j) (removedPrefix e j.val) ∧
      RemovalStep G (removedPrefix e j.val) (e.site j) ∧
      (0 < j.val → ∃ c ∈ removedPrefix e j.val, Adjacent (e.site j) c)

/-- `l:removal`, sec5-window.tex:251–255,287–292,321–327. All four neighbors of a depth-three site are original interior sites. After removal they are pairwise at distance two, have at most three surviving bonds, and are at original depth at least two. -/
def SurvivorGeometryStatement : Prop :=
  ∀ G Y : Finset Plane, ∀ x : Plane, RemovalStep G Y x →
    (survivors G Y x).card ≤ 4 ∧
    (Y = ∅ → (survivors G Y x).card = 4) ∧
    ((∃ c ∈ Y, Adjacent x c) → (survivors G Y x).card ≤ 3) ∧
    (∀ z ∈ survivors G Y x, 2 ≤ boundaryDepth G z) ∧
    (∀ z ∈ survivors G Y x, ∀ w ∈ survivors G Y x, z ≠ w → latticeDist z w = 2)

/-- `e:removalpolynomial`, sec5-window.tex:257–279. Sum the removed site first. Odd tensors vanish, the second tensor supplies pairSum/3, and only all four surviving neighbors create quartic/15. Other sites retain their original legs. -/
def RemovalIntegralStatement : Prop :=
  AKLT.Blueprint.Top.MomentsStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane, RemovalStep G Y x →
    ∀ pinned : Bool,
      partSum pinned G Y τ (fun _ => 1) =
        partSum pinned G (insert x Y) τ (removalPolynomial x (survivors G Y x))

/-- `l:removal`, sec5-window.tex:287–301. Freeze the other spins on a positive fiber. Nonadjacency of the neighbors factors that fiber into one-site laws with at most three unit fields. Apply the three-factor mean bound and retain only positive fibers. -/
def NeighbourFibresStatement : Prop :=
  AKLT.Blueprint.Top.MomentsStatement → AKLT.Blueprint.Top.ThreeFactorMeanStatement →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane, RemovalStep G Y x →
    ∀ pinned : Bool,
      NeighbourControl (partLaw pinned G (insert x Y) τ) (survivors G Y x)

/-- `l:removal`, sec5-window.tex:303–310. On every positive fiber use 2∑mᵣ·mₜ=|∑mᵣ|²−∑|mᵣ|². Average the resulting lower bound; zero-mass fibers contribute zero. -/
def PairMeanAveragingStatement : Prop :=
  ∀ D V : Finset Plane, V ⊆ D → ∀ p : Weight (PlaneConfiguration D),
    Probability p → NeighbourControl p V →
    -(9 / 50 : ℝ) * (V.card : ℝ) ≤
      expectation p (fun σ => pairSum V (extendIcoSpins σ))

/-- `l:removal`, sec5-window.tex:311–315,345. Each scalar product of support vectors has absolute value at most one by Cauchy–Schwarz. The three products in quartic sum to at most three; average with a probability law. -/
def QuarticMeanBoundStatement : Prop :=
  AKLT.Blueprint.Top.MomentsStatement →
    ∀ D : Finset Plane, ∀ p : Weight (PlaneConfiguration D), Probability p →
    ∀ x : Plane, |expectation p (fun σ => quartic x (extendIcoSpins σ))| ≤ 3

/-- `l:removal`, sec5-window.tex:309–317. Linearity of expectation gives 1−3k/50, with an extra worst-case 3/15 only when k=4. Recover 41/50 or 14/25, both above one half. -/
def PolynomialLowerStatement : Prop :=
  ∀ D V : Finset Plane, ∀ p : Weight (PlaneConfiguration D), Probability p →
    ∀ x : Plane, V.card ≤ 4 →
    -(9 / 50 : ℝ) * (V.card : ℝ) ≤ expectation p (fun σ => pairSum V (extendIcoSpins σ)) →
    |expectation p (fun σ => quartic x (extendIcoSpins σ))| ≤ 3 →
    (if V.card = 4 then (14 / 25 : ℝ) else 41 / 50) ≤
      expectation p (fun σ => removalPolynomial x V (extendIcoSpins σ))

/-- `h:P`, sec5-window.tex:321–337. The pair has its common removed neighbor x in insert x Y. Lipschitz depth gives distance to the original S(G) at least b_G(x)−3; convert finite ENat depth before the natural subtraction. -/
def RemovedPairResponseStatement : Prop :=
  ∀ A θ : ℝ, ResponseProperty A θ →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane, RemovalStep G Y x →
    ∀ z ∈ survivors G Y x, ∀ w ∈ survivors G Y x, z ≠ w →
    |partMean true G (insert x Y) τ (fun n => dot (n z) (n w)) -
      partMean false G (insert x Y) τ (fun n => dot (n z) (n w))| ≤
      A * θ ^ depthShift G x

/-- `l:removal`, sec5-window.tex:341–350. Expand pairSum over ordered unequal pairs and divide by two. There are at most six unordered pairs for k=4 and at most three for k≤3. -/
def PairDifferenceStatement : Prop :=
  ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ _x : Plane,
    ∀ V : Finset Plane, V.card ≤ 4 → ∀ d : ℝ, 0 ≤ d →
    (∀ z ∈ V, ∀ w ∈ V, z ≠ w →
      |partMean true G Y τ (fun n => dot (n z) (n w)) -
        partMean false G Y τ (fun n => dot (n z) (n w))| ≤ d) →
    |partMean true G Y τ (pairSum V) - partMean false G Y τ (pairSum V)| ≤
      (if V.card = 4 then 6 else 3) * d

/-- `l:removal`, sec5-window.tex:339–340. Apply the mean value estimate for log on [1/2,∞), where its derivative is bounded by two. -/
def LogLipschitzStatement : Prop :=
  ∀ a b : ℝ, (1 / 2 : ℝ) ≤ a → (1 / 2 : ℝ) ≤ b →
    |Real.log a - Real.log b| ≤ 2 * |a - b|

theorem logLipschitz : LogLipschitzStatement := by
  have ordered : ∀ a b : ℝ, (1 / 2 : ℝ) ≤ a → (1 / 2 : ℝ) ≤ b → b ≤ a →
      |Real.log a - Real.log b| ≤ 2 * |a - b| := by
    intro a b ha hb hba
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hlog : Real.log a - Real.log b ≤ (a - b) / b := by
      rw [← Real.log_div ha0.ne' hb0.ne']
      convert Real.log_le_sub_one_of_pos (div_pos ha0 hb0) using 1
      field_simp
    have hdiv : (a - b) / b ≤ 2 * (a - b) := by
      apply (div_le_iff₀ hb0).mpr
      nlinarith
    simpa only [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb0 hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)] using hlog.trans hdiv
  intro a b ha hb
  rcases le_total b a with h | h
  · exact ordered a b ha hb h
  · simpa only [abs_sub_comm] using ordered b a hb ha h

#print axioms logLipschitz

/-- `e:removaltelescope`, sec5-window.tex:276–285. Divide the two integration identities by their positive after-removal partition sums and expand log of the pinned/free ratio. -/
def LogStepIdentityStatement : Prop :=
  ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane,
    (∀ pinned : Bool, 0 < partSum pinned G Y τ (fun _ => 1) ∧
      0 < partSum pinned G (insert x Y) τ (fun _ => 1)) →
    (∀ pinned : Bool, partSum pinned G Y τ (fun _ => 1) =
      partSum pinned G (insert x Y) τ (removalPolynomial x (survivors G Y x))) →
    logRatio G Y τ - logRatio G (insert x Y) τ =
      Real.log (partMean true G (insert x Y) τ (removalPolynomial x (survivors G Y x))) -
      Real.log (partMean false G (insert x Y) τ (removalPolynomial x (survivors G Y x)))

/-- `l:removal`, sec5-window.tex:339–350. Use linearity of partMean, the pair difference, the quartic bound, and the supplied log Lipschitz estimate. The seed costs at most 4d+4/5≤1+4d; a nonseed costs at most 2d. -/
def LocalLogEstimateStatement : Prop :=
  (∀ a b : ℝ, (1 / 2 : ℝ) ≤ a → (1 / 2 : ℝ) ≤ b →
      |Real.log a - Real.log b| ≤ 2 * |a - b|) →
    ∀ G Y : Finset Plane, ∀ τ : PinAssignment G, ∀ x : Plane,
    ∀ V : Finset Plane, V.card ≤ 4 → ∀ d : ℝ, 0 ≤ d →
    (∀ pinned : Bool, 0 < partSum pinned G Y τ (fun _ => 1) ∧
      (1 / 2 : ℝ) ≤ partMean pinned G Y τ (removalPolynomial x V) ∧
      |partMean pinned G Y τ (quartic x)| ≤ 3) →
    |partMean true G Y τ (pairSum V) - partMean false G Y τ (pairSum V)| ≤
      (if V.card = 4 then 6 else 3) * d →
    |Real.log (partMean true G Y τ (removalPolynomial x V)) -
      Real.log (partMean false G Y τ (removalPolynomial x V))| ≤
      if V.card = 4 then 1 + 4 * d else 2 * d

/-- `e:removaltelescope`, sec5-window.tex:280–285,352–356. Telescope the original-volume logRatio over all prefixes, bound the absolute sum, and isolate index zero. Enumeration injectivity gives the one-seed convention also for a singleton cut. -/
def RemovalTelescopeStatement : Prop :=
  ∀ G X : Finset Plane, ∀ τ : PinAssignment G, ∀ e : RemovalEnumeration X,
    removedPrefix e 0 = ∅ → removedPrefix e (e.last + 1) = X →
    ∀ A θ : ℝ,
    (∀ j : Fin (e.last + 1),
      |logRatio G (removedPrefix e j.val) τ - logRatio G (removedPrefix e (j.val + 1)) τ| ≤
      if j.val = 0 then 1 + 4 * A * θ ^ depthShift G (e.site j)
      else 2 * A * θ ^ depthShift G (e.site j)) →
    |cutError G X τ| ≤ 1 + 4 * A * θ ^ depthShift G (e.site 0) +
      2 * A * ∑ j : Fin e.last, θ ^ depthShift G (e.site j.succ)

/-- `t:cutMOS`, sec5-window.tex:746–752. Bound the seed decay by one. Use b≥3 before converting θ^(b−3)=θ^(-3)θ^b and enlarge the nonseed sum to all X. -/
def RemovalCostSumStatement : Prop :=
  ∀ G X : Finset Plane, ∀ τ : PinAssignment G, ∀ e : RemovalEnumeration X,
    (∀ x ∈ X, 3 ≤ boundaryDepth G x) → ∀ A θ : ℝ, 0 ≤ A → 0 < θ → θ < 1 →
    |cutError G X τ| ≤ 1 + 4 * A * θ ^ depthShift G (e.site 0) +
      2 * A * ∑ j : Fin e.last, θ ^ depthShift G (e.site j.succ) →
    |cutError G X τ| ≤ 1 + 4 * A +
      2 * A * θ ^ (-3 : ℤ) * ∑ z ∈ X, decay θ (boundaryDepth G z)

end AKLT.Blueprint.Win
