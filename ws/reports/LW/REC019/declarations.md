All declarations below are in namespace `AKLT.W.REC019`. Public theorem statements omit their proved bodies; public definitions include their transparent bodies.

## Conditioning.lean

```lean
theorem finite_weighted_bounds {Ω : Type*} [Fintype Ω] (w F : Ω → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) {l u : ℝ} (hl : l ≤ 0) (hu : 0 ≤ u)
    (hF : ∀ σ, l ≤ F σ ∧ F σ ≤ u) :
    l ≤ (∑ σ, w σ * F σ) / (∑ σ, w σ) ∧
      (∑ σ, w σ * F σ) / (∑ σ, w σ) ≤ u
```

```lean
def mixturePair {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (m : Ω → Fin 3 → Vec3) (i j : Fin 3) : ℝ :=
  (∑ σ, w σ * dot (m σ i) (m σ j)) / (∑ σ, w σ)
```

```lean
theorem mixture_pair_bounds {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (m : Ω → Fin 3 → Vec3) (hw : ∀ σ, 0 ≤ w σ)
    (hm : ∀ σ i, normSq (m σ i) ≤ 9 / 25) (i j : Fin 3) :
    -(9 / 25 : ℝ) ≤ mixturePair w m i j ∧ mixturePair w m i j ≤ 9 / 25
```

```lean
theorem mixture_triple_lower {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (m : Ω → Fin 3 → Vec3) (hw : ∀ σ, 0 ≤ w σ)
    (hm : ∀ σ i, normSq (m σ i) ≤ 9 / 25) :
    -(27 / 50 : ℝ) ≤ mixturePair w m 0 1 + mixturePair w m 0 2 + mixturePair w m 1 2
```

## DepartureGeometry.lean

```lean
theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z
```

```lean
theorem adjacent_symmetric {x y : Plane} (h : Adjacent x y) : Adjacent y x
```

```lean
theorem adjacent_of_mem_neighbours {x y : Plane} (h : y ∈ neighbours x) :
    Adjacent x y
```

```lean
theorem neighbours_nonadjacent {x f g : Plane}
    (hf : f ∈ neighbours x) (hg : g ∈ neighbours x) : ¬ Adjacent f g
```

```lean
theorem interior_distance {G : Finset Plane} {y : Plane}
    (hy : y ∈ G) (hi : y ∉ protectedSites G) {z : Plane} (hz : z ∉ G) :
    2 < latticeDist y z
```

```lean
theorem departure_neighbour_no_leg (a : Departure) {x : Plane}
    (hx : x ∈ a.D.presentNeighbours a.y) :
    ∀ e ∈ originalLegs a.G, e.1 ≠ x
```

```lean
theorem remove_presentNeighbours {G : Finset Plane} (D : Network G)
    (y x : Plane) (hxy : x ≠ y) :
    (removeSite D y).presentNeighbours x = (D.presentNeighbours x).erase y
```

```lean
theorem present_symmetric {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x
```

```lean
theorem departure_neighbour_removed_degree (a : Departure) {x : Plane}
    (hx : x ∈ a.D.presentNeighbours a.y) :
    ((removeSite a.D a.y).presentNeighbours x).card ≤ 3
```

## FreePositive.lean

```lean
theorem ico_monomial_nonnegative (m : Fin 3 → ℕ) :
    0 ≤ ∑ j : IcoLetter, ∏ i : Fin 3, icoVector j i ^ m i
```

```lean
theorem site_monomial_nonnegative (s : Status) (m : Fin 3 → ℕ) :
    0 ≤ siteFunctional s (fun n => ∏ i, n i ^ m i)
```

```lean
theorem product_polynomial_nonnegative {ι : Type*} [Fintype ι]
    (s : ι → Status) (p : MvPolynomial (ι × Fin 3) ℕ) :
    0 ≤ productFunctional s (fun a =>
      MvPolynomial.eval₂ (Nat.castRingHom ℝ) (fun v => a v.1 v.2) p)
```

```lean
theorem free_partition_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) : 0 ≤ D.partition τ false (fun _ => 1)
```

```lean
theorem free_pair_partition_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (x y : Plane) :
    0 ≤ D.partition τ false (fun n => dot (n x) (n y))
```

```lean
theorem free_removedPairMean_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y f g : Plane) : 0 ≤ removedPairMean D τ false y f g
```

## LocalBound.lean

```lean
def tripleMeanU (a b c : Vec3) : Vec3 :=
  fun i => moment (fun n => n i * threeProduct a b c n) / moment (threeProduct a b c)
```

```lean
theorem three_unit_mean_bound {a b c : Vec3}
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1) :
    1 / 2 ≤ moment (threeProduct a b c) ∧ normSq (tripleMeanU a b c) ≤ 9 / 25
```

```lean
theorem zero_field_mean_bound {b c : Vec3} (hb : normSq b ≤ 1) (hc : normSq c ≤ 1) :
    1 / 2 ≤ moment (threeProduct 0 b c) ∧ normSq (tripleMeanU 0 b c) ≤ 9 / 25
```

```lean
theorem three_spin_mean_bound (a b c : SpinLetter) :
    1 / 2 ≤ moment (threeProduct (spinVector a) (spinVector b) (spinVector c)) ∧
      normSq (tripleMeanU (spinVector a) (spinVector b) (spinVector c)) ≤ 9 / 25
```

```lean
def tripleMean (s : Status) (a b c : Vec3) : Vec3 :=
  fun i => siteFunctional s (fun n => n i * threeProduct a b c n) /
    siteFunctional s (threeProduct a b c)
```

```lean
theorem three_spin_local_bound (s : Status) (hs : s = .U ∨ s = .D)
    (a b c : SpinLetter) :
    0 < siteFunctional s (threeProduct (spinVector a) (spinVector b) (spinVector c)) ∧
      normSq (tripleMean s (spinVector a) (spinVector b) (spinVector c)) ≤ 9 / 25
```

## LogMean.lean

```lean
theorem logMean_integral {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logarithmicMean x y = ∫ t : ℝ in 0..1,
      Real.exp (t * Real.log x + (1 - t) * Real.log y)
```

```lean
theorem logMean_positive {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < logarithmicMean x y
```

```lean
theorem logMean_monotone {x x' y y' : ℝ}
    (hx : 0 < x) (hxx : x ≤ x') (hy : 0 < y) (hyy : y ≤ y') :
    logarithmicMean x y ≤ logarithmicMean x' y'
```

```lean
theorem logMean_le_upper {x y u : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxu : x ≤ u) (hyu : y ≤ u) : logarithmicMean x y ≤ u
```

```lean
theorem lower_le_logMean {x y l : ℝ} (hl : 0 < l) (hlx : l ≤ x) (hly : l ≤ y) :
    l ≤ logarithmicMean x y
```

```lean
theorem reciprocal_logMean_41_50 :
    1 / (3 * logarithmicMean (41 / 50) 1) ≤ (367502 / 1000000 : ℝ)
```

## Main.lean

```lean
def Residual_TripleLower : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    -(27 / 50 : ℝ) ≤
      removedPairMean a.D a.τ true a.y f g + removedPairMean a.D a.τ true a.y f a.o +
        removedPairMean a.D a.τ true a.y g a.o
```

```lean
def Residual_PairUpper : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    ∀ b : Bool, removedPairMean a.D a.τ b a.y f g ≤ 9 / 25
```

```lean
def Residual_ConditionalMixture : Prop :=
  ∀ a : Departure, a.D.status a.y = .U → ∀ f g : Plane,
    a.D.presentNeighbours a.y = {a.o, f, g} → a.o ≠ f → a.o ≠ g → f ≠ g →
    ∀ b : Bool, ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ m : Fin n → Fin 3 → Vec3,
      (∀ σ, 0 ≤ w σ) ∧ (∀ σ i, normSq (m σ i) ≤ 9 / 25) ∧
      removedPairMean a.D a.τ b a.y f g = mixturePair w m 0 1 ∧
      removedPairMean a.D a.τ b a.y f a.o = mixturePair w m 0 2 ∧
      removedPairMean a.D a.τ b a.y g a.o = mixturePair w m 1 2
```

```lean
theorem residuals_of_conditional_mixture (h : Residual_ConditionalMixture) :
    Residual_TripleLower ∧ Residual_PairUpper
```

```lean
theorem alpha_bound_of_intervals {Iτ I₀ Jτ J₀ : ℝ}
    (hIτ : 41 / 50 ≤ Iτ) (hI₀ : 1 ≤ I₀)
    (hJτp : 0 < Jτ) (hJ₀p : 0 < J₀)
    (hJτ' : Jτ ≤ 134 / 125) (hJ₀' : J₀ ≤ 134 / 125) :
    1 / (3 * logarithmicMean Iτ I₀) - 1 / (5 * logarithmicMean Jτ J₀) ≤
      (18094 / 100000 : ℝ)
```

```lean
theorem main_of_residuals (hT : Residual_TripleLower) (hP : Residual_PairUpper) :
    AKLT.Blueprint.Rec.AlphaUniformStatement
```

```lean
theorem main_of_conditional_mixture (h : Residual_ConditionalMixture) :
    AKLT.Blueprint.Rec.AlphaUniformStatement
```

## NetworkBounds.lean

```lean
theorem network_spins_ball {G : Finset Plane} (D : Network G)
    (σ : D.active → SpinLetter) (x : Plane) : normSq (D.spins σ x) ≤ 1
```

```lean
def networkWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (σ : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (σ x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins σ e.val.1) else 1
```

```lean
theorem partition_as_weight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ σ : D.active → SpinLetter, networkWeight D τ b σ * f (D.spins σ)
```

```lean
theorem networkWeight_nonnegative {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (σ : D.active → SpinLetter) : 0 ≤ networkWeight D τ b σ
```

```lean
theorem network_partition_nonnegative {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1)
```

```lean
theorem network_pair_expectation_bounds {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (x y : Plane) :
    -1 ≤ D.expectation τ b (fun n => dot (n x) (n y)) ∧
      D.expectation τ b (fun n => dot (n x) (n y)) ≤ 1
```

```lean
theorem responseJ_positive {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (y f g : Plane) : 0 < responseJ D τ b y f g
```

## SiteMoments.lean

```lean
theorem moment_constant : moment (fun _ => 1) = 1
```

```lean
theorem moment_first (i : Fin 3) : moment (fun n => n i) = 0
```

```lean
theorem moment_second (i j : Fin 3) :
    moment (fun n => n i * n j) = if i = j then 1 / 3 else 0
```

```lean
theorem moment_third (i j k : Fin 3) : moment (fun n => n i * n j * n k) = 0
```

```lean
theorem moment_fourth (i j k l : Fin 3) :
    moment (fun n => n i * n j * n k * n l) =
      ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) / 15
```

```lean
theorem site_U_eq_moment (f : Vec3 → ℝ) : siteFunctional .U f = moment f
```

```lean
theorem site_D_eq_moment (f : Vec3 → ℝ) :
    siteFunctional .D f = (2 / 5 : ℝ) * f 0 + (3 / 5 : ℝ) * moment f
```

## SpinGeometry.lean

```lean
theorem goldenRatio_positive : 0 < goldenRatio
```

```lean
theorem goldenRatio_square : goldenRatio ^ 2 = goldenRatio + 1
```

```lean
theorem icoRadius_positive : 0 < icoRadius
```

```lean
theorem icoRadius_square : icoRadius ^ 2 = goldenRatio + 2
```

```lean
theorem icoVector_unit (j : IcoLetter) : normSq (icoVector j) = 1
```

```lean
theorem spinVector_ball (j : SpinLetter) : normSq (spinVector j) ≤ 1
```

```lean
theorem normSq_nonnegative (a : Vec3) : 0 ≤ normSq a
```

```lean
theorem dot_square_le (a b : Vec3) : dot a b ^ 2 ≤ normSq a * normSq b
```

```lean
theorem dot_ball_bounds {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    -1 ≤ dot a b ∧ dot a b ≤ 1
```

```lean
theorem spinWeight_nonnegative (s : Status) (j : SpinLetter) : 0 ≤ spinWeight s j
```

```lean
theorem sum_three_dot_lower {a b c : Vec3} (ha : normSq a ≤ 9 / 25)
    (hb : normSq b ≤ 9 / 25) (hc : normSq c ≤ 9 / 25) :
    -(27 / 50 : ℝ) ≤ dot a b + dot a c + dot b c
```

```lean
theorem dot_small_ball_bounds {a b : Vec3}
    (ha : normSq a ≤ 9 / 25) (hb : normSq b ≤ 9 / 25) :
    -(9 / 25 : ℝ) ≤ dot a b ∧ dot a b ≤ 9 / 25
```

## ThreeMean.lean

```lean
def threeProduct (a b c n : Vec3) : ℝ :=
  (1 + dot n a) * (1 + dot n b) * (1 + dot n c)
```

```lean
def tripleP (a b c : Vec3) : ℝ := dot a b + dot a c + dot b c
```

```lean
def tripleV (a b c : Vec3) : Vec3 :=
  fun i => 5 * (a i + b i + c i) + a i * dot b c + b i * dot a c + c i * dot a b
```

```lean
theorem moment_threeProduct (a b c : Vec3) :
    moment (threeProduct a b c) = 1 + tripleP a b c / 3
```

```lean
theorem moment_coord_threeProduct (a b c : Vec3) (i : Fin 3) :
    moment (fun n => n i * threeProduct a b c n) = tripleV a b c i / 15
```
