# Exported declarations

All declarations below are in `AKLT.W.H3C056`. The statements are copied from the delivered sources. Private translation helpers are omitted.

## [Coefficients.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Coefficients.lean)

```lean
theorem all_compass (p : Compass → Prop) :
    (∀ d, p d) ↔ p .east ∧ p .north ∧ p .west ∧ p .south
```

```lean
theorem dead_region_exists (x : Plane) : ∃ j : Fin 5, deadRegion j.val x
```

```lean
theorem dead_region_unique (x : Plane) (j k : Fin 5)
    (hj : deadRegion j.val x) (hk : deadRegion k.val x) : j=k
```

```lean
theorem reward_region (x : Plane) (incoming outgoing : Compass) (j : Fin 5)
    (hj : deadRegion j.val x) :
    relaxedReward x incoming outgoing {kernelCentre} =
      relaxedReward (0,0) incoming outgoing
        (if j.val<4 then {(direction j.val).step} else ∅)
```

```lean
theorem quotient_nonrevisit {m q : Nat} (Q : MemoryQuotient m q) (hQ : Q.Correct)
    (a : Fin q) (d : Compass) (ha : Q.allowed a d = true) (hk : Q.kind a d ≠ .revisit) :
    d ≠ (Q.arrival a).reverse ∧
      Q.kind a d = if d=Q.arrival a then .straight else .turn
```

```lean
theorem known_bond (x : Plane) (d₀ d : Compass)
    (hx : x=kernelStart ∨ x=kernelStart+d₀.step) :
    ({x,x+d.step} : Finset Plane) = {kernelStart,kernelStart+d₀.step} ↔
      (x=kernelStart ∧ d=d₀) ∨ (x=kernelStart+d₀.step ∧ d=d₀.reverse)
```

```lean
theorem phase_sum_shape (k : StepKind) (r : ℚ) (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (phaseTransition k r φ ψ)*v ψ) =
      diagonal φ k*v φ +
        (if φ=.A ∧ k=.turn then coefficientCeiling (passageFactor false*r/3)*v .C else
         if φ=.B ∧ k=.straight then coefficientCeiling (passageFactor true*r/3)*v .D else 0)
```

```lean
theorem phase_row (k : StepKind) (incoming outgoing : Compass) (x : Plane)
    (j : Fin 5) (hj : deadRegion j.val x) (φ : Phase) (v : Phase → Nat)
    (hs : k=.straight → outgoing=incoming) (ht : k=.turn → outgoing≠incoming)
    (hr : k≠.revisit → outgoing≠incoming.reverse) :
    (∑ ψ : Phase, coefficientCeiling
      (phaseTransition k (relaxedReward x incoming outgoing {kernelCentre}) φ ψ)*v ψ) =
      diagonal φ k*v φ +
        (if (φ=.A ∧ k=.turn) ∨ (φ=.B ∧ k=.straight) then
          response (directionCode incoming) (directionCode outgoing) j.val *
            v (if k=.turn then .C else .D) else 0)
```

## [Geometry.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Geometry.lean)

```lean
theorem mem_box (x : Plane) : x ∈ square (0,0) certificateRadius ↔
    (-70 ≤ x.1 ∧ x.1 ≤ 70) ∧ (-70 ≤ x.2 ∧ x.2 ≤ 70)
```

```lean
theorem index_grid (s : Nat) : siteIndex (gridSite s) = s
```

```lean
theorem grid_index (x : Plane) (hx : x ∈ square (0,0) certificateRadius) :
    gridSite (siteIndex x) = x
```

```lean
theorem grid_eq (s : Nat) (x : Plane) (hx : x ∈ square (0,0) certificateRadius) :
    gridSite s = x ↔ s = siteIndex x
```

```lean
theorem step_box (s : Nat) (hs : s < 19881) (d : Compass) :
    gridSite s+d.step ∈ square (0,0) certificateRadius ↔ ¬boundary d s
```

```lean
theorem index_step (s : Nat) (hs : s < 19881) (d : Compass) (h : ¬boundary d s) :
    siteIndex (gridSite s+d.step) = match d with
      | .east => s+141 | .north => s+1 | .west => s-141 | .south => s-1
```

## [Main.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Main.lean)

```lean
def RowTermsAgreementV2 : Prop
```

```lean
theorem rowTerms_v2 : RowTermsAgreementV2
```

```lean
theorem legacy_transfer (hV2 : RowTermsAgreementV2) :
    AKLT.Cert.H3.RowTermsAgreement
```

```lean
theorem main : AKLT.Cert.H3.RowTermsAgreement
```

## [Masks.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Masks.lean)

```lean
theorem packFn_sub (b n : Nat) (f g : Nat → Nat)
    (h : ∀ s < n, g s ≤ f s) :
    packFn b n (fun s => f s - g s) = packFn b n f - packFn b n g
```

```lean
theorem lane_sub {P Q b n : Nat} (hP : Fits P b n) (hQ : Fits Q b n)
    (h : ∀ s < n, lane Q b s ≤ lane P b s) (s : Nat) (hs : s < n) :
    lane (P-Q) b s = lane P b s - lane Q b s
```

```lean
def Mask (M : Nat) (p : Nat → Prop) : Prop
```

```lean
theorem mask_congr {M : Nat} {p q : Nat → Prop} (h : Mask M p)
    (hpq : ∀ s < 19881, p s ↔ q s) : Mask M q
```

```lean
theorem mask_sub {P Q : Nat} {p q : Nat → Prop} (hP : Mask P p) (hQ : Mask Q q)
    (h : ∀ s < 19881, q s → p s) : Mask (P-Q) (fun s => p s ∧ ¬q s)
```

```lean
theorem mask_add {P Q : Nat} {p q : Nat → Prop} (hP : Mask P p) (hQ : Mask Q q)
    (h : ∀ s < 19881, ¬(p s ∧ q s)) : Mask (P+Q) (fun s => p s ∨ q s)
```

```lean
theorem mask_zero : Mask 0 (fun _ => False)
```

```lean
theorem lane_lowMask (b s : Nat) (hb : 0 < b) :
    lane (2^b-1) b s = if s = 0 then 2^b-1 else 0
```

```lean
theorem mask_all : Mask allMask (fun _ => True)
```

```lean
theorem mask_one (t : Nat) (ht : t < 19881) : Mask (oneMask t) (fun s => s = t)
```

```lean
theorem lane_nested (P b w r c : Nat) (hc : c < w) :
    lane (lane P (b*w) r) b c = lane P b (r*w+c)
```

```lean
theorem mask_firstColumn : Mask firstColumn (fun s => s%141=0)
```

```lean
theorem mask_firstRow : Mask firstRow (fun s => s < 141)
```

```lean
theorem fits_shorten {P b n k : Nat} (hP : Fits P b n) (hk : k ≤ n) (hb : 0 < b)
    (hzero : ∀ s < n, k ≤ s → lane P b s = 0) : Fits P b k
```

```lean
theorem fits_shiftLeft {P b n : Nat} (hP : Fits P b n) (k : Nat) :
    Fits (P <<< (b*k)) b (n+k)
```

```lean
theorem mask_lastColumn : Mask lastColumn (fun s => s%141=140)
```

```lean
theorem mask_lastRow : Mask lastRow (fun s => s/141=140)
```

```lean
def boundary (d : Compass) (s : Nat) : Prop
```

```lean
theorem mask_boundary (d : Compass) : Mask (boundaryMask d) (boundary d)
```

## [Pull.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Pull.lean)

```lean
theorem lane_masked (P : Nat) {M : Nat} {p : Nat → Prop} (hM : Mask M p)
    (s : Nat) (hs : s < 19881) :
    lane (Nat.land P M) 80 s = if p s then lane P 80 s else 0
```

```lean
def shiftedPlane (P : Nat) (d : Compass) : Nat
```

```lean
theorem pull_lane_raw (P Z : Nat) (d : Compass) (hZ : Z < 2^26)
    (s : Nat) (hs : s < 19881) :
    lane (pull P Z d) 80 s =
      if boundary d s then Z else lane (shiftedPlane P d) 80 s
```

```lean
theorem pull_lane (P Z : Nat) (d : Compass) (hZ : Z < 2^26)
    (s : Nat) (hs : s < 19881) :
    lane (pull P Z d) 80 s =
      if gridSite s+d.step ∈ square (0,0) certificateRadius
      then lane P 80 (siteIndex (gridSite s+d.step)) else Z
```

## [RewardTranslation.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/RewardTranslation.lean)

```lean
theorem reward_translate (x t : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    relaxedReward (x + t) incoming outgoing (dead.image (tr t)) =
      relaxedReward x incoming outgoing dead
```

```lean
theorem reward_shift_singleton (x : Plane) (incoming outgoing : Compass) :
    relaxedReward x incoming outgoing {kernelCentre} =
      relaxedReward (0,0) incoming outgoing {kernelCentre-x}
```

```lean
theorem reward_shift_empty (x : Plane) (incoming outgoing : Compass) :
    relaxedReward x incoming outgoing ∅ = relaxedReward (0,0) incoming outgoing ∅
```

```lean
theorem reward_erase_irrelevant (x z : Plane) (incoming outgoing : Compass)
    (hz : z ∉ neighbours x) :
    relaxedReward x incoming outgoing {z} = relaxedReward x incoming outgoing ∅
```

## [Row.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Row.lean)

```lean
def edgeTerms {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (d : Compass) : List PackedTerm
```

```lean
def ordinaryRegion (X : PairType) (d₀ : Compass) (x : Plane) : Prop
```

```lean
def knownRegion (d₀ d : Compass) (x : Plane) : Prop
```

```lean
def valueAt {q : Nat} (plane cap : Phase → Fin q → Nat) (a : Fin q)
    (x : Plane) (d : Compass) (ψ : Phase) : Nat
```

```lean
theorem component_edges {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (s : Nat) :
    component 80 s (rowTerms Q plane cap X d₀ φ a) =
      ∑ d : Compass, component 80 s (edgeTerms Q plane cap X d₀ φ a d)
```

```lean
theorem component_edge {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (d : Compass) (s : Nat)
    (hs : s<19881) (hd₀ : d₀≠.east) (hcap : ∀ ψ b, cap ψ b<2^26) :
    component 80 s (edgeTerms Q plane cap X d₀ φ a d) =
      if Q.allowed a d then
        diagonal φ (Q.kind a d) *
          (if ordinaryRegion X d₀ (gridSite s) then
            valueAt plane cap (Q.successor a d) (gridSite s) d φ else 0) +
        (if Q.kind a d=.revisit then 0 else q5 *
          (if knownRegion d₀ d (gridSite s) then
            valueAt plane cap (Q.successor a d) (gridSite s) d φ else 0)) +
        (if (φ=.A ∧ Q.kind a d=.turn) ∨ (φ=.B ∧ Q.kind a d=.straight) then
          ((List.range 5).map fun j =>
            response (directionCode (Q.arrival a)) (directionCode d) j *
              (if deadRegion j (gridSite s) then
                (if ordinaryRegion X d₀ (gridSite s) then
                  valueAt plane cap (Q.successor a d) (gridSite s) d
                    (if Q.kind a d=.turn then .C else .D) else 0) else 0)).sum else 0)
      else 0
```

## [Semantic.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Semantic.lean)

```lean
theorem list_sum_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
```

```lean
theorem response_sum (x : Plane) (incoming outgoing : Compass) (j : Fin 5)
    (hj : deadRegion j.val x) (v : Nat) :
    ((List.range 5).map fun k => response (directionCode incoming) (directionCode outgoing) k *
      (if deadRegion k x then v else 0)).sum =
      response (directionCode incoming) (directionCode outgoing) j.val*v
```

```lean
theorem known_block (x : Plane) (d₀ d : Compass)
    (hx : x=kernelStart ∨ x=kernelStart+d₀.step) :
    ({x,x+d.step} : Finset Plane) = {kernelStart,kernelStart+d₀.step} ↔
      ¬knownRegion d₀ d x
```

```lean
theorem fifth_sum (φ : Phase) (v : Phase → Nat) :
    (∑ ψ : Phase, coefficientCeiling (if φ=ψ then (1:ℚ)/5 else 0)*v ψ) = q5*v φ
```

```lean
theorem edge_agreement {m q : Nat} (Q : MemoryQuotient m q)
    (plane cap : Phase → Fin q → Nat) (X : PairType) (d₀ : Compass)
    (φ : Phase) (a : Fin q) (d : Compass) (hQ : Q.Correct) (hd₀ : d₀≠.east)
    (hdata : ∀ ψ b, cap ψ b<2^26 ∧ Fits (plane ψ b) 80 19881 ∧
      lane (plane ψ b) 80 (siteIndex kernelCentre)=0)
    (s : Nat) (hs : s<19881) (hc : gridSite s≠kernelCentre)
    (htarget : gridSite s≠kernelTarget X) :
    component 80 s (edgeTerms Q plane cap X d₀ φ a d) =
      ∑ ψ : Phase, coefficientCeiling
        (stationaryCoefficientV2 Q X d₀ φ a (gridSite s) d ψ) *
          valueAt plane cap (Q.successor a d) (gridSite s) d ψ
```

## [Spatial.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Spatial.lean)

```lean
theorem mask_four (t₀ t₁ t₂ t₃ : Nat)
    (h₀ : t₀ < 19881) (h₁ : t₁ < 19881) (h₂ : t₂ < 19881) (h₃ : t₃ < 19881)
    (h01 : t₀ ≠ t₁) (h02 : t₀ ≠ t₂) (h03 : t₀ ≠ t₃)
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) :
    Mask (allMask-oneMask t₀-oneMask t₁-oneMask t₂-oneMask t₃)
      (fun s => s ≠ t₀ ∧ s ≠ t₁ ∧ s ≠ t₂ ∧ s ≠ t₃)
```

```lean
theorem centre_mem : kernelCentre ∈ square (0,0) certificateRadius
```

```lean
theorem start_mem : kernelStart ∈ square (0,0) certificateRadius
```

```lean
theorem target_mem (X : PairType) : kernelTarget X ∈ square (0,0) certificateRadius
```

```lean
theorem next_mem (d : Compass) : kernelStart+d.step ∈ square (0,0) certificateRadius
```

```lean
theorem neg_step_mem (d : Compass) : -d.step ∈ square (0,0) certificateRadius
```

```lean
theorem case_ne_east (X : PairType) (d₀ : Compass) (h : (X,d₀) ∈ stationaryCases) :
    d₀ ≠ .east
```

```lean
theorem mask_ordinary (X : PairType) (d₀ : Compass) (hd : d₀ ≠ .east) :
    Mask (ordinaryMask X d₀) (fun s =>
      gridSite s ≠ kernelCentre ∧ gridSite s ≠ kernelTarget X ∧
      gridSite s ≠ kernelStart ∧ gridSite s ≠ kernelStart+d₀.step)
```

```lean
theorem mask_known (d₀ d : Compass) (hd : d₀ ≠ .east) :
    Mask (knownMask d₀ d) (fun s =>
      (gridSite s=kernelStart ∧ d ≠ d₀) ∨
      (gridSite s=kernelStart+d₀.step ∧ d ≠ d₀.reverse))
```

```lean
def deadRegion (j : Nat) (x : Plane) : Prop
```

```lean
theorem mask_centreNeighbour (j : Nat) :
    Mask (centreNeighbourMask j) (fun s => gridSite s = -(direction j).step)
```

```lean
theorem mask_centreNeighbours : Mask centreNeighbourMasks
    (fun s => ∃ d : Compass, gridSite s = -d.step)
```

```lean
theorem mask_dead (j : Nat) : Mask (deadMask j) (fun s => deadRegion j (gridSite s))
```

## [Table.lean](/home/ubuntu/aklt/wt/LW_H3C056/AKLT/W/H3C056/Table.lean)

```lean
theorem powerset_two_singleton {α : Type*} (a : α) :
    Finset.powersetCard 2 {a} = ∅
```

```lean
theorem powerset_two_empty {α : Type*} : Finset.powersetCard 2 (∅ : Finset α) = ∅
```

```lean
theorem powerset_two_pair {α : Type*} [DecidableEq α] (a b : α) (h : a ≠ b) :
    Finset.powersetCard 2 {a,b} = {{a,b}}
```

```lean
theorem diagonal_ceiling (φ : Phase) (k : StepKind) :
    coefficientCeiling (phaseDiagonal φ k) = diagonal φ k
```

```lean
@[simp] theorem ceiling_zero : coefficientCeiling 0 = 0
```

```lean
theorem ceiling_fifth : coefficientCeiling ((1:ℚ)/5) = q5
```

```lean
theorem response_ceiling (incoming outgoing : Compass) (j : Fin 5)
    (h : outgoing ≠ incoming.reverse) :
    coefficientCeiling (passageFactor (decide (outgoing=incoming)) *
      relaxedReward (0,0) incoming outgoing
        (if j.val<4 then {(direction j.val).step} else ∅) / 3) =
      response (directionCode incoming) (directionCode outgoing) j.val
```
