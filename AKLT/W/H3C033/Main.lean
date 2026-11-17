module
public import CertData.H3.Bridge.Interface
public import CertData.H3.Kernel.PrefixView

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option maxHeartbeats 500000

noncomputable section
open scoped BigOperators

namespace AKLT.W.H3C033

open AKLT.Defs
open AKLT.Cert.H3
open AKLT.Cert.H3.Production
open CertData.H3.Bridge

private theorem passageFactor_gt_one (b : Bool) : (1 : ℚ) < passageFactor b := by
  cases b <;> norm_num [passageFactor, localThreshold]

private theorem decide_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

private theorem scaledScore (K p k : ℚ) (hK : K ≠ 0) (hp : p ≠ 0) (hk : k ≠ 0) :
    (K * p - K) / (K * p * (K * k)) = ((p - 1) / (p * k)) / K := by
  field_simp [hK, hp, hk]
  <;> ring

private theorem item_time_lt {E : Exact} {n : Nat} {w : DirectionWord n}
    {s : PrefixState} (hr : PrefixRepresents E w s) {a : RewardItem}
    (ha : a ∈ s.items) : a.time < n := by
  rcases hr with ⟨_, _, _, htimes, _⟩
  have hm : a.time ∈ s.items.map RewardItem.time := List.mem_map.mpr ⟨a, ha, rfl⟩
  rw [htimes] at hm
  rcases List.mem_map.mp hm with ⟨i, hi, hval⟩
  have : a.time = i.val := hval.symm
  omega

private def itemIndex {n : Nat} (a : RewardItem) (h : a.time < n) : Fin n :=
  ⟨a.time, h⟩

private theorem itemIndex_mem {E : Exact} {n : Nat} {w : DirectionWord n}
    {s : PrefixState} (hr : PrefixRepresents E w s) {a : RewardItem}
    (ha : a ∈ s.items) : itemIndex a (item_time_lt hr ha) ∈ firstVisitList w := by
  have hbound := item_time_lt hr ha
  rcases hr with ⟨_, _, _, htimes, _⟩
  have hm : a.time ∈ s.items.map RewardItem.time := List.mem_map.mpr ⟨a, ha, rfl⟩
  rw [htimes] at hm
  rcases List.mem_map.mp hm with ⟨i, hi, hval⟩
  have hv : itemIndex a hbound = i := by
    apply Fin.ext
    exact hval.symm
  rw [hv]
  exact List.mem_reverse.mp hi

private theorem item_data {E : Exact} {n : Nat} {w : DirectionWord n}
    {s : PrefixState} (hr : PrefixRepresents E w s) {a : RewardItem}
    (ha : a ∈ s.items) :
    a.straight = wordStraight kernelIncoming w (itemIndex a (item_time_lt hr ha)) ∧
      (a.reward : ℚ) / E.denominator =
        witnessKappa w (itemIndex a (item_time_lt hr ha)) := by
  have hbound := item_time_lt hr ha
  rcases hr with ⟨_, _, _, _, hitems⟩
  rcases hitems a ha with ⟨i, htime, hstraight, hreward⟩
  have hi : i = itemIndex a hbound := by
    apply Fin.ext
    simpa [itemIndex] using htime
  rw [hi] at hstraight hreward
  exact ⟨hstraight, hreward⟩

private theorem exposureFactor_scaled {E : Exact} (hv : ExactValid E)
    {a : RewardItem} {b : Bool} (hstraight : a.straight = b) :
    (exposureFactor E a : ℚ) / E.denominator = passageFactor b := by
  rcases hv with ⟨hden, hs, ht, _, _, _⟩
  simp only [exposureFactor, hstraight]
  cases b with
  | false =>
      simp [exposureFactor]
      have hden' : (E.denominator : ℚ) ≠ 0 := by positivity
      calc
        (E.turn : ℚ) * 3 / E.denominator = (E.turn : ℚ) / E.denominator * 3 := by
          ring
        _ = (passageFactor false / 3) * 3 := by rw [ht]
        _ = passageFactor false := by ring
  | true =>
      simp [exposureFactor]
      have hden' : (E.denominator : ℚ) ≠ 0 := by positivity
      calc
        (E.straight : ℚ) * 3 / E.denominator = (E.straight : ℚ) / E.denominator * 3 := by
          ring
        _ = (passageFactor true / 3) * 3 := by rw [hs]
        _ = passageFactor true := by ring

private theorem itemLE_eq_shortOrder {E : Exact} {n : Nat} {w : DirectionWord n}
    {s : PrefixState} (hv : ExactValid E) (hr : PrefixRepresents E w s)
    {a b : RewardItem} (ha : a ∈ s.items) (hb : b ∈ s.items) :
    itemLE E a b = shortOrderLE w (itemIndex a (item_time_lt hr ha))
      (itemIndex b (item_time_lt hr hb)) := by
  let i := itemIndex a (item_time_lt hr ha)
  let j := itemIndex b (item_time_lt hr hb)
  have hda := item_data hr ha
  have hdb := item_data hr hb
  change a.straight = wordStraight kernelIncoming w i ∧
      (a.reward : ℚ) / E.denominator = witnessKappa w i at hda
  change b.straight = wordStraight kernelIncoming w j ∧
      (b.reward : ℚ) / E.denominator = witnessKappa w j at hdb
  have hfa := exposureFactor_scaled hv hda.1
  have hfb := exposureFactor_scaled hv hdb.1
  have hden : (0 : ℚ) < E.denominator := by exact_mod_cast hv.1
  have hki : witnessKappa w i = (a.reward : ℚ) / E.denominator := hda.2.symm
  have hkj : witnessKappa w j = (b.reward : ℚ) / E.denominator := hdb.2.symm
  have hki0 : (witnessKappa w i = 0) ↔ a.reward = 0 := by
    constructor
    · intro h
      have : (a.reward : ℚ) / E.denominator = 0 := by rw [← hki, h]
      have : (a.reward : ℚ) = 0 := (div_eq_zero_iff).mp this |>.resolve_right (ne_of_gt hden)
      exact_mod_cast this
    · intro h
      rw [hki]
      simp [h]
  have hkj0 : (witnessKappa w j = 0) ↔ b.reward = 0 := by
    constructor
    · intro h
      have : (b.reward : ℚ) / E.denominator = 0 := by rw [← hkj, h]
      have : (b.reward : ℚ) = 0 := (div_eq_zero_iff).mp this |>.resolve_right (ne_of_gt hden)
      exact_mod_cast this
    · intro h
      rw [hkj]
      simp [h]
  by_cases ha0 : a.reward = 0
  · by_cases hb0 : b.reward = 0
    · have hkiZ := hki0.mpr ha0
      have hkjZ := hkj0.mpr hb0
      have hkiAt : witnessKappa w (itemIndex a (item_time_lt hr ha)) = 0 := hkiZ
      have hkjAt : witnessKappa w (itemIndex b (item_time_lt hr hb)) = 0 := hkjZ
      simp [itemLE, shortOrderLE, ha0, hb0, hkiAt, hkjAt]
      change (a.time ≤ b.time ↔ a.time ≤ b.time)
      rfl
    · have hkiZ := hki0.mpr ha0
      have hkjNZ : witnessKappa w j ≠ 0 := fun h => hb0 (hkj0.mp h)
      have hkiAt : witnessKappa w (itemIndex a (item_time_lt hr ha)) = 0 := hkiZ
      have hkjAt : witnessKappa w (itemIndex b (item_time_lt hr hb)) ≠ 0 := hkjNZ
      simp [itemLE, shortOrderLE, ha0, hb0, hkiAt, hkjAt]
  · by_cases hb0 : b.reward = 0
    · have hkiNZ : witnessKappa w i ≠ 0 := fun h => ha0 (hki0.mp h)
      have hkjZ := hkj0.mpr hb0
      have hkiAt : witnessKappa w (itemIndex a (item_time_lt hr ha)) ≠ 0 := hkiNZ
      have hkjAt : witnessKappa w (itemIndex b (item_time_lt hr hb)) = 0 := hkjZ
      simp [itemLE, shortOrderLE, ha0, hb0, hkiAt, hkjAt]
    · have hki0' : witnessKappa w i ≠ 0 := fun h => ha0 (hki0.mp h)
      have hkj0' : witnessKappa w j ≠ 0 := fun h => hb0 (hkj0.mp h)
      let xa := exposureFactor E a
      let xb := exposureFactor E b
      let K := E.denominator
      let ra := a.reward
      let rb := b.reward
      have hxa : (xa : ℚ) / K = passageFactor (wordStraight kernelIncoming w i) := by
        simpa [xa, i] using hfa
      have hxb : (xb : ℚ) / K = passageFactor (wordStraight kernelIncoming w j) := by
        simpa [xb, j] using hfb
      have hra : (ra : ℚ) / K = witnessKappa w i := by simpa [ra, K] using hda.2
      have hrb : (rb : ℚ) / K = witnessKappa w j := by simpa [rb, K] using hdb.2
      have hxa_gt : K < xa := by
        have hp : (1 : ℚ) < (xa : ℚ) / K := by rw [hxa]; exact passageFactor_gt_one _
        have hq : (K : ℚ) < (xa : ℚ) := by
          have hq' := (lt_div_iff₀ hden).mp hp
          simpa [K] using hq'
        exact_mod_cast hq
      have hxb_gt : K < xb := by
        have hp : (1 : ℚ) < (xb : ℚ) / K := by rw [hxb]; exact passageFactor_gt_one _
        have hq : (K : ℚ) < (xb : ℚ) := by
          have hq' := (lt_div_iff₀ hden).mp hp
          simpa [K] using hq'
        exact_mod_cast hq
      have hra_pos : 0 < ra := Nat.pos_of_ne_zero ha0
      have hrb_pos : 0 < rb := Nat.pos_of_ne_zero hb0
      let crossA : ℚ := ((xa - K) * xb * rb : Nat)
      let crossB : ℚ := ((xb - K) * xa * ra : Nat)
      let scoreA : ℚ := ((xa - K : Nat) : ℚ) / ((xa : ℚ) * ra)
      let scoreB : ℚ := ((xb - K : Nat) : ℚ) / ((xb : ℚ) * rb)
      have hcastA : ((xa - K : Nat) : ℚ) = (xa : ℚ) - K := by
        rw [Nat.cast_sub (Nat.le_of_lt hxa_gt)]
      have hcastB : ((xb - K : Nat) : ℚ) = (xb : ℚ) - K := by
        rw [Nat.cast_sub (Nat.le_of_lt hxb_gt)]
      have hxa_repr : (xa : ℚ) = K * passageFactor (wordStraight kernelIncoming w i) :=
        by simpa [mul_comm] using (div_eq_iff (ne_of_gt hden)).mp hxa
      have hxb_repr : (xb : ℚ) = K * passageFactor (wordStraight kernelIncoming w j) :=
        by simpa [mul_comm] using (div_eq_iff (ne_of_gt hden)).mp hxb
      have hra_repr : (ra : ℚ) = K * witnessKappa w i :=
        by simpa [mul_comm] using (div_eq_iff (ne_of_gt hden)).mp hra
      have hrb_repr : (rb : ℚ) = K * witnessKappa w j :=
        by simpa [mul_comm] using (div_eq_iff (ne_of_gt hden)).mp hrb
      let shortA : ℚ :=
        (passageFactor (wordStraight kernelIncoming w i) - 1) /
          (passageFactor (wordStraight kernelIncoming w i) * witnessKappa w i)
      let shortB : ℚ :=
        (passageFactor (wordStraight kernelIncoming w j) - 1) /
          (passageFactor (wordStraight kernelIncoming w j) * witnessKappa w j)
      have hpfA : passageFactor (wordStraight kernelIncoming w i) ≠ 0 :=
        ne_of_gt (lt_trans (by norm_num) (passageFactor_gt_one _))
      have hpfB : passageFactor (wordStraight kernelIncoming w j) ≠ 0 :=
        ne_of_gt (lt_trans (by norm_num) (passageFactor_gt_one _))
      have hscoreA : scoreA = shortA / K := by
        dsimp [scoreA, shortA]
        rw [hcastA, hxa_repr, hra_repr]
        exact scaledScore K (passageFactor (wordStraight kernelIncoming w i))
          (witnessKappa w i) (ne_of_gt hden) hpfA hki0'
      have hscoreB : scoreB = shortB / K := by
        dsimp [scoreB, shortB]
        rw [hcastB, hxb_repr, hrb_repr]
        exact scaledScore K (passageFactor (wordStraight kernelIncoming w j))
          (witnessKappa w j) (ne_of_gt hden) hpfB hkj0'
      have hxa_pos : 0 < xa := Nat.zero_lt_of_lt hxa_gt
      have hxb_pos : 0 < xb := Nat.zero_lt_of_lt hxb_gt
      have hdenA : (0 : ℚ) < (xa : ℚ) * ra := mul_pos (by exact_mod_cast hxa_pos) (by exact_mod_cast hra_pos)
      have hdenB : (0 : ℚ) < (xb : ℚ) * rb := mul_pos (by exact_mod_cast hxb_pos) (by exact_mod_cast hrb_pos)
      have hlt : crossA < crossB ↔ scoreA < scoreB := by
        dsimp [crossA, crossB, scoreA, scoreB]
        rw [div_lt_div_iff₀ hdenA hdenB]
        constructor <;> intro h <;>
          simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
      have heq : crossA = crossB ↔ scoreA = scoreB := by
        dsimp [crossA, crossB, scoreA, scoreB]
        rw [div_eq_div_iff (ne_of_gt hdenA) (ne_of_gt hdenB)]
        constructor <;> intro h <;>
          simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
      have hcastLt :
          (((xa - K) * xb * rb : Nat) < ((xb - K) * xa * ra : Nat)) ↔ crossA < crossB := by
        exact_mod_cast (show (((xa - K) * xb * rb : Nat) : ℚ) <
            (((xb - K) * xa * ra : Nat) : ℚ) ↔ crossA < crossB by rfl)
      have hcastEq :
          (((xa - K) * xb * rb : Nat) = ((xb - K) * xa * ra : Nat)) ↔ crossA = crossB := by
        exact_mod_cast (show (((xa - K) * xb * rb : Nat) : ℚ) =
            (((xb - K) * xa * ra : Nat) : ℚ) ↔ crossA = crossB by rfl)
      have hdenScore : (0 : ℚ) < K := hden
      have hltK :
          shortA / K < shortB / K ↔ shortA < shortB := by
        constructor
        · intro h
          have hm := (div_lt_div_iff₀ hdenScore hdenScore).mp h
          exact lt_of_mul_lt_mul_right (by simpa [mul_assoc] using hm) hdenScore.le
        · intro h
          apply (div_lt_div_iff₀ hdenScore hdenScore).mpr
          exact mul_lt_mul_of_pos_right h hdenScore
      have heqK :
          shortA / K = shortB / K ↔ shortA = shortB := by
        rw [div_eq_div_iff (ne_of_gt hdenScore) (ne_of_gt hdenScore)]
        constructor <;> intro h
        · exact mul_right_cancel₀ (ne_of_gt hdenScore) (by simpa [mul_assoc] using h)
        · exact congrArg (fun x : ℚ => x * K) h
      have hival : i.val = a.time := rfl
      have hjval : j.val = b.time := rfl
      have hprop :
          (((xa - K) * xb * rb : Nat) < ((xb - K) * xa * ra : Nat) ∨
            (((xa - K) * xb * rb : Nat) = ((xb - K) * xa * ra : Nat) ∧ a.time ≤ b.time)) ↔
          (shortA < shortB ∨ (shortA = shortB ∧ i.val ≤ j.val)) := by
        constructor
        · intro h
          rcases h with hlt' | ⟨heq', htime⟩
          · left
            apply hltK.mp
            rw [← hscoreA, ← hscoreB]
            exact hlt.mp (hcastLt.mp hlt')
          · right
            constructor
            · apply heqK.mp
              rw [← hscoreA, ← hscoreB]
              exact heq.mp (hcastEq.mp heq')
            · simpa [hival, hjval] using htime
        · intro h
          rcases h with hlt' | ⟨heq', htime⟩
          · left
            apply hcastLt.mpr
            apply hlt.mpr
            rw [hscoreA, hscoreB]
            exact hltK.mpr hlt'
          · right
            constructor
            · apply hcastEq.mpr
              apply heq.mpr
              rw [hscoreA, hscoreB]
              exact heqK.mpr heq'
            · simpa [hival, hjval] using htime
      have hleft : itemLE E a b = decide
          (((xa - K) * xb * rb : Nat) < ((xb - K) * xa * ra : Nat) ∨
            (((xa - K) * xb * rb : Nat) = ((xb - K) * xa * ra : Nat) ∧ a.time ≤ b.time)) := by
        simp [itemLE, ha0, hb0, xa, xb, K, ra, rb]
      have hright : shortOrderLE w i j =
          decide (shortA < shortB ∨ (shortA = shortB ∧ i.val ≤ j.val)) := by
        simp [shortOrderLE, shortA, shortB, hki0', hkj0']
      rw [hleft, hright]
      exact decide_iff hprop

private theorem shortComparator : ShortComparatorLeaf := by
  intro E hv n w s hr a b ha hb i j hi hj
  have hia : itemIndex a (item_time_lt hr ha) = i := by
    apply Fin.ext
    exact hi.symm
  have hjb : itemIndex b (item_time_lt hr hb) = j := by
    apply Fin.ext
    exact hj.symm
  rw [itemLE_eq_shortOrder hv hr ha hb, hia, hjb]

private noncomputable def itemOrderScore (E : Exact) (a : RewardItem) : WithTop ℚ :=
  if a.reward = 0 then ⊤ else
    ↑((((exposureFactor E a - E.denominator : Nat) : ℚ) /
      ((exposureFactor E a : ℚ) * (a.reward : ℚ))) : ℚ)

private noncomputable def itemOrderKey (E : Exact) (a : RewardItem) : WithTop ℚ × Nat :=
  (itemOrderScore E a, a.time)

private abbrev lexLE {α β : Type} [LT α] [LE β] (x y : α × β) : Prop :=
  Prod.Lex (· < ·) (· ≤ ·) x y

private theorem itemLE_eq_lex {E : Exact} (hv : ExactValid E) (a b : RewardItem) :
    itemLE E a b = decide (lexLE (itemOrderKey E a) (itemOrderKey E b)) := by
  classical
  have hden : (0 : ℚ) < E.denominator := by exact_mod_cast hv.1
  have hxaRatio : (exposureFactor E a : ℚ) / E.denominator = passageFactor a.straight :=
    exposureFactor_scaled hv rfl
  have hxbRatio : (exposureFactor E b : ℚ) / E.denominator = passageFactor b.straight :=
    exposureFactor_scaled hv rfl
  have hxaGt : E.denominator < exposureFactor E a := by
    have hq : (1 : ℚ) < (exposureFactor E a : ℚ) / E.denominator := by
      rw [hxaRatio]
      exact passageFactor_gt_one _
    have hq' : (E.denominator : ℚ) < (exposureFactor E a : ℚ) := by
      simpa using (lt_div_iff₀ hden).mp hq
    exact_mod_cast hq'
  have hxbGt : E.denominator < exposureFactor E b := by
    have hq : (1 : ℚ) < (exposureFactor E b : ℚ) / E.denominator := by
      rw [hxbRatio]
      exact passageFactor_gt_one _
    have hq' : (E.denominator : ℚ) < (exposureFactor E b : ℚ) := by
      simpa using (lt_div_iff₀ hden).mp hq
    exact_mod_cast hq'
  by_cases ha0 : a.reward = 0
  · by_cases hb0 : b.reward = 0
    · have hprop : (b.reward = 0 ∧ a.time ≤ b.time) ↔
          lexLE (itemOrderKey E a) (itemOrderKey E b) := by
        unfold lexLE
        rw [Prod.lex_def]
        simp [itemOrderKey, itemOrderScore, ha0, hb0]
      unfold itemLE
      simp only [if_pos ha0, if_pos hb0]
      exact decide_iff hprop
    · have hprop : (b.reward = 0 ∧ a.time ≤ b.time) ↔
          lexLE (itemOrderKey E a) (itemOrderKey E b) := by
        simp [lexLE, itemOrderKey, itemOrderScore, Prod.lex_def, ha0, hb0]
      unfold itemLE
      simp only [if_pos ha0, if_neg hb0]
      exact decide_iff hprop
  · by_cases hb0 : b.reward = 0
    · have hprop : True ↔ lexLE (itemOrderKey E a) (itemOrderKey E b) := by
        simp [lexLE, itemOrderKey, itemOrderScore, Prod.lex_def, ha0, hb0]
      unfold itemLE
      simp only [if_neg ha0, if_pos hb0]
      exact decide_iff hprop
    · let xa := exposureFactor E a
      let xb := exposureFactor E b
      let K := E.denominator
      let ra := a.reward
      let rb := b.reward
      have hxaGt' : K < xa := by simpa [K, xa] using hxaGt
      have hxbGt' : K < xb := by simpa [K, xb] using hxbGt
      have hraPos : 0 < ra := Nat.pos_of_ne_zero ha0
      have hrbPos : 0 < rb := Nat.pos_of_ne_zero hb0
      let crossA : ℚ := ((xa - K) * xb * rb : Nat)
      let crossB : ℚ := ((xb - K) * xa * ra : Nat)
      let scoreA : ℚ := ((xa - K : Nat) : ℚ) / ((xa : ℚ) * ra)
      let scoreB : ℚ := ((xb - K : Nat) : ℚ) / ((xb : ℚ) * rb)
      have hcastA : ((xa - K : Nat) : ℚ) = (xa : ℚ) - K := by
        rw [Nat.cast_sub (Nat.le_of_lt hxaGt')]
      have hcastB : ((xb - K : Nat) : ℚ) = (xb : ℚ) - K := by
        rw [Nat.cast_sub (Nat.le_of_lt hxbGt')]
      have hxaPos : 0 < xa := by omega
      have hxbPos : 0 < xb := by omega
      have hdenA : (0 : ℚ) < (xa : ℚ) * ra :=
        mul_pos (by exact_mod_cast hxaPos) (by exact_mod_cast hraPos)
      have hdenB : (0 : ℚ) < (xb : ℚ) * rb :=
        mul_pos (by exact_mod_cast hxbPos) (by exact_mod_cast hrbPos)
      have hlt : crossA < crossB ↔ scoreA < scoreB := by
        dsimp [crossA, crossB, scoreA, scoreB]
        rw [div_lt_div_iff₀ hdenA hdenB]
        constructor <;> intro h <;>
          simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
      have heq : crossA = crossB ↔ scoreA = scoreB := by
        dsimp [crossA, crossB, scoreA, scoreB]
        rw [div_eq_div_iff (ne_of_gt hdenA) (ne_of_gt hdenB)]
        constructor <;> intro h <;>
          simpa [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
      have hcastLt :
          (((xa - K) * xb * rb : Nat) < ((xb - K) * xa * ra : Nat)) ↔ crossA < crossB := by
        exact_mod_cast (show (((xa - K) * xb * rb : Nat) : ℚ) <
            (((xb - K) * xa * ra : Nat) : ℚ) ↔ crossA < crossB by rfl)
      have hcastEq :
          (((xa - K) * xb * rb : Nat) = ((xb - K) * xa * ra : Nat)) ↔ crossA = crossB := by
        exact_mod_cast (show (((xa - K) * xb * rb : Nat) : ℚ) =
            (((xb - K) * xa * ra : Nat) : ℚ) ↔ crossA = crossB by rfl)
      have hprop :
          (((xa - K) * xb * rb : Nat) < ((xb - K) * xa * ra : Nat) ∨
            (((xa - K) * xb * rb : Nat) = ((xb - K) * xa * ra : Nat) ∧ a.time ≤ b.time)) ↔
          lexLE (itemOrderKey E a) (itemOrderKey E b) := by
        have hcross :
            (((xa - K) * xb * rb : Nat) < ((xb - K) * xa * ra : Nat) ∨
              (((xa - K) * xb * rb : Nat) = ((xb - K) * xa * ra : Nat) ∧ a.time ≤ b.time)) ↔
            (scoreA < scoreB ∨ (scoreA = scoreB ∧ a.time ≤ b.time)) := by
          rw [hcastLt, hcastEq, hlt, heq]
        have hkey :
            (scoreA < scoreB ∨ (scoreA = scoreB ∧ a.time ≤ b.time)) ↔
              lexLE (itemOrderKey E a) (itemOrderKey E b) := by
          unfold lexLE itemOrderKey itemOrderScore
          rw [Prod.lex_def]
          simp [ha0, hb0, scoreA, scoreB, xa, xb, K, ra, rb]
        exact hcross.trans hkey
      unfold itemLE
      simp only [if_neg ha0, if_neg hb0]
      exact decide_iff hprop

private theorem itemLE_trans {E : Exact} (hv : ExactValid E) {a b c : RewardItem}
    (hab : itemLE E a b = true) (hbc : itemLE E b c = true) : itemLE E a c = true := by
  rw [itemLE_eq_lex hv] at hab hbc ⊢
  have hab' : lexLE (itemOrderKey E a) (itemOrderKey E b) := decide_eq_true_eq.mp hab
  have hbc' : lexLE (itemOrderKey E b) (itemOrderKey E c) := decide_eq_true_eq.mp hbc
  exact decide_eq_true_eq.mpr (Prod.Lex.trans hab' hbc')

private theorem itemLE_total {E : Exact} (hv : ExactValid E) (a b : RewardItem) :
    itemLE E a b = true ∨ itemLE E b a = true := by
  have htotal : Std.Total (lexLE : (WithTop ℚ × Nat) → (WithTop ℚ × Nat) → Prop) := inferInstance
  rcases htotal.total (itemOrderKey E a) (itemOrderKey E b) with h | h
  · left
    rw [itemLE_eq_lex hv]
    exact decide_eq_true_eq.mpr h
  · right
    rw [itemLE_eq_lex hv]
    exact decide_eq_true_eq.mpr h

private theorem itemLE_pairwise_mergeSort {E : Exact} (hv : ExactValid E)
    (xs : List RewardItem) :
    List.Pairwise (fun a b => itemLE E a b = true) (xs.mergeSort (itemLE E)) := by
  have htrans : ∀ a b c, itemLE E a b = true → itemLE E b c = true → itemLE E a c = true := by
    intro a b c hab hbc
    exact itemLE_trans hv hab hbc
  have htotal : ∀ a b, (itemLE E a b || itemLE E b a) = true := by
    intro a b
    rcases itemLE_total hv a b with h | h <;> simp [h]
  exact List.pairwise_mergeSort htrans htotal xs

private noncomputable def shortOrderScore {n : Nat} (w : DirectionWord n) (i : Fin n) : WithTop ℚ :=
  if witnessKappa w i = 0 then ⊤ else
    ↑((passageFactor (wordStraight kernelIncoming w i) - 1) /
      (passageFactor (wordStraight kernelIncoming w i) * witnessKappa w i))

private noncomputable def shortOrderKey {n : Nat} (w : DirectionWord n) (i : Fin n) :
    WithTop ℚ × Nat := (shortOrderScore w i, i.val)

private theorem shortOrder_eq_lex {n : Nat} (w : DirectionWord n) (i j : Fin n) :
    shortOrderLE w i j = decide (lexLE (shortOrderKey w i) (shortOrderKey w j)) := by
  classical
  by_cases hi : witnessKappa w i = 0
  · by_cases hj : witnessKappa w j = 0
    · have hprop : (witnessKappa w j = 0 ∧ i.val ≤ j.val) ↔
          lexLE (shortOrderKey w i) (shortOrderKey w j) := by
        unfold lexLE
        rw [Prod.lex_def]
        simp [shortOrderKey, shortOrderScore, hi, hj]
      unfold shortOrderLE
      simp only [if_pos hi]
      exact decide_iff hprop
    · have hprop : (witnessKappa w j = 0 ∧ i.val ≤ j.val) ↔
          lexLE (shortOrderKey w i) (shortOrderKey w j) := by
        simp [lexLE, shortOrderKey, shortOrderScore, hi, hj, Prod.lex_def]
      unfold shortOrderLE
      simp only [if_pos hi]
      exact decide_iff hprop
  · by_cases hj : witnessKappa w j = 0
    · have hprop : True ↔ lexLE (shortOrderKey w i) (shortOrderKey w j) := by
        simp [lexLE, shortOrderKey, shortOrderScore, hi, hj, Prod.lex_def]
      unfold shortOrderLE
      simp only [if_neg hi, if_pos hj]
      exact decide_iff hprop
    · have hprop :
          (((passageFactor (wordStraight kernelIncoming w i) - 1) /
              (passageFactor (wordStraight kernelIncoming w i) * witnessKappa w i) <
            (passageFactor (wordStraight kernelIncoming w j) - 1) /
              (passageFactor (wordStraight kernelIncoming w j) * witnessKappa w j)) ∨
            (((passageFactor (wordStraight kernelIncoming w i) - 1) /
                (passageFactor (wordStraight kernelIncoming w i) * witnessKappa w i) =
              (passageFactor (wordStraight kernelIncoming w j) - 1) /
                (passageFactor (wordStraight kernelIncoming w j) * witnessKappa w j)) ∧
              i.val ≤ j.val)) ↔ lexLE (shortOrderKey w i) (shortOrderKey w j) := by
        simp [lexLE, shortOrderKey, shortOrderScore, hi, hj, Prod.lex_def]
      unfold shortOrderLE
      simp only [if_neg hi, if_neg hj]
      exact decide_iff hprop

private theorem shortOrder_trans {n : Nat} (w : DirectionWord n) {i j k : Fin n}
    (hij : shortOrderLE w i j = true) (hjk : shortOrderLE w j k = true) :
    shortOrderLE w i k = true := by
  rw [shortOrder_eq_lex] at hij hjk ⊢
  have hij' : lexLE (shortOrderKey w i) (shortOrderKey w j) := decide_eq_true_eq.mp hij
  have hjk' : lexLE (shortOrderKey w j) (shortOrderKey w k) := decide_eq_true_eq.mp hjk
  exact decide_eq_true_eq.mpr (Prod.Lex.trans hij' hjk')

private theorem shortOrder_total {n : Nat} (w : DirectionWord n) (i j : Fin n) :
    shortOrderLE w i j = true ∨ shortOrderLE w j i = true := by
  have htotal : Std.Total (lexLE : (WithTop ℚ × Nat) → (WithTop ℚ × Nat) → Prop) := inferInstance
  rcases htotal.total (shortOrderKey w i) (shortOrderKey w j) with h | h
  · left
    rw [shortOrder_eq_lex]
    exact decide_eq_true_eq.mpr h
  · right
    rw [shortOrder_eq_lex]
    exact decide_eq_true_eq.mpr h

private def itemFin {n : Nat} (hn : 0 < n) (a : RewardItem) : Fin n :=
  ⟨a.time % n, Nat.mod_lt _ hn⟩

private theorem itemFin_eq_itemIndex {n : Nat} (hn : 0 < n) (a : RewardItem)
    (h : a.time < n) : itemFin hn a = itemIndex a h := by
  apply Fin.ext
  simp [itemFin, itemIndex, Nat.mod_eq_of_lt h]

private theorem finVal_map_injective {n : Nat} {xs ys : List (Fin n)}
    (h : xs.map Fin.val = ys.map Fin.val) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          rcases h with ⟨hxy, htail⟩
          have hxy' : x = y := Fin.ext hxy
          subst y
          simp only [List.cons.injEq]
          exact ⟨True.intro, ih htail⟩

private theorem lexLE_antisymm {a b : WithTop ℚ × Nat}
    (hab : lexLE a b) (hba : lexLE b a) : a = b := by
  unfold lexLE at hab hba
  rw [Prod.lex_def] at hab hba
  rcases hab with hlt | ⟨heq, hle⟩
  · rcases hba with hgt | ⟨heq', _⟩
    · exact (lt_asymm hlt hgt).elim
    · exact (hlt.ne heq'.symm).elim
  · rcases hba with hgt | ⟨heq', hle'⟩
    · exact (hgt.ne heq.symm).elim
    · exact Prod.ext heq (Nat.le_antisymm hle hle')

private theorem shortOrder_antisymm {n : Nat} (w : DirectionWord n) {i j : Fin n}
    (hij : shortOrderLE w i j = true) (hji : shortOrderLE w j i = true) : i = j := by
  have hi : lexLE (shortOrderKey w i) (shortOrderKey w j) := by
    have hdec : decide (lexLE (shortOrderKey w i) (shortOrderKey w j)) = true := by
      simpa [shortOrder_eq_lex] using hij
    exact decide_eq_true_eq.mp hdec
  have hj : lexLE (shortOrderKey w j) (shortOrderKey w i) := by
    have hdec : decide (lexLE (shortOrderKey w j) (shortOrderKey w i)) = true := by
      simpa [shortOrder_eq_lex] using hji
    exact decide_eq_true_eq.mp hdec
  have heq := lexLE_antisymm hi hj
  apply Fin.ext
  exact congrArg Prod.snd heq

private theorem itemIndices_eq_reverse {E : Exact} {n : Nat} {w : DirectionWord n}
    {s : PrefixState} (hr : PrefixRepresents E w s) (hn : 0 < n) :
    s.items.map (itemFin hn) = (firstVisitList w).reverse := by
  have hbound : ∀ a, a ∈ s.items → a.time < n := fun a ha => item_time_lt hr ha
  rcases hr with ⟨_, _, _, htimes, _⟩
  apply finVal_map_injective
  calc
    (s.items.map (itemFin hn)).map Fin.val =
        s.items.map (fun a => (itemFin hn a).val) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro a ha
          rfl
    _ = s.items.map RewardItem.time := by
        apply List.map_congr_left
        intro a ha
        simp [itemFin, Nat.mod_eq_of_lt (hbound a ha)]
    _ = (firstVisitList w).reverse.map Fin.val := htimes

private theorem itemLE_to_shortOrder {E : Exact} {n : Nat} {w : DirectionWord n}
    {s : PrefixState} (hv : ExactValid E) (hr : PrefixRepresents E w s)
    (hn : 0 < n) {a b : RewardItem} (ha : a ∈ s.items) (hb : b ∈ s.items)
    (hle : itemLE E a b = true) :
    shortOrderLE w (itemFin hn a) (itemFin hn b) = true := by
  have hia : (itemFin hn a).val = a.time := by
    simp [itemFin, Nat.mod_eq_of_lt (item_time_lt hr ha)]
  have hib : (itemFin hn b).val = b.time := by
    simp [itemFin, Nat.mod_eq_of_lt (item_time_lt hr hb)]
  have hc := shortComparator E hv n w s hr a b ha hb (itemFin hn a) (itemFin hn b) hia hib
  rw [hle] at hc
  exact hc.symm

private theorem itemSorted_pairwise_mem {E : Exact} (hv : ExactValid E)
    (xs : List RewardItem) :
    List.Pairwise
      (fun a b => a ∈ xs.mergeSort (itemLE E) ∧ b ∈ xs.mergeSort (itemLE E) ∧
        itemLE E a b = true) (xs.mergeSort (itemLE E)) := by
  exact List.Pairwise.and_mem.mp (itemLE_pairwise_mergeSort hv xs)

private theorem sortedItemIndices_pairwise {E : Exact} {n : Nat}
    {w : DirectionWord n} {s : PrefixState} (hv : ExactValid E)
    (hr : PrefixRepresents E w s) (hn : 0 < n) :
    List.Pairwise (fun i j => shortOrderLE w i j = true)
      ((s.items.mergeSort (itemLE E)).map (itemFin hn)) := by
  let sortedItems := s.items.mergeSort (itemLE E)
  have hsortItems : sortedItems.Perm s.items := by
    exact List.mergeSort_perm s.items (itemLE E)
  have hmem : ∀ a ∈ sortedItems, a ∈ s.items := by
    intro a ha
    exact hsortItems.mem_iff.mp ha
  have hpairItemsMem := itemSorted_pairwise_mem hv s.items
  have hpairShortItems : List.Pairwise
      (fun a b => shortOrderLE w (itemFin hn a) (itemFin hn b) = true) sortedItems :=
    hpairItemsMem.imp (by
      intro a b hab
      rcases hab with ⟨ha, hb, hab⟩
      have hma := hmem a ha
      have hmb := hmem b hb
      exact itemLE_to_shortOrder hv hr hn hma hmb hab)
  have hpairShort : List.Pairwise
      (fun i j => shortOrderLE w i j = true) (sortedItems.map (itemFin hn)) := by
    simpa only [List.pairwise_map] using hpairShortItems
  exact hpairShort

private theorem sortedItemIndices_permVisits {E : Exact} {n : Nat}
    {w : DirectionWord n} {s : PrefixState} (hr : PrefixRepresents E w s)
    (hn : 0 < n) :
    ((s.items.mergeSort (itemLE E)).map (itemFin hn)).Perm (firstVisitList w) := by
  let sortedItems := s.items.mergeSort (itemLE E)
  have hsortItems : sortedItems.Perm s.items := List.mergeSort_perm s.items (itemLE E)
  have hp1 : (sortedItems.map (itemFin hn)).Perm (s.items.map (itemFin hn)) :=
    List.Perm.map (itemFin hn) hsortItems
  have hp2 : (s.items.map (itemFin hn)).Perm (firstVisitList w) := by
    rw [itemIndices_eq_reverse hr hn]
    exact List.reverse_perm _
  exact hp1.trans hp2

private theorem sortedVisits_pairwise {n : Nat} (w : DirectionWord n) :
    List.Pairwise (fun i j => shortOrderLE w i j = true)
      ((firstVisitList w).mergeSort (shortOrderLE w)) := by
  have hshortTrans : ∀ i j k, shortOrderLE w i j = true →
      shortOrderLE w j k = true → shortOrderLE w i k = true := by
    intro i j k hij hjk
    exact shortOrder_trans w hij hjk
  have hshortTotal : ∀ i j, (shortOrderLE w i j || shortOrderLE w j i) = true := by
    intro i j
    rcases shortOrder_total w i j with h | h <;> simp [h]
  exact List.pairwise_mergeSort hshortTrans hshortTotal (firstVisitList w)

private theorem sortedItemIndices_eq_sortedVisits {E : Exact} {n : Nat}
    {w : DirectionWord n} {s : PrefixState} (hv : ExactValid E)
    (hr : PrefixRepresents E w s) (hn : 0 < n) :
    (s.items.mergeSort (itemLE E)).map (itemFin hn) =
      (firstVisitList w).mergeSort (shortOrderLE w) := by
  have hpTarget : ((firstVisitList w).mergeSort (shortOrderLE w)).Perm
      (firstVisitList w) := List.mergeSort_perm (firstVisitList w) (shortOrderLE w)
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ hab hba => shortOrder_antisymm w hab hba)
    (sortedItemIndices_pairwise hv hr hn) (sortedVisits_pairwise w)
    ((sortedItemIndices_permVisits hr hn).trans hpTarget.symm)

private theorem exposureNumerator_scaled {E : Exact} {n : Nat} {w : DirectionWord n}
    {s : PrefixState} (hv : ExactValid E) (hr : PrefixRepresents E w s)
    (hn : 0 < n) (xs : List RewardItem) (hmem : ∀ a ∈ xs, a ∈ s.items) :
    ((exposureNumerator E xs : Nat) : ℚ) / (E.denominator : ℚ)^(2*xs.length) =
      exposureSum w (witnessKappa w) (xs.map (itemFin hn)) := by
  induction xs with
  | nil => simp [exposureNumerator, exposureSum]
  | cons a xs ih =>
      have ha : a ∈ s.items := hmem a (by simp)
      have hmemTail : ∀ b ∈ xs, b ∈ s.items := by
        intro b hb
        exact hmem b (by simp [hb])
      have hdata := item_data hr ha
      have hfactor := exposureFactor_scaled hv hdata.1
      have hi := itemFin_eq_itemIndex hn a (item_time_lt hr ha)
      rw [← hi] at hdata hfactor
      have hKpos : (0 : ℚ) < E.denominator := by exact_mod_cast hv.1
      have hKne : (E.denominator : ℚ) ≠ 0 := ne_of_gt hKpos
      have hexp : 2 * (xs.length + 1) = 2 * xs.length + 2 := by omega
      have hcalc :
          (((exposureFactor E a : ℚ) *
              ((a.reward : ℚ) * (E.denominator : ℚ)^(2*xs.length) +
                (E.denominator : ℚ) * (exposureNumerator E xs : ℚ))) /
              (E.denominator : ℚ)^(2*(xs.length+1))) =
            ((exposureFactor E a : ℚ) / E.denominator) *
              ((a.reward : ℚ) / E.denominator +
                (exposureNumerator E xs : ℚ) / (E.denominator : ℚ)^(2*xs.length)) := by
        rw [hexp, pow_add]
        field_simp [hKne]
        <;> ring
      simp only [exposureNumerator, List.length_cons, Nat.cast_mul, Nat.cast_add,
        Nat.cast_pow, List.map_cons, exposureSum]
      rw [hcalc, hfactor, hdata.2, ih hmemTail]

theorem main : CertData.H3.Bridge.ShortValueLeaf := by
  intro E hv n hn w s hr
  by_cases hn0 : n = 0
  · subst n
    rcases hr with ⟨_, _, _, htimes, _⟩
    have hlen := congrArg List.length htimes
    have hitemsLen : s.items.length = 0 := by
      simpa [firstVisitList] using hlen
    have hitems : s.items = [] := List.eq_nil_of_length_eq_zero hitemsLen
    have hshort : shortValue E s = 0 := by
      simp [hitems, shortValue, mergeSortFuel, exposureNumerator]
    rw [hshort]
    simp [closedContribution, kernelOrdering, firstVisitList, exposureSum]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    let hrepr : PrefixRepresents E w s := hr
    rcases hr with ⟨hwalk, hphases, hbase, htimes, hitems⟩
    let sorted := s.items.mergeSort (itemLE E)
    have htimeLen := congrArg List.length htimes
    simp only [List.length_map, List.length_reverse] at htimeLen
    have hfirstLen : (firstVisitList w).length ≤ n := by
      simpa only [firstVisitList, List.length_finRange] using
        List.length_filter_le (fun i => !wordRevisit kernelStart w i) (List.finRange n)
    have hitemsLen : s.items.length ≤ n := by omega
    have hsortPerm : sorted.Perm s.items := List.mergeSort_perm s.items (itemLE E)
    have hsortLen : sorted.length = s.items.length := hsortPerm.length_eq
    have hsortedLen : sorted.length ≤ n := by omega
    have hidx : n + 2 * sorted.length ≤ 36 := by omega
    have hsum : n + (2 * sorted.length + (36 - (n + 2 * sorted.length))) = 36 := by omega
    have hKne : (E.denominator : ℚ) ≠ 0 := by
      have hKpos : (0 : ℚ) < E.denominator := by exact_mod_cast hv.1
      exact ne_of_gt hKpos
    have hpow : (E.denominator : ℚ)^36 =
        (E.denominator : ℚ)^n * ((E.denominator : ℚ)^(2*sorted.length) *
          (E.denominator : ℚ)^(36-(n+2*sorted.length))) := by
      calc
        (E.denominator : ℚ)^36 =
            (E.denominator : ℚ)^(n+(2*sorted.length+(36-(n+2*sorted.length)))) := by
              congr 1
              exact hsum.symm
        _ = (E.denominator : ℚ)^n *
            (E.denominator : ℚ)^(2*sorted.length+(36-(n+2*sorted.length))) := by
              rw [pow_add]
        _ = (E.denominator : ℚ)^n *
            ((E.denominator : ℚ)^(2*sorted.length) *
              (E.denominator : ℚ)^(36-(n+2*sorted.length))) := by
              rw [pow_add]
    have hshortScale : (shortValue E s : ℚ) / (E.denominator^36 : Nat) =
        ((s.base : ℚ) / (E.denominator : ℚ)^n) *
          (((exposureNumerator E sorted : Nat) : ℚ) /
            (E.denominator : ℚ)^(2*sorted.length)) := by
      rw [shortValue, mergeSortFuel_eq (itemLE E) s.items.length s.items le_rfl]
      push_cast
      rw [hwalk.1, hpow]
      field_simp [hKne]
      <;> ring
    have hsorted : sorted.map (itemFin hnpos) =
        (firstVisitList w).mergeSort (shortOrderLE w) :=
      sortedItemIndices_eq_sortedVisits hv hrepr hnpos
    have hmemSorted : ∀ a ∈ sorted, a ∈ s.items := by
      intro a ha
      exact hsortPerm.mem_iff.mp ha
    have hscale := exposureNumerator_scaled hv hrepr hnpos sorted hmemSorted
    rw [hsorted] at hscale
    have hkernel : kernelOrdering w = (firstVisitList w).mergeSort (shortOrderLE w) := by
      simp [kernelOrdering, hn]
    have hbase' : trailBaseWeight kernelStart w =
        (s.base : ℚ) / (E.denominator : ℚ)^n := by
      simpa only [Nat.cast_pow] using hbase
    calc
      (shortValue E s : ℚ) / (E.denominator^36 : Nat) =
          ((s.base : ℚ) / (E.denominator : ℚ)^n) *
            exposureSum w (witnessKappa w)
              ((firstVisitList w).mergeSort (shortOrderLE w)) := by
        rw [hshortScale, hscale]
      _ = closedContribution w := by
        rw [← hbase', closedContribution, hkernel]

end AKLT.W.H3C033
end

#print axioms AKLT.W.H3C033.main
