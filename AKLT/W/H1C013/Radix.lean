import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C013

variable {α : Type*}

theorem foldl_congr_mem {β : Type*} (xs : List α) (f g : β → α → β)
    (h : ∀ a x, x ∈ xs → f a x = g a x) (a : β) :
    xs.foldl f a = xs.foldl g a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h a x (List.mem_cons_self ..)]
    exact ih (fun a y hy => h a y (List.mem_cons_of_mem x hy)) _

theorem sum_filter_zero {M : Type*} [AddCommMonoid M] (xs : List α)
    (p : α → Bool) (f : α → M) (h : ∀ x ∈ xs, p x = false → f x = 0) :
    (xs.map f).sum = ((xs.filter p).map f).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases hp : p x <;> simp [hp, h x (List.mem_cons_self ..), ht]

theorem length_filter_sum (xs : List α) (p : α → Bool) :
    (xs.filter p).length = (xs.map (fun x => if p x then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp, ih, Nat.add_comm]

/-- Big-endian mixed-radix encoding, in the order of the supplied list. -/
def radix (xs : List α) (dim digit : α → Nat) : Nat :=
  xs.foldl (fun a x => a * dim x + digit x) 0

theorem radix_acc (xs : List α) (dim digit : α → Nat) (a : Nat) :
    xs.foldl (fun a x => a * dim x + digit x) a =
      a * (xs.map dim).prod + radix xs dim digit := by
  induction xs generalizing a with
  | nil => simp [radix]
  | cons x xs ih =>
    simp only [radix, List.foldl_cons, Nat.zero_mul, Nat.zero_add,
      List.map_cons, List.prod_cons]
    rw [ih, ih]
    ring

theorem radix_cons (x : α) (xs : List α) (dim digit : α → Nat) :
    radix (x :: xs) dim digit = digit x * (xs.map dim).prod + radix xs dim digit := by
  simp only [radix, List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  exact radix_acc xs dim digit (digit x)

theorem radix_append (xs ys : List α) (dim digit : α → Nat) :
    radix (xs ++ ys) dim digit =
      radix xs dim digit * (ys.map dim).prod + radix ys dim digit := by
  simp only [radix, List.foldl_append]
  exact radix_acc ys dim digit _

theorem radix_lt (xs : List α) (dim digit : α → Nat)
    (h : ∀ x ∈ xs, digit x < dim x) :
    radix xs dim digit < (xs.map dim).prod := by
  induction xs with
  | nil => simp [radix]
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [radix_cons, List.map_cons, List.prod_cons]
    nlinarith

theorem radix_congr (xs : List α) (dim digit digit' : α → Nat)
    (h : ∀ x ∈ xs, digit x = digit' x) :
    radix xs dim digit = radix xs dim digit' := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [radix_cons, radix_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem radix_injective (xs : List α) (dim f g : α → Nat)
    (hf : ∀ x ∈ xs, f x < dim x) (hg : ∀ x ∈ xs, g x < dim x)
    (he : radix xs dim f = radix xs dim g) : ∀ x ∈ xs, f x = g x := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hft := fun x hx => hf x (List.mem_cons_of_mem a hx)
    have hgt := fun x hx => hg x (List.mem_cons_of_mem a hx)
    have hfl := radix_lt xs dim f hft
    have hgl := radix_lt xs dim g hgt
    have hp : 0 < (xs.map dim).prod := lt_of_le_of_lt (Nat.zero_le _) hfl
    rw [radix_cons, radix_cons] at he
    have ha : f a = g a := by
      have hd := congrArg (fun n => n / (xs.map dim).prod) he
      simpa only [Nat.mul_comm (f a), Nat.mul_comm (g a),
        Nat.mul_add_div hp, Nat.div_eq_of_lt hfl, Nat.div_eq_of_lt hgl,
        Nat.add_zero] using hd
    have ht : radix xs dim f = radix xs dim g := by
      rw [ha] at he
      exact Nat.add_left_cancel he
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih hft hgt ht x hx

theorem radix_surjective [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (dim : α → Nat) (hd : ∀ x ∈ xs, 0 < dim x) (n : Nat)
    (h : n < (xs.map dim).prod) :
    ∃ f : α → Nat, (∀ x ∈ xs, f x < dim x) ∧ radix xs dim f = n := by
  induction xs generalizing n with
  | nil =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    have hn : n = 0 := by simpa using h
    simpa [radix] using hn.symm
  | cons a xs ih =>
    rcases List.nodup_cons.mp hn with ⟨hna, hnt⟩
    have hdt := fun x hx => hd x (List.mem_cons_of_mem a hx)
    have hp : 0 < (xs.map dim).prod := List.prod_pos (by simpa using hdt)
    obtain ⟨f, hf, he⟩ := ih hnt hdt (n % (xs.map dim).prod) (Nat.mod_lt _ hp)
    let g := fun x => if x = a then n / (xs.map dim).prod else f x
    have hga : g a = n / (xs.map dim).prod := if_pos rfl
    have hgt : ∀ x ∈ xs, g x = f x := by
      intro x hx
      exact if_neg (show x ≠ a from fun he => hna (he ▸ hx))
    refine ⟨g, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hga]
        apply (Nat.div_lt_iff_lt_mul hp).mpr
        simpa only [List.map_cons, List.prod_cons] using h
      · rw [hgt x hx]
        exact hf x hx
    · rw [radix_cons, hga, radix_congr xs dim g f hgt, he]
      simpa only [Nat.mul_comm] using Nat.div_add_mod n (xs.map dim).prod

/-- Recover a digit using its suffix-product stride. -/
theorem radix_digit (xs : List α) (dim f : α → Nat)
    (hf : ∀ x ∈ xs, f x < dim x) (i : Nat) (hi : i < xs.length) :
    radix xs dim f / ((xs.drop (i+1)).map dim).prod % dim xs[i] = f xs[i] := by
  have hs : xs = xs.take i ++ xs[i] :: xs.drop (i+1) :=
    by rw [← List.drop_eq_getElem_cons hi]; exact (List.take_append_drop i xs).symm
  have ht : ∀ x ∈ xs.drop (i+1), f x < dim x :=
    fun x hx => hf x (List.mem_of_mem_drop hx)
  have htail := radix_lt (xs.drop (i+1)) dim f ht
  have hp : 0 < ((xs.drop (i+1)).map dim).prod := by omega
  have hx := hf xs[i] (List.getElem_mem hi)
  rw [congrArg (fun l => radix l dim f) hs, radix_append, radix_cons]
  simp only [List.map_cons, List.prod_cons]
  rw [show radix (xs.take i) dim f *
      (dim xs[i] * ((xs.drop (i+1)).map dim).prod) +
      (f xs[i] * ((xs.drop (i+1)).map dim).prod + radix (xs.drop (i+1)) dim f) =
      ((xs.drop (i+1)).map dim).prod *
        (radix (xs.take i) dim f * dim xs[i] + f xs[i]) +
      radix (xs.drop (i+1)) dim f by ring]
  rw [Nat.mul_add_div hp, Nat.div_eq_of_lt htail, Nat.add_zero,
    Nat.mul_add_mod', Nat.mod_eq_of_lt hx]

end AKLT.W.H1C013
