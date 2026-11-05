/-!
# Decimal doubling, digit by digit

The machine keeps `2 ^ n` as its list of decimal digits, least significant first, and
doubles it in one pass with a carry. `dbl` is that pass and `pw n` the list it holds in
round `n`; `pw_num` says `pw n` are the digits of `2 ^ n`, and `zero_mem_iff` turns
"some digit is 0" into the form of the theorem statement.
-/

namespace TM.ZeroFree

/-- A decimal digit. -/
inductive D | d0 | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8 | d9
deriving DecidableEq, Repr

open D

def D.val : D → Nat
  | d0 => 0 | d1 => 1 | d2 => 2 | d3 => 3 | d4 => 4
  | d5 => 5 | d6 => 6 | d7 => 7 | d8 => 8 | d9 => 9

/-- The value of a carry. -/
def cv : Bool → Nat
  | false => 0
  | true => 1

/-- `(2d + c) mod 10` and the carry `[2d + c ≥ 10]` (which is `[d ≥ 5]`). -/
def dd : Bool → D → D
  | false, d0 => d0 | false, d1 => d2 | false, d2 => d4 | false, d3 => d6 | false, d4 => d8
  | false, d5 => d0 | false, d6 => d2 | false, d7 => d4 | false, d8 => d6 | false, d9 => d8
  | true, d0 => d1 | true, d1 => d3 | true, d2 => d5 | true, d3 => d7 | true, d4 => d9
  | true, d5 => d1 | true, d6 => d3 | true, d7 => d5 | true, d8 => d7 | true, d9 => d9

def hi : D → Bool
  | d0 | d1 | d2 | d3 | d4 => false
  | d5 | d6 | d7 | d8 | d9 => true

theorem dd_val (c : Bool) (d : D) : (dd c d).val + 10 * cv (hi d) = 2 * d.val + cv c := by
  cases c <;> cases d <;> rfl

/-- Double a digit list (least significant first) with carry `c`. -/
def dbl (c : Bool) : List D → List D
  | [] => match c with
    | false => []
    | true => [d1]
  | d :: ds => dd c d :: dbl (hi d) ds

/-- The digits of `2 ^ n`. -/
def pw : Nat → List D
  | 0 => [d1]
  | n + 1 => dbl false (pw n)

/-- The number a digit list stands for. -/
def num : List D → Nat
  | [] => 0
  | d :: ds => d.val + 10 * num ds

theorem num_dbl (c : Bool) (ds : List D) : num (dbl c ds) = 2 * num ds + cv c := by
  induction ds generalizing c with
  | nil => cases c <;> rfl
  | cons d ds ih =>
    simp only [dbl, num, ih]
    have := dd_val c d
    omega

theorem pw_num (n : Nat) : num (pw n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pw, num_dbl, ih, cv, Nat.pow_succ]; omega

/-- No leading zero: the last digit is not 0. -/
def canon : List D → Bool
  | [] => true
  | [d] => d != d0
  | _ :: e :: ds => canon (e :: ds)

abbrev Canon (ds : List D) : Prop := canon ds = true

theorem D.val_lt (d : D) : d.val < 10 := by cases d <;> decide

theorem D.val_eq_zero {d : D} : d.val = 0 ↔ d = d0 := by cases d <;> decide

theorem num_pos : ∀ {ds : List D}, ds ≠ [] → Canon ds → 0 < num ds
  | [], h, _ => absurd rfl h
  | [d], _, hc => by
    simp only [num]
    have : d.val ≠ 0 := by
      intro h; rw [D.val_eq_zero.1 h] at hc; exact absurd hc (by decide)
    omega
  | d :: e :: ds, _, hc => by
    have := num_pos (ds := e :: ds) (List.cons_ne_nil _ _) hc
    simp only [num] at this ⊢; omega

theorem canon_tail : ∀ {d : D} {ds : List D}, Canon (d :: ds) → Canon ds
  | _, [], _ => rfl
  | _, _ :: _, h => h

theorem canon_dbl : ∀ (c : Bool) (ds : List D), Canon ds → Canon (dbl c ds)
  | false, [], _ => rfl
  | true, [], _ => rfl
  | c, [d], hc => by
    cases c <;> cases d <;> first | exact absurd hc (by decide) | rfl
  | c, d :: e :: ds, hc => by
    have ih := canon_dbl (hi d) (e :: ds) hc
    show Canon (dd c d :: dd (hi d) e :: dbl (hi e) ds)
    exact ih

theorem canon_pw (n : Nat) : Canon (pw n) := by
  induction n with
  | zero => decide
  | succ n ih => exact canon_dbl false _ ih

/-- "Some digit is 0", in the form of the theorem statement. -/
theorem zero_mem_iff : ∀ (ds : List D), Canon ds →
    ((∃ k, num ds / 10 ^ k ≠ 0 ∧ num ds / 10 ^ k % 10 = 0) ↔ d0 ∈ ds)
  | [], _ => by simp [num]
  | d :: ds, hc => by
    have ih := zero_mem_iff ds (canon_tail hc)
    have hd := D.val_lt d
    have shift : ∀ k, num (d :: ds) / 10 ^ (k + 1) = num ds / 10 ^ k := by
      intro k
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
      simp only [num]; congr 1; omega
    constructor
    · rintro ⟨k, h1, h2⟩
      cases k with
      | zero =>
        simp only [num, Nat.pow_zero, Nat.div_one] at h2
        have : d.val = 0 := by omega
        exact List.mem_cons.2 (Or.inl (D.val_eq_zero.1 this).symm)
      | succ k =>
        rw [shift] at h1 h2
        exact List.mem_cons_of_mem _ (ih.1 ⟨k, h1, h2⟩)
    · intro h
      rcases List.mem_cons.1 h with h | h
      · subst h
        refine ⟨0, ?_, ?_⟩
        · have hne : ds ≠ [] := by rintro rfl; exact absurd hc (by decide)
          have := num_pos hne (canon_tail hc)
          simp only [num, D.val, Nat.pow_zero, Nat.div_one]; omega
        · simp only [num, D.val, Nat.pow_zero, Nat.div_one]; omega
      · obtain ⟨k, h1, h2⟩ := ih.2 h
        exact ⟨k + 1, by rw [shift]; exact h1, by rw [shift]; exact h2⟩

/-- The digit 0 occurs in `pw n` iff it occurs in the decimal expansion of `2 ^ n`. -/
theorem zero_free_iff (n : Nat) :
    (∀ k, 2 ^ n / 10 ^ k ≠ 0 → (2 ^ n / 10 ^ k) % 10 ≠ 0) ↔ d0 ∉ pw n := by
  rw [← pw_num, ← zero_mem_iff _ (canon_pw n)]
  constructor
  · rintro h ⟨k, h1, h2⟩; exact h k h1 h2
  · intro h k h1 h2; exact h ⟨k, h1, h2⟩

end TM.ZeroFree
