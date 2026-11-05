import TinyCryptids.Defs

/-!
# Doubling in base 3, digit by digit

The machine keeps `2 ^ n` as its list of base-3 digits, least significant
first, and doubles it in one pass with a carry. `dbl` is that pass and `pw n` the
list it holds in round `n`; `pw_eq` links `pw n` to `digits3 (2 ^ n)`.
-/

namespace TM.Erdos

open TinyCryptids

/-- A base-3 digit. -/
inductive Dig | z | o | t
deriving DecidableEq, Repr

open Dig

def Dig.val : Dig → Nat
  | z => 0
  | o => 1
  | t => 2

/-- Double a digit list (least significant first), with carry in `c`. -/
def dbl : Bool → List Dig → List Dig
  | false, [] => []
  | true, [] => [o]
  | false, z :: ds => z :: dbl false ds
  | false, o :: ds => t :: dbl false ds
  | false, t :: ds => o :: dbl true ds
  | true, z :: ds => o :: dbl false ds
  | true, o :: ds => z :: dbl true ds
  | true, t :: ds => t :: dbl true ds

/-- The digits of `2 ^ n`, as the machine computes them. -/
def pw : Nat → List Dig
  | 0 => [o]
  | n + 1 => dbl false (pw n)

theorem digits3_zero : digits3 0 = [] := by rw [digits3]; simp

theorem digits3_ne {n : Nat} (h : n ≠ 0) : digits3 n = n % 3 :: digits3 (n / 3) := by
  rw [digits3]; simp [h]

/-- The value of a carry. -/
def cv : Bool → Nat
  | false => 0
  | true => 1

theorem dbl_val : ∀ (ds : List Dig) (m : Nat) (c : Bool), ds.map Dig.val = digits3 m →
    (dbl c ds).map Dig.val = digits3 (2 * m + cv c) := by
  intro ds
  induction ds with
  | nil =>
    intro m c h
    have hm : m = 0 := by
      apply Classical.byContradiction; intro hm
      rw [digits3_ne hm] at h; exact List.noConfusion h
    subst hm
    cases c
    · simp [dbl, cv, digits3_zero]
    · simp [dbl, cv, digits3_ne, digits3_zero, Dig.val]
  | cons d r ih =>
    intro m c h
    have hm : m ≠ 0 := by intro hm; subst hm; rw [digits3_zero] at h; exact List.noConfusion h
    rw [digits3_ne hm] at h
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hd, hr⟩ := h
    have hne : 2 * m + cv c ≠ 0 := by cases c <;> simp [cv] <;> omega
    rw [digits3_ne hne]
    have step : ∀ (d' : Dig) (c' : Bool), d'.val = (2 * m + cv c) % 3 →
        (2 * m + cv c) / 3 = 2 * (m / 3) + cv c' →
        d'.val :: (dbl c' r).map Dig.val = (2 * m + cv c) % 3 :: digits3 ((2 * m + cv c) / 3) := by
      intro d' c' h1 h2; rw [h1, h2, ih _ _ hr]
    cases c <;> cases d <;> simp only [Dig.val] at hd <;> simp only [dbl, List.map_cons] <;>
      exact step _ _ (by simp only [cv, Dig.val]; omega) (by simp only [cv]; omega)

theorem pw_eq (n : Nat) : (pw n).map Dig.val = digits3 (2 ^ n) := by
  induction n with
  | zero => simp [pw, Dig.val, digits3_ne, digits3_zero]
  | succ n ih =>
    have := dbl_val (pw n) (2 ^ n) false ih
    simp only [cv, Nat.add_zero] at this
    rw [pw, this, Nat.pow_succ, Nat.mul_comm]

theorem two_mem (n : Nat) : 2 ∈ digits3 (2 ^ n) ↔ t ∈ pw n := by
  rw [← pw_eq, List.mem_map]
  constructor
  · rintro ⟨d, hd, hv⟩; cases d <;> simp [Dig.val] at hv; exact hd
  · intro h; exact ⟨t, h, rfl⟩

end TM.Erdos
