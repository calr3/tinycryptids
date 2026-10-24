import TinyCryptids.Defs

/-!
# The statement

`properDivSum` (`TinyCryptids.Defs`) is the sum of the proper divisors; the lemmas
here are the arithmetic the proof needs.
-/

namespace TM.OddPerfect

open TinyCryptids


example : properDivSum 6 = 6 := by decide
example : properDivSum 28 = 28 := by decide
example : properDivSum 1 = 0 := by decide
example : properDivSum 12 = 16 := by decide

theorem properDivSum_eq (n : Nat) (hn : 1 ≤ n) : properDivSum n = divSumBelow n (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [properDivSum, divSumBelow]

theorem sub_mod_self (n d : Nat) (h : d ≤ n) : (n - d) % d = n % d := by
  have := Nat.add_mod_right (n - d) d
  rw [Nat.sub_add_cancel h] at this; exact this.symm

theorem divSumBelow_step (n d : Nat) (hd : 1 ≤ d) (hdn : d < n) :
    divSumBelow n (d - 1) + (if (n - d) % d = 0 then d else 0) = divSumBelow n d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [sub_mod_self n (e + 1) (by omega)]
  simp only [divSumBelow, Nat.add_sub_cancel, hdn, true_and]

/-- `(x + 1) % d` from `x % d` -/
theorem mod_succ (x d : Nat) :
    (x % d + 1 < d → (x + 1) % d = x % d + 1) ∧ (x % d + 1 = d → (x + 1) % d = 0) := by
  have e := Nat.div_add_mod x d
  constructor
  · intro h
    have : x + 1 = d * (x / d) + (x % d + 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · intro h
    have : x + 1 = d * (x / d + 1) := by rw [Nat.mul_add]; omega
    rw [this, Nat.mul_mod_right]

end TM.OddPerfect
