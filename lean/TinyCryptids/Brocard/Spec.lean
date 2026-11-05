import TinyCryptids.Defs

/-!
# The statement

Brocard's problem: `n! + 1 = m²` has the solutions `n = 4, 5, 7`; the machine
looks for one with `n ≥ 8`. `fact` is `TinyCryptids.fact`; the lemmas here are
the arithmetic the proof needs.
-/

namespace TM.Brocard

open TinyCryptids


theorem fact_pos : ∀ n, 1 ≤ fact n
  | 0 => by decide
  | n + 1 => by
    have := fact_pos n
    show 1 ≤ fact n * (n + 1)
    have := Nat.mul_le_mul this (show 1 ≤ n + 1 by omega)
    omega

theorem fact_succ' (n : Nat) : fact (n + 1) = fact n + n * fact n := by
  show fact n * (n + 1) = _
  rw [Nat.mul_succ, Nat.mul_comm (fact n) n, Nat.add_comm]

theorem sq_succ (j : Nat) : (j + 1) * (j + 1) = j * j + (2 * j + 1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

/-- strictly between two consecutive squares there is no square -/
theorem not_square_between (j c : Nat) (h1 : 1 ≤ c) (h2 : c < 2 * j + 1) :
    ¬ ∃ m, j * j + c = m * m := by
  rintro ⟨m, hm⟩
  rcases Nat.lt_or_ge j m with h | h
  · have := Nat.mul_le_mul (show j + 1 ≤ m from h) (show j + 1 ≤ m from h)
    rw [sq_succ] at this; omega
  · have := Nat.mul_le_mul h h; omega

end TM.Brocard
