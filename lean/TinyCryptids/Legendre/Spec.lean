import TinyCryptids.Defs

/-!
# The statement

Legendre's conjecture: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`. `LegendreFails n` says that `n` is a counterexample.
-/

namespace TM.Legendre

open TinyCryptids


def LegendreFails (n : Nat) : Prop := 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n + 1) ^ 2 → ¬ Prime p

theorem sq (n : Nat) : n ^ 2 = n * n := by rw [Nat.pow_two]

theorem sq_succ (n : Nat) : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

theorem not_fails_one : ¬ LegendreFails 1 := fun ⟨_, h⟩ =>
  h 2 (by decide) (by decide) ⟨by decide, fun d h1 h2 => by omega⟩

theorem square_not_prime (n : Nat) (hn : 2 ≤ n) : ¬ Prime (n * n) := by
  rintro ⟨_, h⟩
  have : n < n * n := by
    have := Nat.mul_le_mul_left n hn
    omega
  exact h n this hn (Nat.mul_mod_right n n)

/-- for `n ≥ 2`, `n` is a counterexample iff none of `n², …, n² + 2n` is prime -/
theorem fails_iff (n : Nat) (hn : 2 ≤ n) :
    LegendreFails n ↔ ∀ i, i < 2 * n + 1 → ¬ Prime (n * n + i) := by
  unfold LegendreFails
  rw [sq, sq, sq_succ]
  constructor
  · rintro ⟨_, h⟩ i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact square_not_prime n hn
    · exact h _ (by omega) (by omega)
  · intro h
    refine ⟨by omega, fun p h1 h2 => ?_⟩
    have := h (p - n * n) (by omega)
    rwa [show n * n + (p - n * n) = p by omega] at this

theorem add_mod_self_left' (d x : Nat) : (d + x) % d = x % d := by
  rw [Nat.add_comm]; exact Nat.add_mod_right x d

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

end TM.Legendre
