import TinyCryptids.Defs

/-!
# The statement

Oppermann's conjecture: for every `n ≥ 2` there is a prime in `(n² - n, n²)` and a prime in
`(n², n² + n)`. `FA n` and `FB n` say that the first or the second interval has none.
-/

namespace TM.Oppermann

open TinyCryptids

/-- no prime in `(n² - n, n²)` -/
def FA (n : Nat) : Prop := ∀ p, n * n - n < p → p < n * n → ¬ Prime p

/-- no prime in `(n², n² + n)` -/
def FB (n : Nat) : Prop := ∀ p, n * n < p → p < n * n + n → ¬ Prime p

theorem sq_succ (n : Nat) : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

theorem le_sq (n : Nat) (hn : 2 ≤ n) : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn

theorem not_FA_two : ¬ FA 2 := by
  intro h
  refine h 3 (by decide) (by decide) ⟨by decide, fun d h1 h2 => ?_⟩
  obtain rfl : d = 2 := by omega
  decide

/-- `n * c` is not prime when `2 ≤ n` and `2 ≤ c` -/
theorem mul_not_prime (n c : Nat) (hn : 2 ≤ n) (hc : 2 ≤ c) : ¬ Prime (n * c) := by
  rintro ⟨_, h⟩
  have : n < n * c := by
    have := Nat.mul_le_mul_left n hc
    omega
  exact h n this hn (Nat.mul_mod_right n c)

/-- for `n ≥ 3`: `FA n` iff none of `n² - n, …, n² - 1` is prime -/
theorem FA_iff (n : Nat) (hn : 3 ≤ n) : FA n ↔ ∀ i, i < n → ¬ Prime (n * n - n + i) := by
  have h2 := le_sq n (by omega)
  have hsq : n * n - n = n * (n - 1) := by
    rw [Nat.mul_sub_one]
  constructor
  · intro h i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [Nat.add_zero, hsq]; exact mul_not_prime n (n - 1) (by omega) (by omega)
    · exact h _ (by omega) (by omega)
  · intro h p h1 h2'
    have := h (p - (n * n - n)) (by omega)
    rwa [show n * n - n + (p - (n * n - n)) = p by omega] at this

/-- for `n ≥ 2`: `FB n` iff none of `n², …, n² + n - 1` is prime -/
theorem FB_iff (n : Nat) (hn : 2 ≤ n) : FB n ↔ ∀ i, i < n → ¬ Prime (n * n + i) := by
  constructor
  · intro h i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact mul_not_prime n n hn hn
    · exact h _ (by omega) (by omega)
  · intro h p h1 h2
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

end TM.Oppermann
