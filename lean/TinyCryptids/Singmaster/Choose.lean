import TinyCryptids.Defs

/-!
# Facts about binomial coefficients
-/

namespace TinyCryptids

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl
theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_eq_zero : ∀ n k, n < k → choose n k = 0
  | 0, 0, h => absurd h (by decide)
  | 0, k + 1, _ => rfl
  | n + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero n k (by omega), choose_eq_zero n (k + 1) (by omega)]

theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_self n, choose_eq_zero n (n + 1) (by omega)]

theorem choose_one : ∀ n, choose n 1 = n
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_one n, choose_zero_right]; omega

theorem choose_pos : ∀ n k, k ≤ n → 1 ≤ choose n k
  | _, 0, _ => by simp
  | 0, k + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by rw [choose_succ_succ]; have := choose_pos n k (by omega); omega

/-- `n ≤ C(n, k)` strictly inside a row. -/
theorem le_choose : ∀ n k, 1 ≤ k → k < n → n ≤ choose n k
  | 0, _, _, h => absurd h (by omega)
  | n + 1, 0, h, _ => absurd h (by omega)
  | n + 1, k + 1, _, h => by
    rw [choose_succ_succ]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; rw [choose_zero_right, choose_one]; omega
    · have h1 := le_choose n k hk (by omega)
      have h2 := choose_pos n (k + 1) (by omega)
      omega

/-- `(n + 1) · C(n, k) = C(n + 1, k + 1) · (k + 1)`. -/
theorem succ_mul_choose : ∀ n k, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by simp [choose]
  | n + 1, 0 => by rw [choose_zero_right, choose_one]
  | n + 1, k + 1 => by
    have h1 := succ_mul_choose n k
    have h2 := succ_mul_choose n (k + 1)
    rw [choose_succ_succ (n + 1) (k + 1), choose_succ_succ n k] at *
    generalize choose n k = a at *
    generalize choose n (k + 1) = b at *
    generalize choose (n + 1) (k + 1 + 1) = c at *
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at *
    omega

/-- Values `≥ 2` occur only at `1 ≤ k < n ≤ N`. -/
theorem choose_range {n k N : Nat} (h : choose n k = N) (hN : 2 ≤ N) : k ≤ n ∧ n ≤ N := by
  rcases Nat.lt_or_ge n k with hl | hl
  · rw [choose_eq_zero n k hl] at h; omega
  · refine ⟨hl, ?_⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; rw [choose_zero_right] at h; omega
    · rcases Nat.lt_or_ge k n with hkn | hkn
      · have := le_choose n k hk hkn; omega
      · rw [show k = n by omega, choose_self] at h; omega

end TinyCryptids
