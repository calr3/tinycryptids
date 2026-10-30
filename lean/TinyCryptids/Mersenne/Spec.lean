import TinyCryptids.Defs

/-!
# Arithmetic for the Mersenne prime machine

* `Good m e`: the trial divisor `e` divides neither `m` nor `m + 1`.
* `mersenne_iff`: for odd `m ≥ 3`, `m` is prime and `m + 1` is a power of 2 iff every odd
  `e` with `3 ≤ e < m` is good.
* `mpc_iff`: the Mersenne prime conjecture says that such `m` are unbounded.
-/

namespace TM.Mersenne

open TinyCryptids

def Good (m e : Nat) : Prop := m % e ≠ 0 ∧ (m + 1) % e ≠ 0

/-- `m` is a Mersenne prime -/
def MP (m : Nat) : Prop := Prime m ∧ ∃ k, m + 1 = 2 ^ k

/-- an odd `q ≥ 3` divides no power of 2 -/
theorem odd_not_dvd_pow2 (q : Nat) (hq : q % 2 = 1) (h3 : 3 ≤ q) : ∀ k, ¬ q ∣ 2 ^ k := by
  intro k
  induction k with
  | zero => intro h; have := Nat.le_of_dvd (by decide) h; omega
  | succ k ih =>
    intro ⟨t, ht⟩
    have h2 : (q * t) % 2 = 0 := by rw [← ht, Nat.pow_succ, Nat.mul_mod_left]
    have ht2 : t % 2 = 0 := by rw [Nat.mul_mod, hq] at h2; simpa using h2
    refine ih ⟨t / 2, ?_⟩
    rw [show t = 2 * (t / 2) by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm q 2,
      Nat.mul_assoc] at ht
    omega

/-- a number `≥ 1` without odd divisors `≥ 3` is a power of 2 -/
theorem pow2_of_no_odd : ∀ n, 1 ≤ n → (∀ q, q % 2 = 1 → 3 ≤ q → ¬ q ∣ n) → ∃ k, n = 2 ^ k := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h1 h
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exact ⟨0, by omega⟩
    · rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · obtain ⟨k, hk⟩ := ih (n / 2) (by omega) (by omega) fun q hq h3 ⟨t, ht⟩ =>
          h q hq h3 ⟨2 * t, by rw [← Nat.mul_assoc, Nat.mul_comm q 2, Nat.mul_assoc, ← ht]; omega⟩
        exact ⟨k + 1, by rw [Nat.pow_succ, ← hk]; omega⟩
      · exact absurd (Nat.dvd_refl n) (h n ho (by omega))

theorem mersenne_iff (m : Nat) (hm : 3 ≤ m) (ho : m % 2 = 1) :
    MP m ↔ ∀ e, 3 ≤ e → e < m → e % 2 = 1 → Good m e := by
  constructor
  · rintro ⟨⟨_, hp⟩, k, hk⟩ e h1 h2 h3
    refine ⟨hp e h2 (by omega), fun h => odd_not_dvd_pow2 e h3 h1 k ?_⟩
    rw [← hk]; exact Nat.dvd_of_mod_eq_zero h
  · intro h
    refine ⟨⟨by omega, fun e h2 h1 hz => ?_⟩, pow2_of_no_odd (m + 1) (by omega) fun q hq h3 hd => ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one e with he | he
      · obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hz
        have : m % 2 = 0 := by rw [ht, Nat.mul_mod, he]; simp
        omega
      · exact (h e (by omega) h2 he).1 hz
    · rcases Nat.lt_or_ge q m with hl | hl
      · exact (h q h3 hl hq).2 (Nat.mod_eq_zero_of_dvd hd)
      · have hle := Nat.le_of_dvd (by omega) hd
        rcases Nat.eq_or_lt_of_le hl with heq | hl'
        · subst heq
          obtain ⟨t, ht⟩ := hd
          rcases t with _ | _ | t
          · omega
          · omega
          · have : m * 2 ≤ m * (t + 1 + 1) := Nat.mul_le_mul_left m (by omega)
            omega
        · omega

/-- the Mersenne prime conjecture: Mersenne primes are unbounded -/
theorem mpc_iff : MersennePrimeConjecture ↔ ∀ N, ∃ m, N ≤ m ∧ MP m := by
  constructor
  · intro h N
    obtain ⟨k, hk, hp⟩ := h (N + 1)
    have hlt : k < 2 ^ k := Nat.lt_two_pow_self
    have := hp.two_le
    exact ⟨2 ^ k - 1, by omega, hp, k, by omega⟩
  · intro h n
    obtain ⟨m, hm, hp, k, hk⟩ := h (2 ^ n)
    refine ⟨k, ?_, by rw [show 2 ^ k - 1 = m by omega]; exact hp⟩
    apply Classical.byContradiction; intro hn
    have : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    omega

end TM.Mersenne
