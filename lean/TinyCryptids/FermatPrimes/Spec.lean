import TinyCryptids.Defs

/-!
# Arithmetic for the Fermat prime machine

* `Good m e`: the trial divisor `e` divides neither `m` nor `m - 1`.
* `FP m`: `m` is prime and `m - 1` is a power of 2 (a "pass" of the machine).
* `prime_pow_two_add_one`: if `2 ^ k + 1` is prime and `k ≥ 1`, then `k` is a power of 2.
* `fp_iff`: for odd `m ≥ 7`, `FP m` iff every odd `e` with `3 ≤ e ≤ m - 4` is good.
* `fp_small`: the passes `7 ≤ m ≤ 65537` are 17, 257 and 65537.
* `fp_big_iff`: some Fermat number `2 ^ 2 ^ n + 1` with `n ≥ 5` is prime iff some `m > 65537`
  passes.
-/

namespace TM.FermatPrimes

open TinyCryptids

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

def Good (m e : Nat) : Prop := m % e ≠ 0 ∧ (m - 1) % e ≠ 0

/-- `m` is prime and `m - 1` is a power of 2 -/
def FP (m : Nat) : Prop := Prime m ∧ ∃ k, m = 2 ^ k + 1

theorem sq_sub_one (a : Nat) : (a + 1) * (a - 1) = a ^ 2 - 1 := by
  rcases a with _ | b
  · simp
  · rw [Nat.pow_two, show b + 1 - 1 = b by omega]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

/-- `a + 1` divides `a ^ q + 1` for odd `q` -/
theorem dvd_pow_odd_add_one (a : Nat) : ∀ t, a + 1 ∣ a ^ (2 * t + 1) + 1 := by
  intro t
  induction t with
  | zero => show a + 1 ∣ a ^ 1 + 1; rw [Nat.pow_one]; exact Nat.dvd_refl _
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    rw [show 2 * (t + 1) + 1 = 2 + (2 * t + 1) by omega, Nat.pow_add]
    generalize a ^ (2 * t + 1) = X at hc ⊢
    rcases a with _ | b
    · simp
    · refine ⟨(b + 1) ^ 2 * c - b, ?_⟩
      have h1 : (b + 1 + 1) * ((b + 1) ^ 2 * c) = (b + 1) ^ 2 * X + (b + 1) ^ 2 := by
        rw [Nat.mul_left_comm, ← hc, Nat.mul_add, Nat.mul_one]
      have h2 := sq_sub_one (b + 1)
      rw [show b + 1 - 1 = b by omega] at h2
      have h3 : 1 ≤ (b + 1) ^ 2 := Nat.pos_pow_of_pos 2 (Nat.succ_pos b)
      have h4 : (b + 1 + 1) * b ≤ (b + 1 + 1) * ((b + 1) ^ 2 * c) := by
        rw [h1, h2]; omega
      rw [Nat.mul_sub_left_distrib, h1, h2]
      omega

/-- `2 ^ k + 1` prime with `k ≥ 1` forces `k` to be a power of 2 -/
theorem prime_pow_two_add_one (k : Nat) (hk : 1 ≤ k) (h : Prime (2 ^ k + 1)) : ∃ n, k = 2 ^ n := by
  refine pow2_of_no_odd k hk fun q hq h3 ⟨j, hj⟩ => ?_
  obtain ⟨t, rfl⟩ : ∃ t, q = 2 * t + 1 := ⟨q / 2, by omega⟩
  have hj1 : 1 ≤ j := by rcases j with _ | j <;> simp_all
  have hd := dvd_pow_odd_add_one (2 ^ j) t
  rw [← Nat.pow_mul, Nat.mul_comm, ← hj] at hd
  rcases ((prime_iff_dvd _).1 h).2 _ hd with h1 | h1
  · have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  · have : j < k := by
      rw [hj]
      have h5 : (2 * t + 1) * j = 2 * (t * j) + j := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      have h6 : 1 * j ≤ t * j := Nat.mul_le_mul_right j (by omega)
      omega
    have := Nat.pow_lt_pow_of_lt (show 1 < 2 by decide) this
    omega

theorem fp_iff (m : Nat) (hm : 7 ≤ m) (ho : m % 2 = 1) :
    FP m ↔ ∀ e, 3 ≤ e → e + 4 ≤ m → e % 2 = 1 → Good m e := by
  constructor
  · rintro ⟨⟨_, hp⟩, k, hk⟩ e h1 h2 h3
    refine ⟨hp e (by omega) (by omega), fun h0 => odd_not_dvd_pow2 e h3 h1 k ?_⟩
    rw [show 2 ^ k = m - 1 by omega]; exact Nat.dvd_of_mod_eq_zero h0
  · intro h
    refine ⟨⟨by omega, fun d hd h2 hz => ?_⟩, ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one d with he | he
      · obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hz
        have : m % 2 = 0 := by rw [ht, Nat.mul_mod, he]; simp
        omega
      · rcases Nat.lt_or_ge (d + 4) (m + 1) with hl | hl
        · exact (h d (by omega) (by omega) he).1 hz
        · -- d = m - 2
          rw [Nat.mod_eq_sub_mod (by omega : d ≤ m), show m - d = 2 by omega,
            Nat.mod_eq_of_lt (by omega : 2 < d)] at hz
          omega
    · obtain ⟨k, hk⟩ := pow2_of_no_odd (m - 1) (by omega) fun q hq h3 hd => by
        have hle := Nat.le_of_dvd (by omega) hd
        rcases Nat.lt_or_ge (q + 4) (m + 1) with hl | hl
        · exact (h q h3 (by omega) hq).2 (Nat.mod_eq_zero_of_dvd hd)
        · obtain rfl : q = m - 2 := by omega
          have : m - 2 ∣ m - 1 - (m - 2) := Nat.dvd_sub (by omega) hd (Nat.dvd_refl _)
          rw [show m - 1 - (m - 2) = 1 by omega] at this
          have := Nat.le_of_dvd (by omega) this
          omega
      exact ⟨k, by omega⟩

/-- the range the machine tests: odd `e` with `3 ≤ e ≤ m - 2` -/
theorem fp_iff' (m : Nat) (hm : 5 ≤ m) (ho : m % 2 = 1) :
    FP m ↔ ∀ e, 3 ≤ e → e + 2 ≤ m → e % 2 = 1 → Good m e := by
  constructor
  · rintro ⟨⟨_, hp⟩, k, hk⟩ e h1 h2 h3
    refine ⟨hp e (by omega) (by omega), fun h0 => odd_not_dvd_pow2 e h3 h1 k ?_⟩
    rw [show 2 ^ k = m - 1 by omega]; exact Nat.dvd_of_mod_eq_zero h0
  · intro h
    refine ⟨⟨by omega, fun d hd h2 hz => ?_⟩, ?_⟩
    · rcases Nat.mod_two_eq_zero_or_one d with he | he
      · obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hz
        have : m % 2 = 0 := by rw [ht, Nat.mul_mod, he]; simp
        omega
      · exact (h d (by omega) (by omega) he).1 hz
    · obtain ⟨k, hk⟩ := pow2_of_no_odd (m - 1) (by omega) fun q hq h3 hd => by
        have hle := Nat.le_of_dvd (by omega) hd
        exact (h q h3 (by omega) hq).2 (Nat.mod_eq_zero_of_dvd hd)
      exact ⟨k, by omega⟩

/-- primality from trial division up to `b` with `p < b * b` -/
theorem prime_of_lt (p b : Nat) (h2 : 2 ≤ p) (hb : p < b * b)
    (h : ∀ d, d < b → 2 ≤ d → p % d ≠ 0) : Prime p := by
  refine ⟨h2, fun d hd h2d hz => ?_⟩
  rcases Nat.lt_or_ge d b with hl | hl
  · exact h d hl h2d hz
  · obtain ⟨e, he⟩ := Nat.dvd_of_mod_eq_zero hz
    have he1 : 2 ≤ e := by
      rcases e with _ | _ | e
      · omega
      · omega
      · omega
    have heb : e < b := by
      apply Classical.byContradiction; intro hn
      have : b * b ≤ d * e := Nat.mul_le_mul hl (by omega)
      omega
    exact h e heb he1 (Nat.mod_eq_zero_of_dvd ⟨d, by rw [he, Nat.mul_comm]⟩)

theorem prime_17 : Prime 17 := prime_of_lt 17 5 (by decide) (by decide) (by decide)
theorem prime_257 : Prime 257 := prime_of_lt 257 17 (by decide) (by decide) (by decide)
set_option maxRecDepth 100000 in
theorem prime_65537 : Prime 65537 := prime_of_lt 65537 257 (by decide) (by decide) (by decide)

/-- the passes up to 65537 (beyond 5) are 17, 257 and 65537 -/
theorem fp_small (m : Nat) (h7 : 7 ≤ m) (hm : m ≤ 65537) :
    FP m ↔ m = 17 ∨ m = 257 ∨ m = 65537 := by
  constructor
  · rintro ⟨hp, k, rfl⟩
    have hk1 : 1 ≤ k := by rcases k with _ | k <;> simp_all
    obtain ⟨n, rfl⟩ := prime_pow_two_add_one k hk1 hp
    have hn : n ≤ 4 := by
      apply Classical.byContradiction; intro hn
      have h1 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ 2 ^ 5 ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by decide) h1
      have : 2 ^ 2 ^ 5 = 4294967296 := by decide
      omega
    obtain _ | _ | _ | _ | _ | n := n
    · simp at h7
    · simp at h7
    · simp
    · simp
    · simp
    · omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨prime_17, 4, rfl⟩
    · exact ⟨prime_257, 8, rfl⟩
    · exact ⟨prime_65537, 16, rfl⟩

/-- the statement: some Fermat number `2 ^ 2 ^ n + 1` with `n ≥ 5` is prime iff some
`m > 65537` passes -/
theorem fp_big_iff : (∃ n, 5 ≤ n ∧ Prime (2 ^ 2 ^ n + 1)) ↔ ∃ m, 65537 < m ∧ FP m := by
  constructor
  · rintro ⟨n, hn, hp⟩
    have h1 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    have h2 : 2 ^ 2 ^ 5 ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by decide) h1
    have : 2 ^ 2 ^ 5 = 4294967296 := by decide
    exact ⟨_, by omega, hp, _, rfl⟩
  · rintro ⟨m, hm, hp, k, rfl⟩
    have hk1 : 1 ≤ k := by rcases k with _ | k <;> simp_all
    obtain ⟨n, rfl⟩ := prime_pow_two_add_one k hk1 hp
    refine ⟨n, ?_, hp⟩
    apply Classical.byContradiction; intro hn
    have h1 : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 2 ^ n ≤ 2 ^ 2 ^ 4 := Nat.pow_le_pow_right (by decide) h1
    have : 2 ^ 2 ^ 4 = 65536 := by decide
    omega

theorem fp_5 : FP 5 := ⟨prime_of_lt 5 3 (by decide) (by decide) (by decide), 2, rfl⟩

theorem FP.odd {m : Nat} (h : FP m) (h3 : 3 ≤ m) : m % 2 = 1 := by
  have := h.1.2 2 (by omega) (Nat.le_refl _)
  omega

end TM.FermatPrimes
