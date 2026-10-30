import TinyCryptids.Defs

/-!
# Fermat's little theorem

(A copy of `../AgohGiuga/Fermat.lean`.)

`a ^ (p - 1) % p = 1` for a prime `p` and `0 < a < p`, from the binomial theorem
(`p ∣ choose p k` for `0 < k < p`, so `(a + 1) ^ p ≡ a ^ p + 1`).
-/

namespace TM.WallSunSun2
open TinyCryptids

/-- Euclid's lemma -/
theorem prime_dvd_mul {p a b : Nat} (hp : Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  have hpos : 0 < p := by have := hp.1; omega
  have hg : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  by_cases h1 : Nat.gcd p a = 1
  · right
    have : p ∣ Nat.gcd (a * b) (p * b) := Nat.dvd_gcd h (Nat.dvd_mul_right p b)
    rwa [Nat.gcd_mul_right, Nat.gcd_comm, h1, Nat.one_mul] at this
  · left
    have g1 : 1 ≤ Nat.gcd p a := Nat.gcd_pos_of_pos_left a hpos
    have g2 : Nat.gcd p a ≤ p := Nat.le_of_dvd hpos hg
    have hgp : Nat.gcd p a = p := by
      refine Classical.byContradiction fun hne => ?_
      exact hp.2 (Nat.gcd p a) (by omega) (by omega) (Nat.mod_eq_zero_of_dvd hg)
    rw [← hgp]; exact Nat.gcd_dvd_right p a

theorem choose_lt : ∀ n k, n < k → choose n k = 0
  | 0, k + 1, _ => rfl
  | n + 1, k + 1, h => by
    show choose n k + choose n (k + 1) = 0
    rw [choose_lt n k (by omega), choose_lt n (k + 1) (by omega)]

theorem choose_self : ∀ n, choose n n = 1
  | 0 => rfl
  | n + 1 => by
    show choose n n + choose n (n + 1) = 1
    rw [choose_self n, choose_lt n (n + 1) (by omega)]

theorem choose_mul : ∀ n k, choose (n + 1) (k + 1) * (k + 1) = (n + 1) * choose n k
  | 0, 0 => rfl
  | 0, k + 1 => by
    show (choose 0 (k + 1) + choose 0 (k + 2)) * (k + 2) = 1 * choose 0 (k + 1)
    rw [choose_lt 0 (k + 1) (by omega), choose_lt 0 (k + 2) (by omega)]; simp
  | n + 1, 0 => by
    show (choose (n + 1) 0 + choose (n + 1) 1) * 1 = (n + 2) * choose (n + 1) 0
    have h := choose_mul n 0
    have e : choose (n + 1) 0 = 1 := rfl
    have e0 : choose n 0 = 1 := by cases n <;> rfl
    rw [e0, Nat.mul_one, Nat.mul_one] at h
    rw [e, Nat.mul_one, Nat.mul_one, h]; omega
  | n + 1, k + 1 => by
    show (choose (n + 1) (k + 1) + choose (n + 1) (k + 2)) * (k + 2) = (n + 2) * choose (n + 1) (k + 1)
    have h1 := choose_mul n k
    have h2 := choose_mul n (k + 1)
    have e : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl
    generalize choose (n + 1) (k + 1) = X at *
    generalize choose (n + 1) (k + 2) = Y at *
    generalize choose n k = A at *
    generalize choose n (k + 1) = B at *
    calc (X + Y) * (k + 2) = X * (k + 1) + X + Y * (k + 2) := by
          rw [Nat.add_mul, show k + 2 = (k + 1) + 1 from rfl, Nat.mul_succ X (k + 1)]
      _ = (n + 1) * A + X + (n + 1) * B := by rw [h1, h2]
      _ = (n + 1) * (A + B) + X := by rw [Nat.mul_add]; omega
      _ = (n + 2) * X := by rw [← e, Nat.succ_mul (n + 1) X]

theorem prime_dvd_choose {p k : Nat} (hp : Prime p) (h0 : 0 < k) (hk : k < p) : p ∣ choose p k := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := choose_mul m j
  have hd : m + 1 ∣ choose (m + 1) (j + 1) * (j + 1) := by rw [h]; exact Nat.dvd_mul_right _ _
  rcases prime_dvd_mul hp hd with h | h
  · exact h
  · have := Nat.le_of_dvd (by omega) h; omega

/-- `f 0 + … + f (n - 1)` -/
def ssum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ssum f n + f n

theorem ssum_add (f g : Nat → Nat) : ∀ n, ssum (fun k => f k + g k) n = ssum f n + ssum g n
  | 0 => rfl
  | n + 1 => by simp only [ssum, ssum_add f g n]; omega

theorem ssum_mul (c : Nat) (f : Nat → Nat) : ∀ n, ssum (fun k => f k * c) n = ssum f n * c
  | 0 => by simp [ssum]
  | n + 1 => by simp only [ssum, ssum_mul c f n, Nat.add_mul]

theorem ssum_shift (f : Nat → Nat) : ∀ n, ssum f (n + 1) = f 0 + ssum (fun k => f (k + 1)) n
  | 0 => by simp [ssum]
  | n + 1 => by
    show ssum f (n + 1) + f (n + 1) = f 0 + (ssum (fun k => f (k + 1)) n + f (n + 1))
    rw [ssum_shift f n]; omega

theorem ssum_ext {f g : Nat → Nat} : ∀ n, (∀ k, k < n → f k = g k) → ssum f n = ssum g n
  | 0, _ => rfl
  | n + 1, h => by
    show ssum f n + f n = ssum g n + g n
    rw [ssum_ext n (fun k hk => h k (by omega)), h n (by omega)]

theorem dvd_ssum {d : Nat} {f : Nat → Nat} : ∀ n, (∀ k, k < n → d ∣ f k) → d ∣ ssum f n
  | 0, _ => Nat.dvd_zero d
  | n + 1, h => Nat.dvd_add (dvd_ssum n (fun k hk => h k (by omega))) (h n (by omega))

/-- the binomial theorem for `(a + 1) ^ n` -/
theorem binom (a : Nat) : ∀ n, (a + 1) ^ n = ssum (fun k => choose n k * a ^ k) (n + 1)
  | 0 => by simp [ssum, choose]
  | n + 1 => by
    have e0 : choose n 0 = 1 := by cases n <;> rfl
    have hS := ssum_shift (fun k => choose n k * a ^ k) (n + 1)
    have e3 : ssum (fun k => choose n k * a ^ k) (n + 2) =
        ssum (fun k => choose n k * a ^ k) (n + 1) := by
      show ssum (fun k => choose n k * a ^ k) (n + 1) + choose n (n + 1) * a ^ (n + 1) = _
      rw [choose_lt n (n + 1) (by omega), Nat.zero_mul, Nat.add_zero]
    rw [e3] at hS
    simp only [e0, Nat.pow_zero, Nat.mul_one] at hS
    have e1 : ssum (fun k => choose (n + 1) (k + 1) * a ^ (k + 1)) (n + 1) =
        ssum (fun k => choose n k * a ^ k * a + choose n (k + 1) * a ^ (k + 1)) (n + 1) :=
      ssum_ext _ (fun k _ => by
        show (choose n k + choose n (k + 1)) * a ^ (k + 1) = _
        rw [Nat.add_mul, Nat.pow_succ, Nat.mul_assoc])
    rw [ssum_add, ssum_mul] at e1
    have hR := ssum_shift (fun k => choose (n + 1) k * a ^ k) (n + 1)
    simp only [show choose (n + 1) 0 = 1 from rfl, Nat.pow_zero, Nat.mul_one] at hR
    rw [Nat.pow_succ, binom a n, hR, e1, Nat.mul_add, Nat.mul_one]
    omega

theorem pow_add_one_mod {p : Nat} (hp : Prime p) (a : Nat) : (a + 1) ^ p % p = (a ^ p + 1) % p := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.1; omega⟩
  have hb := binom a (m + 1)
  have hs : ssum (fun k => choose (m + 1) k * a ^ k) (m + 1 + 1) =
      ssum (fun k => choose (m + 1) k * a ^ k) (m + 1) + choose (m + 1) (m + 1) * a ^ (m + 1) := rfl
  rw [hs, ssum_shift, choose_self, show choose (m + 1) 0 = 1 from rfl] at hb
  simp only [Nat.pow_zero, Nat.mul_one, Nat.one_mul] at hb
  have hM : m + 1 ∣ ssum (fun k => choose (m + 1) (k + 1) * a ^ (k + 1)) m :=
    dvd_ssum m (fun k hk => Nat.dvd_trans (prime_dvd_choose (hm ▸ hp) (by omega) (by omega))
      (Nat.dvd_mul_right _ _))
  obtain ⟨c, hc⟩ := hM
  rw [hm, hb, hc]
  rw [show 1 + (m + 1) * c + a ^ (m + 1) = a ^ (m + 1) + 1 + (m + 1) * c by omega,
    Nat.add_mul_mod_self_left]

theorem pow_prime_mod {p : Nat} (hp : Prime p) : ∀ a, a ^ p % p = a % p
  | 0 => by rw [Nat.zero_pow (by have := hp.1; omega)]
  | a + 1 => by
    rw [pow_add_one_mod hp, Nat.add_mod, pow_prime_mod hp a, ← Nat.add_mod]

/-- **Fermat's little theorem** -/
theorem fermat {p a : Nat} (hp : Prime p) (h0 : 0 < a) (ha : a < p) : a ^ (p - 1) % p = 1 := by
  have h2 := hp.1
  have hpow : 1 ≤ a ^ (p - 1) := Nat.pos_pow_of_pos _ h0
  have e : a ^ p = a * a ^ (p - 1) := by
    rw [show p = (p - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]; simp
  have hm := pow_prime_mod hp a
  have hle : a ≤ a ^ p := by rw [e]; exact Nat.le_mul_of_pos_right a hpow
  have hd : p ∣ a ^ p - a := by
    have h1 := Nat.mod_add_div (a ^ p) p
    have h2 := Nat.mod_add_div a p
    rw [hm] at h1
    rw [show a ^ p - a = p * (a ^ p / p) - p * (a / p) by omega]
    exact Nat.dvd_sub (by omega) (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)
  rw [e, show a * a ^ (p - 1) - a = a * (a ^ (p - 1) - 1) by rw [Nat.mul_sub_one]] at hd
  rcases prime_dvd_mul hp hd with h | h
  · have := Nat.le_of_dvd h0 h; omega
  · have h3 := Nat.mod_eq_zero_of_dvd h
    have : a ^ (p - 1) = (a ^ (p - 1) - 1) + 1 := by omega
    rw [this, Nat.add_mod, h3, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

end TM.WallSunSun2
