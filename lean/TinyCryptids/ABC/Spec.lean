import TinyCryptids.Defs
import TinyCryptids.Core.BeepBoop

/-!
# Arithmetic for the abc machine

* `rstep a b c r d`: the machine's update of `R` at the trial divisor `d` (`R := R * d` when
  `d` shares a factor with `a`, `b` or `c` and `gcd(R, d) = 1`); from `R = 1` at `d = 2`, the
  updates up to `d = c` give `rad(abc)` (`rfrom_rad`).
* `val c r`: the least `n` with `c ^ n > r ^ (n + 1)` (the number of beeps of a passing pair),
  which exists when `r < c` (`val_spec`).
* `pairAt k`: the `k`-th pair `(a, c)` of the enumeration `c = 2, 3, …`, `a = 1, …, c - 1`.
* `good_iff`: some value of `val` occurs for infinitely many coprime pairs with
  `rad(abc) < c` iff the abc conjecture fails.
-/

namespace TM.ABC
open TinyCryptids

/-! ## primes -/

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

theorem exists_prime_dvd : ∀ d, 2 ≤ d → ∃ p, Prime p ∧ p ∣ d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro hd
    by_cases hp : Prime d
    · exact ⟨d, hp, Nat.dvd_refl d⟩
    · have : ∃ e, e < d ∧ 2 ≤ e ∧ d % e = 0 := by
        apply Classical.byContradiction; intro hne
        exact hp ⟨hd, fun e h1 h2 h3 => hne ⟨e, h1, h2, h3⟩⟩
      obtain ⟨e, h1, h2, h3⟩ := this
      obtain ⟨p, hp, hpe⟩ := ih e h1 h2
      exact ⟨p, hp, Nat.dvd_trans hpe (Nat.dvd_of_mod_eq_zero h3)⟩

/-- a prime divides one of two coprime-or-not numbers sharing a factor with it -/
theorem prime_gcd {d x : Nat} (hd : Prime d) : Nat.gcd x d ≠ 1 ↔ d ∣ x := by
  have hd2 := hd.1
  constructor
  · intro h
    have hg : Nat.gcd x d ∣ d := Nat.gcd_dvd_right x d
    rcases ((prime_iff_dvd d).1 hd).2 _ hg with h1 | h1
    · exact absurd h1 h
    · rw [← h1]; exact Nat.gcd_dvd_left x d
  · intro h h1
    have : d ∣ Nat.gcd x d := Nat.dvd_gcd h (Nat.dvd_refl d)
    rw [h1] at this
    have := Nat.le_of_dvd (by omega) this
    omega

/-- a number sharing a factor with `d` shares a prime factor with it -/
theorem gcd_prime {d x : Nat} (hd : 1 ≤ d) (h : Nat.gcd x d ≠ 1) : ∃ p, Prime p ∧ p ∣ x ∧ p ∣ d := by
  have hg0 : Nat.gcd x d ≠ 0 := by
    intro h0; have := (Nat.gcd_eq_zero_iff.1 h0).2; omega
  obtain ⟨p, hp, hpg⟩ := exists_prime_dvd (Nat.gcd x d) (by omega)
  exact ⟨p, hp, Nat.dvd_trans hpg (Nat.gcd_dvd_left x d), Nat.dvd_trans hpg (Nat.gcd_dvd_right x d)⟩

/-! ## `radBelow` -/

theorem radBelow_pos (n : Nat) : ∀ k, 1 ≤ radBelow n k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    have ih := radBelow_pos n k
    show 1 ≤ radBelow n k * (if Prime k ∧ n % k = 0 then k else 1)
    split
    · next h => have h2 := h.1.1; exact Nat.le_trans (by omega : 1 ≤ 1 * 1) (Nat.mul_le_mul ih (by omega))
    · omega

theorem dvd_radBelow {n p : Nat} (hp : Prime p) (hpn : p ∣ n) : ∀ k, p < k → p ∣ radBelow n k
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
    show p ∣ radBelow n k * (if Prime k ∧ n % k = 0 then k else 1)
    rcases Nat.lt_or_ge p k with h1 | h1
    · exact Nat.dvd_trans (dvd_radBelow hp hpn k h1) (Nat.dvd_mul_right _ _)
    · obtain rfl : p = k := by omega
      rw [if_pos ⟨hp, Nat.mod_eq_zero_of_dvd hpn⟩]
      exact Nat.dvd_mul_left _ _

theorem prime_dvd_radBelow {n p : Nat} (hp : Prime p) : ∀ k, p ∣ radBelow n k → p < k
  | 0, h => by
    have h' : p ∣ 1 := h
    have := Nat.le_of_dvd (by omega) h'; have := hp.1; omega
  | k + 1, h => by
    have h' : p ∣ radBelow n k * (if Prime k ∧ n % k = 0 then k else 1) := h
    rcases prime_dvd_mul hp h' with h1 | h1
    · have := prime_dvd_radBelow hp k h1; omega
    · split at h1
      · next hk =>
        rcases ((prime_iff_dvd k).1 hk.1).2 p h1 with e | e
        · have := hp.1; omega
        · omega
      · have := Nat.le_of_dvd (by omega) h1; have := hp.1; omega

/-- no new prime factor in `[k, m)`: `radBelow` is constant there -/
theorem radBelow_const {n k : Nat} (h : ∀ j, k ≤ j → ¬ (Prime j ∧ n % j = 0)) :
    ∀ m, k ≤ m → radBelow n m = radBelow n k := by
  intro m hm
  induction m with
  | zero => obtain rfl : k = 0 := by omega
            rfl
  | succ m ih =>
    rcases Nat.lt_or_ge m k with h1 | h1
    · obtain rfl : k = m + 1 := by omega
      rfl
    · show radBelow n m * (if Prime m ∧ n % m = 0 then m else 1) = _
      rw [if_neg (h m h1), Nat.mul_one, ih h1]

/-! ## the update of `R` -/

/-- `R := R * d` iff `d` shares a factor with `a`, `b` or `c` and none with `R` -/
def rstep (a b c r d : Nat) : Nat :=
  if (Nat.gcd a d ≠ 1 ∨ Nat.gcd b d ≠ 1 ∨ Nat.gcd c d ≠ 1) ∧ Nat.gcd r d = 1 then r * d else r

/-- the updates for `d, d + 1, …, d + k - 1` -/
def rfrom (a b c : Nat) : Nat → Nat → Nat → Nat
  | r, _, 0 => r
  | r, d, k + 1 => rfrom a b c (rstep a b c r d) (d + 1) k

theorem rstep_pos {a b c r d : Nat} (hr : 1 ≤ r) (hd : 1 ≤ d) : 1 ≤ rstep a b c r d := by
  unfold rstep; split
  · exact Nat.mul_le_mul hr hd
  · exact hr

theorem rstep_rad {a b c d : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 2 ≤ d) :
    rstep a b c (radBelow (a * b * c) d) d = radBelow (a * b * c) (d + 1) := by
  have hn : 1 ≤ a * b * c := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
  show _ = radBelow (a * b * c) d * (if Prime d ∧ (a * b * c) % d = 0 then d else 1)
  unfold rstep
  by_cases hp : Prime d
  · -- `d` prime: a hit iff `d ∣ abc`, and `d` does not divide the product of smaller primes
    have hR : Nat.gcd (radBelow (a * b * c) d) d = 1 := by
      apply Classical.byContradiction; intro h
      have := prime_dvd_radBelow hp d ((prime_gcd hp).1 h); omega
    have hit : (Nat.gcd a d ≠ 1 ∨ Nat.gcd b d ≠ 1 ∨ Nat.gcd c d ≠ 1) ↔ (a * b * c) % d = 0 := by
      rw [prime_gcd hp, prime_gcd hp, prime_gcd hp]
      constructor
      · rintro (h | h | h)
        · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h (Nat.dvd_trans (Nat.dvd_mul_right a b)
            (Nat.dvd_mul_right _ c)))
        · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h (Nat.dvd_trans (Nat.dvd_mul_left b a)
            (Nat.dvd_mul_right _ c)))
        · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h (Nat.dvd_mul_left c _))
      · intro h
        rcases prime_dvd_mul hp (Nat.dvd_of_mod_eq_zero h) with h1 | h1
        · rcases prime_dvd_mul hp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h1)
    by_cases h : (a * b * c) % d = 0
    · rw [if_pos ⟨hit.2 h, hR⟩, if_pos ⟨hp, h⟩]
    · rw [if_neg (fun h' => h (hit.1 h'.1)), if_neg (fun h' => h h'.2), Nat.mul_one]
  · -- `d` not prime: a hit has a smaller prime factor, already in `R`
    rw [if_neg (show ¬ (Prime d ∧ (a * b * c) % d = 0) from fun h => hp h.1), Nat.mul_one]
    rw [if_neg]
    rintro ⟨hh, hg⟩
    have key : ∀ x, x ∣ a * b * c → Nat.gcd x d ≠ 1 → False := by
      intro x hx h
      obtain ⟨p, pp, px, pd⟩ := gcd_prime (by omega) h
      have hpd : p < d := by
        have := Nat.le_of_dvd (by omega) pd
        rcases Nat.lt_or_ge p d with h1 | h1
        · exact h1
        · obtain rfl : p = d := by omega
          exact absurd pp hp
      have h1 := dvd_radBelow pp (Nat.dvd_trans px hx) d hpd
      have h2 : p ∣ Nat.gcd (radBelow (a * b * c) d) d := Nat.dvd_gcd h1 pd
      rw [hg] at h2
      have := Nat.le_of_dvd (by omega) h2; have := pp.1; omega
    rcases hh with h | h | h
    · exact key a (Nat.dvd_trans (Nat.dvd_mul_right a b) (Nat.dvd_mul_right _ c)) h
    · exact key b (Nat.dvd_trans (Nat.dvd_mul_left b a) (Nat.dvd_mul_right _ c)) h
    · exact key c (Nat.dvd_mul_left c _) h

theorem rfrom_radBelow {a b c : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ∀ k d, 2 ≤ d → rfrom a b c (radBelow (a * b * c) d) d k = radBelow (a * b * c) (d + k) := by
  intro k
  induction k with
  | zero => intro d _; rfl
  | succ k ih =>
    intro d hd
    show rfrom a b c (rstep a b c (radBelow (a * b * c) d) d) (d + 1) k = _
    rw [rstep_rad ha hb hc hd, ih (d + 1) (by omega), Nat.add_assoc, Nat.add_comm 1 k]

/-- from `R = 1` at `d = 2`, the updates for `d = 2, …, c` give `rad(abc)` -/
theorem rfrom_rad {a b c : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : a + b = c) :
    rfrom a b c 1 2 (c - 1) = rad (a * b * c) := by
  have h2 : radBelow (a * b * c) 2 = 1 := rfl
  have h3 := rfrom_radBelow (c := c) ha hb (by omega) (c - 1) 2 (Nat.le_refl 2)
  rw [h2] at h3
  rw [h3, show 2 + (c - 1) = c + 1 by omega]
  unfold rad
  -- no prime factor of `abc` is above `c`
  have hn : c + 1 ≤ a * b * c + 1 := by
    have : 1 ≤ a * b := Nat.mul_le_mul ha hb
    have := Nat.mul_le_mul this (Nat.le_refl c); omega
  refine (radBelow_const ?_ _ hn).symm
  rintro j hj ⟨hp, hj0⟩
  have hd := Nat.dvd_of_mod_eq_zero hj0
  have hle : ∀ x, 1 ≤ x → j ∣ x → j ≤ x := fun x hx h => Nat.le_of_dvd hx h
  rcases prime_dvd_mul hp hd with h1 | h1
  · rcases prime_dvd_mul hp h1 with h2 | h2
    · have := hle a ha h2; omega
    · have := hle b hb h2; omega
  · have := hle c (by omega) h1; omega

theorem rad_two_le {n : Nat} (hn : 2 ≤ n) : 2 ≤ rad n := by
  obtain ⟨p, hp, hpn⟩ := exists_prime_dvd n hn
  have hle := Nat.le_of_dvd (by omega) hpn
  have h1 := dvd_radBelow hp hpn (n + 1) (by omega)
  have := Nat.le_of_dvd (radBelow_pos n (n + 1)) h1
  have := hp.1
  unfold rad; omega

/-! ## coprimality: the machine tests `gcd(a, c)` and `gcd(b, c)` -/

theorem gcd_ac (a b : Nat) : Nat.gcd a (a + b) = Nat.gcd a b := by
  rw [Nat.gcd_rec, Nat.add_mod_left, ← Nat.gcd_rec]

theorem gcd_bc (a b : Nat) : Nat.gcd b (a + b) = Nat.gcd a b := by
  rw [Nat.gcd_rec, Nat.add_mod_right, ← Nat.gcd_rec, Nat.gcd_comm]

/-! ## the number of beeps -/

/-- `(r + 1)^n * r ≥ r^n * (r + n)` (Bernoulli) -/
theorem bern (r : Nat) : ∀ n, r ^ n * (r + n) ≤ (r + 1) ^ n * r
  | 0 => by simp
  | n + 1 => by
    have ih := bern r n
    rw [Nat.pow_succ, Nat.pow_succ]
    have h1 : r ^ n * r * (r + (n + 1)) ≤ r ^ n * (r + n) * (r + 1) := by
      rw [Nat.mul_assoc, Nat.mul_assoc]
      apply Nat.mul_le_mul (Nat.le_refl _)
      have e1 : r * (r + (n + 1)) = r * r + (r * n + r) := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      have e2 : (r + n) * (r + 1) = r * r + r + (r * n + n) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.mul_comm n r]
      rw [e1, e2]; omega
    have h2 : r ^ n * (r + n) * (r + 1) ≤ (r + 1) ^ n * r * (r + 1) := Nat.mul_le_mul ih (Nat.le_refl _)
    calc r ^ n * r * (r + (n + 1)) ≤ (r + 1) ^ n * r * (r + 1) := Nat.le_trans h1 h2
      _ = (r + 1) ^ n * (r + 1) * r := by rw [Nat.mul_assoc, Nat.mul_comm r, ← Nat.mul_assoc]

/-- `c > r ≥ 1`: `c ^ (r * r) > r ^ (r * r + 1)` -/
theorem pow_beat {c r : Nat} (hr : 1 ≤ r) (hrc : r < c) : r ^ (r * r + 1) < c ^ (r * r) := by
  have hb := bern r (r * r)
  have h1 : r ^ (r * r + 1) * r < r ^ (r * r) * (r + r * r) := by
    rw [Nat.pow_succ, Nat.mul_assoc]
    apply Nat.mul_lt_mul_of_pos_left _ (Nat.pos_pow_of_pos _ hr)
    have : 0 < r * r := Nat.mul_le_mul hr hr
    omega
  have h2 : (r + 1) ^ (r * r) ≤ c ^ (r * r) := Nat.pow_le_pow_left (by omega) _
  have h3 : r ^ (r * r + 1) * r < c ^ (r * r) * r :=
    Nat.lt_of_lt_of_le h1 (Nat.le_trans hb (Nat.mul_le_mul h2 (Nat.le_refl r)))
  exact Nat.lt_of_mul_lt_mul_right h3

/-- the search for the least `n` with `r ^ (n + 1) < c ^ n`, from `n`, with `f` more tries -/
def vAux (c r : Nat) : Nat → Nat → Nat
  | 0, n => n
  | f + 1, n => if r ^ (n + 1) < c ^ n then n else vAux c r f (n + 1)

/-- the number of beeps of a pair with `rad = r`: the least `n` with `c ^ n > r ^ (n + 1)` -/
def val (c r : Nat) : Nat := vAux c r (r * r) 0

theorem vAux_spec {c r N : Nat} (hN : r ^ (N + 1) < c ^ N) :
    ∀ f n, n ≤ N → N ≤ n + f → (∀ m, m < n → c ^ m ≤ r ^ (m + 1)) →
      r ^ (vAux c r f n + 1) < c ^ vAux c r f n ∧ ∀ m, m < vAux c r f n → c ^ m ≤ r ^ (m + 1) := by
  intro f
  induction f with
  | zero =>
    intro n h1 h2 h3
    obtain rfl : n = N := by omega
    exact ⟨hN, h3⟩
  | succ f ih =>
    intro n h1 h2 h3
    by_cases h : r ^ (n + 1) < c ^ n
    · have e : vAux c r (f + 1) n = n := by simp [vAux, h]
      rw [e]; exact ⟨h, h3⟩
    · have e : vAux c r (f + 1) n = vAux c r f (n + 1) := by simp [vAux, h]
      rw [e]
      have hnN : n ≠ N := by intro e; subst e; exact h hN
      refine ih (n + 1) (by omega) (by omega) ?_
      intro m hm
      rcases Nat.lt_or_ge m n with h4 | h4
      · exact h3 m h4
      · obtain rfl : m = n := by omega
        omega

theorem val_spec {c r : Nat} (hr : 1 ≤ r) (hrc : r < c) :
    r ^ (val c r + 1) < c ^ val c r ∧ ∀ m, m < val c r → c ^ m ≤ r ^ (m + 1) :=
  vAux_spec (pow_beat hr hrc) (r * r) 0 (Nat.zero_le _) (by omega) (fun m h => absurd h (Nat.not_lt_zero m))

/-! ## the enumeration of pairs -/

def nextPair (x : Nat × Nat) : Nat × Nat := if x.1 + 1 < x.2 then (x.1 + 1, x.2) else (1, x.2 + 1)

def pairAt : Nat → Nat × Nat
  | 0 => (1, 2)
  | k + 1 => nextPair (pairAt k)

theorem nextPair_spec {a c k : Nat} (h1 : 1 ≤ a) (h2 : a < c) (h3 : 2 * k + 3 * c = c * c + 2 * a) :
    1 ≤ (nextPair (a, c)).1 ∧ (nextPair (a, c)).1 < (nextPair (a, c)).2 ∧
      2 * (k + 1) + 3 * (nextPair (a, c)).2 = (nextPair (a, c)).2 * (nextPair (a, c)).2 + 2 * (nextPair (a, c)).1 := by
  by_cases h : a + 1 < c
  · rw [show nextPair (a, c) = (a + 1, c) by simp [nextPair, h]]
    show 1 ≤ a + 1 ∧ a + 1 < c ∧ 2 * (k + 1) + 3 * c = c * c + 2 * (a + 1)
    omega
  · rw [show nextPair (a, c) = (1, c + 1) by simp [nextPair, h]]
    show 1 ≤ 1 ∧ 1 < c + 1 ∧ 2 * (k + 1) + 3 * (c + 1) = (c + 1) * (c + 1) + 2 * 1
    obtain rfl : c = a + 1 := by omega
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at h3 ⊢
    omega

theorem pairAt_spec : ∀ k, 1 ≤ (pairAt k).1 ∧ (pairAt k).1 < (pairAt k).2 ∧
    2 * k + 3 * (pairAt k).2 = (pairAt k).2 * (pairAt k).2 + 2 * (pairAt k).1
  | 0 => by decide
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := pairAt_spec k
    show 1 ≤ (nextPair (pairAt k)).1 ∧ (nextPair (pairAt k)).1 < (nextPair (pairAt k)).2 ∧
      2 * (k + 1) + 3 * (nextPair (pairAt k)).2 = (nextPair (pairAt k)).2 * (nextPair (pairAt k)).2 +
        2 * (nextPair (pairAt k)).1
    generalize pairAt k = x at h1 h2 h3
    exact nextPair_spec h1 h2 h3

theorem pairAt_c_le (k : Nat) : (pairAt k).2 ≤ k + 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    show (nextPair (pairAt k)).2 ≤ k + 1 + 2
    unfold nextPair; split <;> simp only <;> omega

/-- every pair `1 ≤ a < c` occurs -/
theorem pairAt_onto : ∀ c, 2 ≤ c → ∀ a, 1 ≤ a → a < c → ∃ k, pairAt k = (a, c) := by
  intro c hc
  induction c, hc using Nat.le_induction with
  | base => intro a h1 h2; obtain rfl : a = 1 := by omega
            exact ⟨0, rfl⟩
  | succ c hc ih =>
    -- `(1, c + 1)` follows `(c - 1, c)`
    obtain ⟨k0, hk0⟩ := ih (c - 1) (by omega) (by omega)
    have base : pairAt (k0 + 1) = (1, c + 1) := by
      show nextPair (pairAt k0) = _
      rw [hk0]; simp only [nextPair]; rw [if_neg (by omega)]
    intro a h1 h2
    induction a, h1 using Nat.le_induction with
    | base => exact ⟨k0 + 1, base⟩
    | succ a ha iha =>
      obtain ⟨k, hk⟩ := iha (by omega)
      refine ⟨k + 1, ?_⟩
      show nextPair (pairAt k) = _
      rw [hk]; simp only [nextPair]; rw [if_pos (by omega)]

/-- a pair that is coprime and beats its radical: the machine's "good" segment -/
def Good (a c : Nat) : Prop := Nat.gcd a (c - a) = 1 ∧ rad (a * (c - a) * c) < c

/-- uniform bound for finitely many values -/
theorem bound_all {P : Nat → Nat → Prop} (hm : ∀ v K L, K ≤ L → P v K → P v L) :
    ∀ n, (∀ v, v ≤ n → ∃ K, P v K) → ∃ K, ∀ v, v ≤ n → P v K := by
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨K, hK⟩ := h 0 (Nat.le_refl 0)
    refine ⟨K, fun v hv => ?_⟩
    obtain rfl : v = 0 := by omega
    exact hK
  | succ n ih =>
    intro h
    obtain ⟨K1, hK1⟩ := ih (fun v hv => h v (by omega))
    obtain ⟨K2, hK2⟩ := h (n + 1) (Nat.le_refl _)
    refine ⟨K1 + K2, fun v hv => ?_⟩
    rcases Nat.lt_or_ge v (n + 1) with h1 | h1
    · exact hm v K1 _ (by omega) (hK1 v (by omega))
    · obtain rfl : v = n + 1 := by omega
      exact hm _ K2 _ (by omega) hK2

/-- some value of `val` repeats over infinitely many good pairs iff the abc conjecture fails -/
theorem good_iff :
    (∃ v, ∀ K, ∃ k, K ≤ k ∧ Good (pairAt k).1 (pairAt k).2 ∧
      val (pairAt k).2 (rad ((pairAt k).1 * ((pairAt k).2 - (pairAt k).1) * (pairAt k).2)) = v) ↔
    ¬ ABCConjecture := by
  constructor
  · rintro ⟨v, hv⟩ habc
    -- `v ≥ 1` (a good pair has `c ^ 0 = 1 ≤ rad`)
    obtain ⟨k0, -, hg0, hv0⟩ := hv 0
    have hv1 : 1 ≤ v := by
      obtain ⟨-, h2⟩ := hg0
      have hr : 1 ≤ rad ((pairAt k0).1 * ((pairAt k0).2 - (pairAt k0).1) * (pairAt k0).2) := radBelow_pos _ _
      have := (val_spec hr h2).1
      rw [hv0] at this
      rcases Nat.eq_zero_or_pos v with e | e
      · subst e; rw [Nat.pow_zero, Nat.zero_add, Nat.pow_one] at this; omega
      · exact e
    obtain ⟨N, hN⟩ := habc v hv1
    obtain ⟨k, hk, ⟨hg1, hg2⟩, hval⟩ := hv (N * N + 2 * N + 1)
    obtain ⟨h1, h2, h3⟩ := pairAt_spec k
    generalize pairAt k = x at hg1 hg2 hval h1 h2 h3
    obtain ⟨a, c⟩ := x
    simp only at hg1 hg2 hval h1 h2 h3
    have hcN : N ≤ c := by
      apply Classical.byContradiction; intro hlt
      have : c * c ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hab : a + (c - a) = c := by omega
    have := hN a (c - a) h1 (by omega) hg1 (by omega)
    rw [hab] at this
    have hr : 1 ≤ rad (a * (c - a) * c) := radBelow_pos _ _
    have := (val_spec hr hg2).1
    rw [hval] at this
    omega
  · intro habc
    -- some `n` with infinitely many triples beating `rad ^ ((n+1)/n)`
    have : ∃ n, 1 ≤ n ∧ ∀ N, ∃ a b, 1 ≤ a ∧ 1 ≤ b ∧ Nat.gcd a b = 1 ∧ N ≤ a + b ∧
        rad (a * b * (a + b)) ^ (n + 1) < (a + b) ^ n := by
      apply Classical.byContradiction; intro hne
      apply habc; intro n hn
      apply Classical.byContradiction; intro hN
      apply hne; refine ⟨n, hn, fun N => ?_⟩
      apply Classical.byContradiction; intro hab
      apply hN; refine ⟨N, fun a b ha hb hg hNab => ?_⟩
      apply Classical.byContradiction; intro hlt
      exact hab ⟨a, b, ha, hb, hg, hNab, by omega⟩
    obtain ⟨n, hn, hinf⟩ := this
    apply Classical.byContradiction; intro hno
    -- each value `v ≤ n` occurs only below some index
    have hb : ∀ v, v ≤ n → ∃ K, ∀ k, K ≤ k → ¬ (Good (pairAt k).1 (pairAt k).2 ∧
        val (pairAt k).2 (rad ((pairAt k).1 * ((pairAt k).2 - (pairAt k).1) * (pairAt k).2)) = v) := by
      intro v _
      apply Classical.byContradiction; intro h
      apply hno; refine ⟨v, fun K => ?_⟩
      apply Classical.byContradiction; intro h'
      apply h; refine ⟨K, fun k hk hgk => h' ⟨k, hk, hgk⟩⟩
    obtain ⟨K, hK⟩ := bound_all (fun v K L hKL h k hk => h k (by omega)) n hb
    obtain ⟨a, b, ha, hb1, hg, hab, hbeat⟩ := hinf (K + 2)
    obtain ⟨k, hk⟩ := pairAt_onto (a + b) (by omega) a ha (by omega)
    have hkK : K ≤ k := by have := pairAt_c_le k; rw [hk] at this; simp only at this; omega
    have hba : a + b - a = b := by omega
    have hr : 1 ≤ rad (a * b * (a + b)) := radBelow_pos _ _
    have hrc : rad (a * b * (a + b)) < a + b := by
      apply Classical.byContradiction; intro hle
      have h1 : (a + b) ^ n ≤ rad (a * b * (a + b)) ^ n := Nat.pow_le_pow_left (by omega) n
      have h2 : rad (a * b * (a + b)) ^ n ≤ rad (a * b * (a + b)) ^ (n + 1) :=
        Nat.pow_le_pow_right hr (by omega)
      omega
    have hvs := val_spec hr hrc
    have hvn : val (a + b) (rad (a * b * (a + b))) ≤ n := by
      apply Classical.byContradiction; intro h
      have := hvs.2 n (by omega); omega
    refine hK _ hvn k hkK ?_
    rw [hk]
    show (Nat.gcd a (a + b - a) = 1 ∧ rad (a * (a + b - a) * (a + b)) < a + b) ∧
      val (a + b) (rad (a * (a + b - a) * (a + b))) = _
    rw [hba]
    exact ⟨⟨hg, hrc⟩, rfl⟩

end TM.ABC
