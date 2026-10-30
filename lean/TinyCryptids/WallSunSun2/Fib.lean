import TinyCryptids.WallSunSun2.Fermat

/-!
# Fibonacci divisibility

* `fib_add`, `fib_dvd_mul`, `fib_succ_coprime`: the addition formula, `F m ∣ F (m t)`, and
  that no prime divides two consecutive Fibonacci numbers.
* `rank_dvd`: if `z` is the least `z ≥ 1` with `q ∣ F z`, then `q ∣ F n → z ∣ n`.
* `lift`: `F (z (t + 1)) ≡ (t + 1) F z F (z - 1) ^ t (mod F z ^ 2)`, so
  `sq_of_sq`: `q² ∣ F k` with `q ∤ k` gives `q² ∣ F z`.
-/

namespace TM.WallSunSun2
open TinyCryptids

theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

theorem dvd_of_add_dvd {q a b : Nat} (h : q ∣ a + b) (hb : q ∣ b) : q ∣ a := by
  exact (Nat.dvd_add_iff_left hb).mpr h

/-- the addition formula -/
theorem fib_add (m : Nat) : ∀ n, fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n
  | 0 => by simp [fib]
  | 1 => by
    show fib (m + 2) = fib (m + 1) * 1 + fib m * 1
    rw [fib_add_two]; omega
  | n + 2 => by
    have h1 := fib_add m n
    have h2 := fib_add m (n + 1)
    rw [show m + (n + 2) + 1 = (m + n + 1) + 2 by omega, fib_add_two, h1,
      show m + n + 1 + 1 = m + (n + 1) + 1 by omega, h2,
      show n + 2 + 1 = (n + 1) + 2 by omega, fib_add_two (n + 1), fib_add_two n]
    simp only [Nat.mul_add]; omega

theorem fib_dvd_mul (m : Nat) : ∀ t, fib m ∣ fib (m * t)
  | 0 => by rw [Nat.mul_zero]; exact Nat.dvd_zero _
  | t + 1 => by
    cases m with
    | zero => rw [Nat.zero_mul]; exact Nat.dvd_refl _
    | succ s =>
      rw [show (s + 1) * (t + 1) = (s + 1) * t + s + 1 by rw [Nat.mul_succ]; omega, fib_add]
      exact Nat.dvd_add (Nat.dvd_mul_left _ _)
        (Nat.dvd_trans (fib_dvd_mul (s + 1) t) (Nat.dvd_mul_right _ _))

theorem fib_dvd_of_dvd {m n : Nat} (h : m ∣ n) : fib m ∣ fib n := by
  obtain ⟨t, rfl⟩ := h; exact fib_dvd_mul m t

/-- a prime divides no two consecutive Fibonacci numbers -/
theorem fib_succ_coprime {q : Nat} (hq : Prime q) : ∀ n, q ∣ fib n → q ∣ fib (n + 1) → False
  | 0, _, h => by have h' : q ∣ 1 := h; have := Nat.le_of_dvd (by decide) h'; have := hq.1; omega
  | n + 1, h1, h2 => by
    rw [fib_add_two] at h2
    exact fib_succ_coprime hq n (dvd_of_add_dvd h2 h1) h1

theorem prime_dvd_pow {q : Nat} (hq : Prime q) (b : Nat) : ∀ t, q ∣ b ^ t → q ∣ b
  | 0, h => by rw [Nat.pow_zero] at h; have := Nat.le_of_dvd (by decide) h; have := hq.1; omega
  | t + 1, h => by
    rw [Nat.pow_succ] at h
    rcases prime_dvd_mul hq h with h | h
    · exact prime_dvd_pow hq b t h
    · exact h

/-- a least element -/
theorem exists_least (P : Nat → Prop) : ∀ n, P n → ∃ z, P z ∧ ∀ y, y < z → ¬ P y := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases h : ∃ y, y < n ∧ P y
    · obtain ⟨y, hy, hp⟩ := h; exact ih y hy hp
    · exact ⟨n, hn, fun y hy hp => h ⟨y, hy, hp⟩⟩

/-- `z` is the rank of apparition of `q` -/
def Rank (q z : Nat) : Prop := 1 ≤ z ∧ q ∣ fib z ∧ ∀ y, y < z → 1 ≤ y → ¬ q ∣ fib y

theorem rank_exists {q n : Nat} (hn : 1 ≤ n) (h : q ∣ fib n) : ∃ z, Rank q z := by
  obtain ⟨z, ⟨h1, h2⟩, h3⟩ := exists_least (fun y => 1 ≤ y ∧ q ∣ fib y) n ⟨hn, h⟩
  exact ⟨z, h1, h2, fun y hy hy1 hd => h3 y hy ⟨hy1, hd⟩⟩

theorem rank_dvd {q z n : Nat} (hq : Prime q) (hz : Rank q z) (h : q ∣ fib n) : z ∣ n := by
  obtain ⟨hz1, hzq, hmin⟩ := hz
  have e := Nat.div_add_mod n z
  generalize n / z = t at e
  have hr := Nat.mod_lt n (show z > 0 by omega)
  generalize n % z = r at e hr
  subst e
  rcases r with _ | r
  · exact Nat.dvd_mul_right z t
  · exfalso
    rw [show z * t + (r + 1) = z * t + r + 1 by omega, fib_add] at h
    have hzt : q ∣ fib (z * t) := Nat.dvd_trans hzq (fib_dvd_mul z t)
    have h' : q ∣ fib (z * t + 1) * fib (r + 1) :=
      dvd_of_add_dvd h (Nat.dvd_trans hzt (Nat.dvd_mul_right _ _))
    rcases prime_dvd_mul hq h' with h | h
    · exact fib_succ_coprime hq _ hzt h
    · exact hmin (r + 1) hr (by omega) h

theorem i_two_mul (a : Int) : 2 * a = a + a := by omega
theorem i_mul_two (a : Int) : a * 2 = a + a := by omega

/-- ring normalization by AC-rewriting, then `omega` on the products as atoms -/
macro "ring_z" : tactic => `(tactic| (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul] <;> omega))
/-- the same, using the hypotheses too -/
macro "ring_z'" : tactic => `(tactic| (simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_neg, Int.neg_mul, Int.neg_neg, i_two_mul, i_mul_two, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_one, Int.one_mul] at * <;> omega))
macro "ring_n" : tactic => `(tactic| (simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_one, Nat.one_mul] <;> omega))

/-- `u t = F (z t + s)`, `v t = F (z t + s + 1)` with `z = s + 1`, `a = F z`, `b = F s`:
`u t ≡ b ^ (t + 1) (mod a)` and `v t ≡ (t + 1) a b ^ t (mod a²)` -/
theorem lift (s : Nat) : ∀ t,
    ((fib (s + 1) : Int) ∣ (fib ((s + 1) * t + s) : Int) - (fib s : Int) ^ t * fib s) ∧
    ((fib (s + 1) : Int) * fib (s + 1) ∣
      (fib ((s + 1) * t + s + 1) : Int) - ((t : Int) + 1) * fib (s + 1) * (fib s : Int) ^ t)
  | 0 => by
    simp only [Int.pow_zero, Int.one_mul, Int.mul_one, Int.sub_self, Nat.mul_zero, Nat.zero_add,
      Int.natCast_zero, Int.zero_add]
    exact ⟨Int.dvd_zero _, Int.dvd_zero _⟩
  | t + 1 => by
    obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := lift s t
    have eu : fib ((s + 1) * (t + 1) + s) = fib ((s + 1) * t + s + 1) * fib (s + 1) +
        fib ((s + 1) * t + s) * fib s := by
      rw [show (s + 1) * (t + 1) + s = ((s + 1) * t + s) + s + 1 by rw [Nat.mul_succ]; omega, fib_add]
    have ev : fib ((s + 1) * (t + 1) + s + 1) = (fib ((s + 1) * t + s) + fib ((s + 1) * t + s + 1)) *
        fib (s + 1) + fib ((s + 1) * t + s + 1) * fib s := by
      rw [show (s + 1) * (t + 1) + s + 1 = ((s + 1) * t + s + 1) + s + 1 by rw [Nat.mul_succ]; omega,
        fib_add, show (s + 1) * t + s + 1 + 1 = (s + 1) * t + s + 2 by omega, fib_add_two]
    rw [eu, ev]
    simp only [Int.natCast_add, Int.natCast_mul, Int.pow_succ, Int.natCast_one]
    generalize (fib ((s + 1) * t + s) : Int) = u at hX hY ⊢
    generalize (fib ((s + 1) * t + s + 1) : Int) = v at hX hY ⊢
    generalize (fib (s + 1) : Int) = a at hX hY ⊢
    generalize (fib s : Int) = b at hX hY ⊢
    generalize (b ^ t : Int) = B at hX hY ⊢
    generalize (t : Int) = T at hY ⊢
    have hu : u = B * b + a * X := by omega
    have hv : v = (T + 1) * a * B + a * a * Y := by omega
    subst hu hv
    constructor
    · exact ⟨(T + 1) * a * B + a * a * Y + b * X, by ring_z⟩
    · exact ⟨X + (T + 1) * B + a * Y + b * Y, by ring_z⟩

/-- **lifting**: if `q² ∣ F k` and `q ∤ k`, then `q²` divides `F` of the rank of `q` -/
theorem sq_of_sq {q z k : Nat} (hq : Prime q) (hz : Rank q z) (hk : q * q ∣ fib k) (hqk : ¬ q ∣ k) :
    q * q ∣ fib z := by
  have hq2 := hq.1
  have hzk := rank_dvd hq hz (Nat.dvd_trans (Nat.dvd_mul_right q q) hk)
  obtain ⟨j, rfl⟩ := hzk
  obtain ⟨s, rfl⟩ : ∃ s, z = s + 1 := ⟨z - 1, by have := hz.1; omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by
    rcases j with _ | j
    · exact absurd (Nat.dvd_zero q) (by simpa using hqk)
    · omega⟩
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨a', ha⟩ := hz.2.1
  have hv := (lift s t).2
  rw [show (s + 1) * t + s + 1 = (s + 1) * (t + 1) by rw [Nat.mul_succ]; omega] at hv
  -- q² ∣ (t + 1) a b^t
  have h1 : ((q * q : Nat) : Int) ∣ ((t : Int) + 1) * fib (s + 1) * (fib s : Int) ^ t := by
    have hk' : ((q * q : Nat) : Int) ∣ (fib ((s + 1) * (t + 1)) : Int) := Int.ofNat_dvd.mpr hk
    have ha' : ((q * q : Nat) : Int) ∣ (fib (s + 1) : Int) * fib (s + 1) := by
      rw [ha]; exact Int.ofNat_dvd.mpr (Nat.mul_dvd_mul (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _))
    have := Int.dvd_sub hk' (Int.dvd_trans ha' hv)
    rwa [Int.sub_sub_self] at this
  have h2 : q * q ∣ q * ((t + 1) * a' * fib s ^ t) := by
    have e : ((t : Int) + 1) * fib (s + 1) * (fib s : Int) ^ t = ((q * ((t + 1) * a' * fib s ^ t) : Nat) : Int) := by
      rw [ha]; simp only [Int.natCast_mul, Int.natCast_pow, Int.natCast_add, Int.natCast_one,
        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e] at h1; exact Int.ofNat_dvd.mp h1
  have h3 := Nat.dvd_of_mul_dvd_mul_left (by omega) h2
  rcases prime_dvd_mul hq h3 with h | h
  · rcases prime_dvd_mul hq h with h | h
    · exact hqk (Nat.dvd_trans h (Nat.dvd_mul_left _ _))
    · exact hn (by rw [ha]; exact Nat.mul_dvd_mul_left q h)
  · exact fib_succ_coprime hq s (prime_dvd_pow hq _ t h) hz.2.1

end TM.WallSunSun2
