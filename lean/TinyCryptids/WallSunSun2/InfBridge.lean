import TinyCryptids.WallSunSun2.Bridge

/-!
# Infinitely many `m` pass iff there are infinitely many Wall–Sun–Sun primes

* `pow_of_pow`: `q^j ∣ F k` with `q ∤ k` gives `q^j ∣ F z`, `z` the rank of `q` (the lifting
  of `sq_of_sq` for any power: `F (z (t + 1)) ≡ (t + 1) F z F (z - 1)^t (mod (F z)²)`).
* `dvd_of_prime_pows`: `m ∣ X` if every prime power dividing `m` divides `X`.
* `pass_dvd`: if every Wall–Sun–Sun prime is below `N`, every `m` that passes divides
  `F (N!)`: its prime factors are Wall–Sun–Sun primes `q < N`, and `q^(2a) ∣ m²` gives
  `q^a ∣ F (z q)`, with `z q ∣ wssIndex q ≤ N`.
-/

namespace TM.WallSunSun2
open TinyCryptids

theorem fib_pos' : ∀ n, 1 ≤ n → 1 ≤ fib n
  | 0, h => absurd h (by decide)
  | 1, _ => by decide
  | n + 2, _ => by rw [fib_add_two]; have := fib_pos' (n + 1) (by omega); omega

/-- the exponent of `q` in `m ≥ 1` -/
theorem max_pow {q m : Nat} (hq : 2 ≤ q) (hm : 1 ≤ m) : ∃ e, q ^ e ∣ m ∧ ¬ q ^ (e + 1) ∣ m := by
  have big : ¬ q ^ (m + 1) ∣ m := fun h => by
    have := Nat.le_of_dvd (by omega) h
    have := @Nat.lt_pow_self (m + 1) q (by omega); omega
  obtain ⟨e, he, hmin⟩ := exists_least (fun e => ¬ q ^ (e + 1) ∣ m) m big
  refine ⟨e, ?_, he⟩
  rcases e with _ | e
  · simp
  · exact Classical.byContradiction (hmin e (by omega))

theorem not_dvd_pow {r q : Nat} (hr : Prime r) (hq : Prime q) (hne : r ≠ q) (a : Nat) : ¬ r ∣ q ^ a := by
  intro h
  rcases a with _ | a
  · rw [Nat.pow_zero] at h; have := Nat.le_of_dvd (by decide) h; have := hr.1; omega
  · have := prime_dvd_pow hr q (a + 1) h
    rcases ((prime_iff_dvd q).1 hq).2 r this with e | e
    · have := hr.1; omega
    · exact hne e

/-- `r^b ∣ c Y` with `r ∤ c` gives `r^b ∣ Y` -/
theorem pow_dvd_of_mul {r c : Nat} (hr : Prime r) (hc : ¬ r ∣ c) : ∀ b Y, r ^ b ∣ c * Y → r ^ b ∣ Y
  | 0, _, _ => by simp
  | b + 1, Y, h => by
    have h1 : r ∣ c * Y := Nat.dvd_trans (Nat.dvd_mul_left r (r ^ b)) (by rwa [← Nat.pow_succ])
    rcases prime_dvd_mul hr h1 with h1 | ⟨Y', rfl⟩
    · exact absurd h1 hc
    · have e1 : r ^ (b + 1) = r * r ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
      have e2 : c * (r * Y') = r * (c * Y') := Nat.mul_left_comm _ _ _
      rw [e1, e2] at h
      have h2 := Nat.dvd_of_mul_dvd_mul_left (by have := hr.1; omega) h
      rw [e1]; exact Nat.mul_dvd_mul_left r (pow_dvd_of_mul hr hc b Y' h2)

theorem dvd_of_prime_pows : ∀ m, 1 ≤ m → ∀ X, (∀ r b, Prime r → r ^ b ∣ m → r ^ b ∣ X) → m ∣ X := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm X hX
    rcases Nat.lt_or_ge m 2 with h1 | h2
    · obtain rfl : m = 1 := by omega
      exact Nat.one_dvd X
    obtain ⟨q, hq, hqm⟩ := exists_prime_factor m h2
    obtain ⟨a, ha, hna⟩ := max_pow hq.1 hm
    obtain ⟨m', rfl⟩ := ha
    have hqa : 2 ≤ q ^ a := by
      rcases a with _ | a
      · simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one] at hqm hna
        exact absurd hqm hna
      · have : q ^ 1 ≤ q ^ (a + 1) := Nat.pow_le_pow_right (by have := hq.1; omega) (by omega)
        rw [Nat.pow_one] at this; have := hq.1; omega
    have hm' : 1 ≤ m' := by
      rcases m' with _ | m'
      · simp at hm
      · omega
    have hlt : m' < q ^ a * m' := by
      have := Nat.mul_le_mul_right m' hqa; omega
    have hqm' : ¬ q ∣ m' := fun h => hna (by rw [Nat.pow_succ]; exact Nat.mul_dvd_mul_left _ h)
    obtain ⟨Y, hY⟩ := hX q a hq (Nat.dvd_mul_right _ _)
    rw [hY]
    refine Nat.mul_dvd_mul_left _ (ih m' hlt hm' Y fun r b hr hrb => ?_)
    rcases b with _ | b
    · simp
    · have hrq : r ≠ q := fun e => hqm' (e ▸ Nat.dvd_of_pow_dvd (by omega) hrb)
      have := hX r (b + 1) hr (Nat.dvd_trans hrb (Nat.dvd_mul_left _ _))
      rw [hY] at this
      exact pow_dvd_of_mul hr (not_dvd_pow hr hq hrq a) (b + 1) Y this

/-- **lifting** for any power -/
theorem pow_of_pow {q z k j : Nat} (hq : Prime q) (hz : Rank q z) (hj : 1 ≤ j) (hk : q ^ j ∣ fib k)
    (hqk : ¬ q ∣ k) : q ^ j ∣ fib z := by
  have hq2 := hq.1
  have hzk := rank_dvd hq hz (Nat.dvd_of_pow_dvd hj hk)
  obtain ⟨j', rfl⟩ := hzk
  obtain ⟨s, rfl⟩ : ∃ s, z = s + 1 := ⟨z - 1, by have := hz.1; omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, j' = t + 1 := ⟨j' - 1, by
    rcases j' with _ | j'
    · exact absurd (Nat.dvd_zero q) (by simpa using hqk)
    · omega⟩
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨e, ⟨a', ha⟩, hne⟩ := max_pow hq2 (fib_pos' (s + 1) (by omega))
  have hej : e < j := Classical.byContradiction fun h =>
    hn (Nat.dvd_trans (Nat.pow_dvd_pow q (by omega)) ⟨a', ha⟩)
  have he1 : 1 ≤ e := by
    rcases e with _ | e
    · exact absurd (by simpa using hz.2.1) hne
    · omega
  have ha' : ¬ q ∣ a' := fun h => hne (by rw [ha, Nat.pow_succ]; exact Nat.mul_dvd_mul_left _ h)
  have hv := (lift s t).2
  rw [show (s + 1) * t + s + 1 = (s + 1) * (t + 1) by rw [Nat.mul_succ]; omega] at hv
  -- q^(e+1) ∣ (t + 1) a b^t
  have h1 : ((q ^ (e + 1) : Nat) : Int) ∣ ((t : Int) + 1) * fib (s + 1) * (fib s : Int) ^ t := by
    have hk' : ((q ^ (e + 1) : Nat) : Int) ∣ (fib ((s + 1) * (t + 1)) : Int) :=
      Int.ofNat_dvd.mpr (Nat.dvd_trans (Nat.pow_dvd_pow q (by omega)) hk)
    have ha2 : ((q ^ (e + 1) : Nat) : Int) ∣ (fib (s + 1) : Int) * fib (s + 1) := by
      rw [← Int.natCast_mul]; refine Int.ofNat_dvd.mpr ?_
      rw [ha]
      exact Nat.dvd_trans (Nat.pow_dvd_pow q (show e + 1 ≤ e + e by omega))
        (by rw [Nat.pow_add]; exact Nat.mul_dvd_mul (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _))
    have := Int.dvd_sub hk' (Int.dvd_trans ha2 hv)
    rwa [Int.sub_sub_self] at this
  have h2 : q ^ e * q ∣ q ^ e * ((t + 1) * a' * fib s ^ t) := by
    have e2 : ((t : Int) + 1) * fib (s + 1) * (fib s : Int) ^ t = ((q ^ e * ((t + 1) * a' * fib s ^ t) : Nat) : Int) := by
      rw [ha]; simp only [Int.natCast_mul, Int.natCast_pow, Int.natCast_add, Int.natCast_one,
        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    rw [e2, Nat.pow_succ] at h1; exact Int.ofNat_dvd.mp h1
  have h3 := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_pow_of_pos e (by omega)) h2
  rcases prime_dvd_mul hq h3 with h | h
  · rcases prime_dvd_mul hq h with h | h
    · exact hqk (Nat.dvd_trans h (Nat.dvd_mul_left _ _))
    · exact ha' h
  · exact fib_succ_coprime hq s (prime_dvd_pow hq _ t h) hz.2.1

theorem dvd_fact : ∀ n z, 1 ≤ z → z ≤ n → z ∣ fact n
  | 0, z, h1, h2 => by omega
  | n + 1, z, h1, h2 => by
    show z ∣ fact n * (n + 1)
    rcases Nat.lt_or_ge z (n + 1) with h | h
    · exact Nat.dvd_trans (dvd_fact n z h1 (by omega)) (Nat.dvd_mul_right _ _)
    · obtain rfl : z = n + 1 := by omega
      exact Nat.dvd_mul_left _ _

theorem fact_pos : ∀ n, 1 ≤ fact n
  | 0 => by decide
  | n + 1 => by
    show 1 ≤ fact n * (n + 1)
    have := fact_pos n; have := Nat.mul_le_mul this (show 1 ≤ n + 1 by omega); omega

/-- a prime factor of `m` does not divide `idx m = m ∓ 1` -/
theorem not_dvd_idx {q m : Nat} (hq : Prime q) (hqm : q ∣ m) : ¬ q ∣ idx m := fun hqk => by
  have h1 : q ∣ 1 := by
    unfold idx at hqk
    split at hqk
    · have := Nat.dvd_sub (show m - 1 ≤ m by omega) hqm hqk
      rwa [show m - (m - 1) = 1 by omega] at this
    · exact dvd_of_add_dvd (show q ∣ 1 + m by rwa [Nat.add_comm]) hqm
  have := Nat.le_of_dvd (by decide) h1; have := hq.1; omega

/-- with all Wall–Sun–Sun primes below `N`, every `m` that passes divides `F (N!)` -/
theorem pass_dvd {N : Nat} (hN : ∀ p, Prime p → p * p ∣ fib (wssIndex p) → p < N) {m : Nat}
    (hm : 2 ≤ m) (hd : m * m ∣ fib (idx m)) : m ∣ fib (fact N) := by
  refine dvd_of_prime_pows m (by omega) _ fun q a hq hqa => ?_
  rcases a with _ | a
  · simp
  have hqm := Nat.dvd_of_pow_dvd (by omega) hqa
  have hni := not_dvd_idx hq hqm
  have hw := wss_of_sq hq (Nat.dvd_trans (Nat.mul_dvd_mul hqm hqm) hd) hni
  have hlt := hN q hq hw
  have hwf := prime_dvd_fib_wss hq
  obtain ⟨z, hz⟩ := rank_exists (wssIndex_pos hq.1) hwf
  have h2 : q ^ ((a + 1) + (a + 1)) ∣ fib (idx m) := by
    rw [Nat.pow_add]; exact Nat.dvd_trans (Nat.mul_dvd_mul hqa hqa) hd
  have hp := pow_of_pow hq hz (by omega) h2 hni
  have hzw := rank_dvd hq hz hwf
  have hzle : z ≤ wssIndex q := Nat.le_of_dvd (wssIndex_pos hq.1) hzw
  have hwle : wssIndex q ≤ q + 1 := by unfold wssIndex; split <;> (try split) <;> omega
  refine Nat.dvd_trans (Nat.pow_dvd_pow q (by omega)) (Nat.dvd_trans hp (fib_dvd_of_dvd ?_))
  exact dvd_fact N z hz.1 (by omega)

theorem wss_passes {p : Nat} (hp : Prime p) (hd : p * p ∣ fib (wssIndex p)) : p * p ∣ fib (idx p) := by
  have h5 : p ≠ 5 := by rintro rfl; revert hd; decide
  have h50 : p % 5 ≠ 0 := fun e => by
    rcases Nat.lt_or_ge 5 p with l | l
    · exact hp.2 5 l (by decide) e
    · have := hp.1; omega
  unfold wssIndex at hd; unfold idx
  rw [if_neg h50] at hd
  exact hd

/-- **infinitely many `m` pass iff there are infinitely many Wall–Sun–Sun primes** -/
theorem inf_bridge :
    (∀ N, ∃ m, N ≤ m ∧ 2 ≤ m ∧ m * m ∣ fib (idx m)) ↔ InfinitelyManyWallSunSunPrimes := by
  constructor
  · intro h N
    refine Classical.byContradiction fun hn => ?_
    have hN : ∀ p, Prime p → p * p ∣ fib (wssIndex p) → p < N := fun p hp hd =>
      Classical.byContradiction fun hl => hn ⟨p, by omega, hp, hd⟩
    obtain ⟨m, hm, hm2, hd⟩ := h (fib (fact N) + 1)
    have := Nat.le_of_dvd (fib_pos' _ (fact_pos N)) (pass_dvd hN hm2 hd)
    omega
  · intro h N
    obtain ⟨p, hpN, hp, hd⟩ := h N
    exact ⟨p, hpN, hp.1, wss_passes hp hd⟩

end TM.WallSunSun2
