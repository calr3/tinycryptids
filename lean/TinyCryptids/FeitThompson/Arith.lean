import TinyCryptids.Defs

/-!
# Arithmetic for the Feit–Thompson machine

* `rep_horner`: `rep b (n + 1) = b * rep b n + 1` (what the Horner routine computes);
* `rep_lt`: for `2 ≤ p < q`, `rep q p < rep p q`, so a counterexample `rep p q ∣ rep q p`
  has `q < p` (`ft_iff`);
* `pl m`: the primes below `m`, increasing; `prime_iff_pl`: trial division by them.
-/

namespace TM.FeitThompson

open TinyCryptids

theorem rep_succ (b n : Nat) : rep b (n + 1) = rep b n + b ^ n := rfl

theorem rep_horner (b : Nat) : ∀ n, rep b (n + 1) = b * rep b n + 1
  | 0 => by simp [rep]
  | n + 1 => by
    show rep b (n + 1) + b ^ (n + 1) = b * (rep b n + b ^ n) + 1
    rw [rep_horner b n, Nat.pow_succ, Nat.mul_add, Nat.mul_comm (b ^ n) b]
    omega

theorem rep_pos (b n : Nat) (hn : 1 ≤ n) : 1 ≤ rep b n := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [rep_horner]; omega

/-- `(q + 1)^i * (q - i) ≤ q^(i + 1)` for `i ≤ q` -/
theorem pow_succ_le (q : Nat) : ∀ i, i ≤ q → (q + 1) ^ i * (q - i) ≤ q ^ (i + 1)
  | 0, _ => by simp
  | i + 1, h => by
    have ih := pow_succ_le q i (by omega)
    have h1 : (q + 1) * (q - (i + 1)) ≤ q * (q - i) := by
      obtain ⟨k, rfl⟩ : ∃ k, q = i + 1 + k := ⟨q - (i + 1), by omega⟩
      rw [show i + 1 + k - (i + 1) = k by omega, show i + 1 + k - i = k + 1 by omega]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    calc (q + 1) ^ (i + 1) * (q - (i + 1)) = (q + 1) ^ i * ((q + 1) * (q - (i + 1))) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ (q + 1) ^ i * (q * (q - i)) := Nat.mul_le_mul_left _ h1
      _ = q * ((q + 1) ^ i * (q - i)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm ((q + 1) ^ i) q, Nat.mul_assoc]
      _ ≤ q * q ^ (i + 1) := Nat.mul_le_mul_left _ ih
      _ = q ^ (i + 1 + 1) := by rw [Nat.pow_succ q (i + 1), Nat.mul_comm]

/-- `(q + 1)^i ≤ p * q^i` for `i < p ≤ q` -/
theorem pow_le_mul (p q i : Nat) (hi : i < p) (hpq : p ≤ q) : (q + 1) ^ i ≤ p * q ^ i := by
  have h1 := pow_succ_le q i (by omega)
  have h2 : q ≤ p * (q - i) := by
    obtain ⟨a, rfl⟩ : ∃ a, p = i + 1 + a := ⟨p - (i + 1), by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, q = i + 1 + a + c := ⟨q - (i + 1 + a), by omega⟩
    rw [show i + 1 + a + c - i = a + c + 1 by omega]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    have : i * c + a * c + c ≥ c := by omega
    have : i * a + a * a + a ≥ a := by omega
    omega
  have hq : 0 < q := by omega
  apply Nat.le_of_mul_le_mul_left (c := q) _ hq
  calc q * (q + 1) ^ i = (q + 1) ^ i * q := Nat.mul_comm _ _
    _ ≤ (q + 1) ^ i * (p * (q - i)) := Nat.mul_le_mul_left _ h2
    _ = p * ((q + 1) ^ i * (q - i)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm ((q + 1) ^ i) p, Nat.mul_assoc]
    _ ≤ p * q ^ (i + 1) := Nat.mul_le_mul_left _ h1
    _ = q * (p * q ^ i) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (p * q ^ i) q]

theorem rep_succ_le (p q : Nat) (hpq : p ≤ q) : ∀ n, n ≤ p → rep (q + 1) n ≤ p * rep q n
  | 0, _ => by simp [rep]
  | n + 1, h => by
    rw [rep_succ, rep_succ, Nat.mul_add]
    have := rep_succ_le p q hpq n (by omega)
    have := pow_le_mul p q n (by omega) hpq
    omega

/-- `rep q p ≤ rep p q` for `q ≥ p ≥ 1`, strictly for `q > p` -/
theorem rep_le (p : Nat) (hp : 1 ≤ p) : ∀ k, rep (p + k) p ≤ rep p (p + k) ∧
    (1 ≤ k → rep (p + k) p < rep p (p + k))
  | 0 => ⟨Nat.le_refl _, fun h => absurd h (by omega)⟩
  | k + 1 => by
    have ih := (rep_le p hp k).1
    have h1 := rep_succ_le p (p + k) (by omega) p (Nat.le_refl _)
    have h2 := Nat.mul_le_mul_left p ih
    rw [show p + (k + 1) = p + k + 1 by omega, rep_horner p (p + k)]
    exact ⟨by omega, fun _ => by omega⟩

theorem rep_lt {p q : Nat} (hp : 1 ≤ p) (hpq : p < q) : rep q p < rep p q := by
  have := (rep_le p hp (q - p)).2 (by omega)
  rwa [show p + (q - p) = q by omega] at this

/-- A counterexample has its smaller prime as the exponent of the divisor. -/
theorem ft_iff : (∃ p q, Prime p ∧ Prime q ∧ p ≠ q ∧ rep p q ∣ rep q p) ↔
    (∃ p m, Prime p ∧ Prime m ∧ p < m ∧ rep m p ∣ rep p m) := by
  constructor
  · rintro ⟨p, q, hp, hq, hne, hd⟩
    rcases Nat.lt_or_ge p q with h | h
    · have hlt := rep_lt (by have := hp.two_le; omega) h
      have hpos := rep_pos q p (by have := hp.two_le; omega)
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    · exact ⟨q, p, hq, hp, by omega, hd⟩
  · rintro ⟨p, m, hp, hm, hlt, hd⟩
    exact ⟨m, p, hm, hp, by omega, hd⟩

/-! ## the primes below `m` -/

/-- the primes `< m`, increasing -/
def pl : Nat → List Nat
  | 0 => []
  | n + 1 => if Prime n then pl n ++ [n] else pl n

theorem mem_pl : ∀ m x, x ∈ pl m ↔ Prime x ∧ x < m
  | 0, x => by simp [pl]
  | n + 1, x => by
    unfold pl
    have ih := mem_pl n x
    split
    · rw [List.mem_append, ih]; simp only [List.mem_singleton]
      constructor
      · rintro (⟨h1, h2⟩ | rfl)
        · exact ⟨h1, by omega⟩
        · exact ⟨by assumption, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge x n with h | h
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr (by omega)
    · rw [ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rcases Nat.lt_or_ge x n with h | h
        · exact h
        · have : x = n := by omega
          subst this; contradiction

theorem pl_succ_prime {m : Nat} (h : Prime m) : pl (m + 1) = pl m ++ [m] := by
  simp [pl, h]

theorem pl_succ_not {m : Nat} (h : ¬ Prime m) : pl (m + 1) = pl m := by
  simp [pl, h]

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

/-- trial division by the primes below `m` -/
theorem prime_iff_pl (m : Nat) (hm : 2 ≤ m) : Prime m ↔ ∀ p ∈ pl m, ¬ p ∣ m := by
  constructor
  · intro h p hp hd
    obtain ⟨hpp, hlt⟩ := (mem_pl m p).1 hp
    exact h.2 p hlt hpp.two_le (Nat.mod_eq_zero_of_dvd hd)
  · intro h
    refine ⟨hm, fun d hd h2 hz => ?_⟩
    obtain ⟨p, hp, hpd⟩ := exists_prime_dvd d h2
    exact h p ((mem_pl m p).2 ⟨hp, Nat.lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpd) hd⟩)
      (Nat.dvd_trans hpd (Nat.dvd_of_mod_eq_zero hz))

theorem pl_two_le {m p : Nat} (h : p ∈ pl m) : 2 ≤ p := ((mem_pl m p).1 h).1.two_le

end TM.FeitThompson
