import TinyCryptids.Defs

/-!
# The statement

Kurepa's conjecture: no odd prime `p` divides `!p = 0! + 1! + … + (p - 1)!`. The machine tests
every `n ≥ 3`; `kurepa_iff` shows that some `n ≥ 3` divides `!n` iff some odd prime `p` divides
`!p`: a prime `q ≤ n` divides `k!` for `k ≥ q`, so `!n ≡ !q (mod q)`, and `!n ≡ 2 (mod 4)` for
`n ≥ 4`.
-/

namespace TM.Kurepa

open TinyCryptids

theorem fact_pos : ∀ n, 1 ≤ fact n
  | 0 => by decide
  | n + 1 => by
    have := fact_pos n
    show 1 ≤ fact n * (n + 1)
    have := Nat.mul_le_mul this (show 1 ≤ n + 1 by omega)
    omega

theorem fact_succ' (n : Nat) : fact (n + 1) = fact n + n * fact n := by
  show fact n * (n + 1) = _
  rw [Nat.mul_succ, Nat.mul_comm (fact n) n, Nat.add_comm]

theorem dvd_fact {q : Nat} (hq : 1 ≤ q) : ∀ k, q ≤ k → q ∣ fact k
  | 0, h => by omega
  | k + 1, h => by
    show q ∣ fact k * (k + 1)
    rcases Nat.lt_or_ge q (k + 1) with h' | h'
    · exact Nat.dvd_trans (dvd_fact hq k (by omega)) (Nat.dvd_mul_right _ _)
    · obtain rfl : q = k + 1 := by omega
      exact Nat.dvd_mul_left _ _

theorem leftFact_mod {q : Nat} (hq : 1 ≤ q) : ∀ k, leftFact (q + k) % q = leftFact q % q
  | 0 => rfl
  | k + 1 => by
    show (leftFact (q + k) + fact (q + k)) % q = _
    obtain ⟨c, hc⟩ := dvd_fact hq (q + k) (by omega)
    rw [hc, Nat.add_mul_mod_self_left]
    exact leftFact_mod hq k

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

/-- Some `n ≥ 3` divides `!n` iff some odd prime `p` divides `!p`. -/
theorem kurepa_iff :
    (∃ n, 3 ≤ n ∧ n ∣ leftFact n) ↔ ∃ p, Prime p ∧ 2 < p ∧ p ∣ leftFact p := by
  constructor
  · rintro ⟨n, hn, hd⟩
    -- an odd divisor `d ≥ 3` of `n`
    have h4 : ¬ 4 ∣ n := by
      intro h4
      have e := leftFact_mod (q := 4) (by omega) (n - 4)
      rw [show 4 + (n - 4) = n by
        have : 4 ≤ n := by
          obtain ⟨c, hc⟩ := h4
          rcases c with _ | c
          · omega
          · rw [hc]; exact Nat.le_mul_of_pos_right 4 (by omega)
        omega] at e
      have : leftFact 4 % 4 = 2 := by decide
      have := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h4 hd)
      omega
    have hodd : ∃ d, 3 ≤ d ∧ d % 2 = 1 ∧ d ∣ n := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
        have hk : k % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one k with h' | h'
          · exact absurd ⟨k / 2, by omega⟩ h4
          · exact h'
        exact ⟨k, by omega, hk, Nat.dvd_mul_left k 2⟩
      · exact ⟨n, hn, h, Nat.dvd_refl n⟩
    obtain ⟨d, hd3, hd2, hdn⟩ := hodd
    obtain ⟨p, hp, hpd⟩ := exists_prime_dvd d (by omega)
    have hp2 : 2 < p := by
      have := hp.two_le
      rcases Nat.lt_or_ge 2 p with h | h
      · exact h
      · obtain rfl : p = 2 := by omega
        obtain ⟨c, hc⟩ := hpd; omega
    have hpn : p ∣ n := Nat.dvd_trans hpd hdn
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
    have e := leftFact_mod (q := p) (by omega) (n - p)
    rw [show p + (n - p) = n by omega] at e
    refine ⟨p, hp, hp2, Nat.dvd_of_mod_eq_zero ?_⟩
    rw [← e]; exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hpn hd)
  · rintro ⟨p, hp, h2, hd⟩
    exact ⟨p, by omega, hd⟩

end TM.Kurepa
