import TinyCryptids.WallSunSun2.Recip

/-!
# Every `m` that passes has a Wall–Sun–Sun prime factor

`idx m` is `m - 1` if `m ≡ ±1 (mod 5)`, else `m + 1`: the index the machine uses for every `m`.
`bridge`: some `m ≥ 2` has `m² ∣ F (idx m)` iff some prime `p` has `p² ∣ F (wssIndex p)`.
A prime factor `q` of such an `m` does not divide `idx m = m ∓ 1`, so by `sq_of_sq` `q²`
divides `F` of the rank of `q`, which divides `F (wssIndex q)` (`prime_dvd_fib_wss`).
-/

namespace TM.WallSunSun2
open TinyCryptids

def idx (m : Nat) : Nat := if m % 5 = 1 ∨ m % 5 = 4 then m - 1 else m + 1

theorem exists_prime_factor : ∀ m, 2 ≤ m → ∃ q, Prime q ∧ q ∣ m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    by_cases hp : Prime m
    · exact ⟨m, hp, Nat.dvd_refl m⟩
    · have : ∃ d, d < m ∧ 2 ≤ d ∧ m % d = 0 := Classical.byContradiction fun hn =>
        hp ⟨hm, fun d h1 h2 h3 => hn ⟨d, h1, h2, h3⟩⟩
      obtain ⟨d, h1, h2, h3⟩ := this
      obtain ⟨q, hq, hqd⟩ := ih d h1 h2
      exact ⟨q, hq, Nat.dvd_trans hqd (Nat.dvd_of_mod_eq_zero h3)⟩

theorem wssIndex_pos {q : Nat} (hq : 2 ≤ q) : 1 ≤ wssIndex q := by
  unfold wssIndex; split
  · omega
  · split <;> omega

/-- a prime factor `q` of `m` with `q² ∣ F k`, `q ∤ k` is a Wall–Sun–Sun prime -/
theorem wss_of_sq {q k : Nat} (hq : Prime q) (hk : q * q ∣ fib k) (hqk : ¬ q ∣ k) :
    q * q ∣ fib (wssIndex q) := by
  have hw := prime_dvd_fib_wss hq
  obtain ⟨z, hz⟩ := rank_exists (wssIndex_pos hq.1) hw
  exact Nat.dvd_trans (sq_of_sq hq hz hk hqk) (fib_dvd_of_dvd (rank_dvd hq hz hw))

theorem bridge : (∃ m, 2 ≤ m ∧ m * m ∣ fib (idx m)) ↔ ∃ p, Prime p ∧ p * p ∣ fib (wssIndex p) := by
  constructor
  · rintro ⟨m, hm, hd⟩
    obtain ⟨q, hq, hqm⟩ := exists_prime_factor m hm
    refine ⟨q, hq, wss_of_sq hq (Nat.dvd_trans (Nat.mul_dvd_mul hqm hqm) hd) fun hqk => ?_⟩
    have h1 : q ∣ 1 := by
      unfold idx at hqk
      split at hqk
      · have := Nat.dvd_sub (show m - 1 ≤ m by omega) hqm hqk
        rwa [show m - (m - 1) = 1 by omega] at this
      · exact dvd_of_add_dvd (show q ∣ 1 + m by rwa [Nat.add_comm]) hqm
    have := Nat.le_of_dvd (by decide) h1; have := hq.1; omega
  · rintro ⟨p, hp, hd⟩
    refine ⟨p, hp.1, ?_⟩
    have h5 : p ≠ 5 := by rintro rfl; revert hd; decide
    have h50 : p % 5 ≠ 0 := fun e => by
      rcases Nat.lt_or_ge 5 p with l | l
      · exact hp.2 5 l (by decide) e
      · have := hp.1; omega
    unfold wssIndex at hd; unfold idx
    rw [if_neg h50] at hd
    exact hd

end TM.WallSunSun2
