import TinyCryptids.Defs

/-!
# Arithmetic for the Firoozbakht machine

`pl m`: the primes below `m`, increasing; `prime_iff_pl`: trial division by them.
-/

namespace TM.Firoozbakht

open TinyCryptids

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

end TM.Firoozbakht
