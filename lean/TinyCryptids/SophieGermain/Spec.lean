import TinyCryptids.Defs

/-!
# Arithmetic for the Sophie Germain machine

* `Good n e`: the trial divisor `e` divides neither `n` nor `2 n + 1`.
* `sg_iff`: for odd `n ≥ 5`, `n` is a Sophie Germain prime iff every odd `e` with
  `3 ≤ e ≤ n - 2` is good.
-/

namespace TM.SophieGermain

open TinyCryptids

def Good (n e : Nat) : Prop := n % e ≠ 0 ∧ (2 * n + 1) % e ≠ 0

theorem sg_iff (n : Nat) (hn : 5 ≤ n) (ho : n % 2 = 1) :
    SophieGermainPrime n ↔ ∀ e, 3 ≤ e → e + 2 ≤ n → e % 2 = 1 → Good n e := by
  constructor
  · rintro ⟨⟨_, hp⟩, ⟨_, hq⟩⟩ e h1 h2 _
    exact ⟨hp e (by omega) (by omega), hq e (by omega) (by omega)⟩
  · intro h
    refine ⟨⟨by omega, fun d hd h2 hz => ?_⟩, ⟨by omega, fun d hd h2 hz => ?_⟩⟩
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hz
      rcases Nat.mod_two_eq_zero_or_one d with he | he
      · have : n % 2 = 0 := by rw [hk, Nat.mul_mod, he]; simp
        omega
      · exact (h d (by omega) (by omega) he).1 hz
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hz
      have hpar : (d * k) % 2 = 1 := by rw [← hk]; omega
      rw [Nat.mul_mod] at hpar
      have hd2 : d % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one d with h0 | h0 <;> rcases Nat.mod_two_eq_zero_or_one k with h1 | h1 <;>
          simp [h0, h1] at hpar <;> omega
      have hk2 : k % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one k with h1 | h1
        · simp [h1] at hpar
        · exact h1
      -- the cofactor is odd and not 1, so at least 3
      have hk3 : 3 ≤ k := by
        rcases k with _ | _ | _ | k
        · omega
        · omega
        · omega
        · omega
      have : d * 3 ≤ d * k := Nat.mul_le_mul_left d hk3
      exact (h d (by omega) (by omega) hd2).2 hz

end TM.SophieGermain
