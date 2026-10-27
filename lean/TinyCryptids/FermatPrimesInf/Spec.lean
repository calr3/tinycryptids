import TinyCryptids.FermatPrimes.Spec

/-!
# The arithmetic: infinitely many Fermat primes as infinitely many passes

The test of a candidate is `../FermatPrimes`'s (`Good`, `FP`, `fp_iff'`): for odd `m ≥ 5`,
`m` is a pass (`FP m`: prime, `m - 1` a power of 2) iff no odd `e` with `3 ≤ e ≤ m - 2`
divides `m` or `m - 1`. A prime `2 ^ k + 1` has `k = 2 ^ n` (`prime_pow_two_add_one`), so the
passes are exactly the Fermat primes.
-/

namespace TM.FermatPrimesInf

open TinyCryptids
open TM.FermatPrimes (FP prime_pow_two_add_one)

theorem fpi_iff : InfinitelyManyFermatPrimes ↔ ∀ N, ∃ m, N ≤ m ∧ FP m := by
  constructor
  · intro h N
    obtain ⟨k, hk, hp⟩ := h N
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k < 2 ^ 2 ^ k := Nat.lt_two_pow_self
    exact ⟨2 ^ 2 ^ k + 1, by omega, hp, 2 ^ k, rfl⟩
  · intro h n
    obtain ⟨m, hm, hp, k, rfl⟩ := h (2 ^ 2 ^ n + 2)
    have hpos : 0 < 2 ^ 2 ^ n := Nat.two_pow_pos _
    have hk1 : 1 ≤ k := by
      rcases k with _ | k
      · rw [Nat.pow_zero] at hm; omega
      · omega
    obtain ⟨j, rfl⟩ := prime_pow_two_add_one k hk1 hp
    refine ⟨j, ?_, hp⟩
    apply Classical.byContradiction; intro hj
    have h1 : 2 ^ j ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 2 ^ j ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by decide) h1
    omega

end TM.FermatPrimesInf
