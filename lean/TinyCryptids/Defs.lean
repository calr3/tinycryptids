/-!
# Mathematical definitions used in the theorem statements

Every machine's main theorem is stated with these definitions (core Lean only,
no Mathlib). Proofs may use other forms internally, linked to these by lemmas.
-/

namespace TinyCryptids

/-- `p` is prime: at least 2, and no `d` with `2 ≤ d < p` divides it. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → p % d ≠ 0

theorem Prime.two_le {p : Nat} (h : Prime p) : 2 ≤ p := h.1

instance : DecidablePred Prime := fun p => by unfold Prime; exact inferInstance

/-- Divisor form of primality: the only divisors are `1` and `p`. -/
theorem prime_iff_dvd (p : Nat) : Prime p ↔ 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p := by
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d hd => ?_⟩
    have hdp : d ≤ p := Nat.le_of_dvd (by omega) hd
    rcases Nat.lt_or_ge d 2 with hlt | hge
    · rcases d with _ | _ | d
      · obtain ⟨k, hk⟩ := hd; simp at hk; omega
      · exact Or.inl rfl
      · omega
    · rcases Nat.lt_or_ge d p with hlt' | hge'
      · exact absurd (Nat.mod_eq_zero_of_dvd hd) (h d hlt' hge)
      · exact Or.inr (by omega)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d hdp hd hm => ?_⟩
    rcases h d (Nat.dvd_of_mod_eq_zero hm) with h1 | h1 <;> omega

/-- The twin prime conjecture: there are infinitely many primes `p` with `p + 2` prime. -/
def TwinPrimeConjecture : Prop := ∀ n, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)

/-- There are infinitely many Fermat primes: infinitely many `n` with `2 ^ 2 ^ n + 1` prime. -/
def InfinitelyManyFermatPrimes : Prop := ∀ n, ∃ k, n ≤ k ∧ Prime (2 ^ 2 ^ k + 1)

/-- `f` applied `k` times. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => f (iterate f k x)

/-- The Collatz map: `x / 2` for even `x`, `3x + 1` for odd `x`. Its only known cycle on the
positive integers is `1 → 4 → 2 → 1`. -/
def collatz (x : Nat) : Nat := if x % 2 = 0 then x / 2 else 3 * x + 1

example : iterate collatz 3 1 = 1 := by decide
example : iterate collatz 7 3 = 1 := by decide

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => fact n * (n + 1)

/-- Left factorial `!n = 0! + 1! + … + (n-1)!`. -/
def leftFact : Nat → Nat
  | 0 => 0
  | n + 1 => leftFact n + fact n

/-- sum of the divisors `d ≤ k` of `n` with `d < n` -/
def divSumBelow (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => divSumBelow n k + (if k + 1 < n ∧ n % (k + 1) = 0 then k + 1 else 0)

/-- sum of the proper divisors of `n` (`properDivSum 1 = 0`); `n` is perfect iff it equals `n` -/
def properDivSum (n : Nat) : Nat := divSumBelow n n

example : properDivSum 6 = 6 := by decide
example : properDivSum 28 = 28 := by decide

/-- The product of the primes `p < k` that divide `n`. -/
def radBelow (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => radBelow n k * (if Prime k ∧ n % k = 0 then k else 1)

/-- The radical of `n ≥ 1`: the product of its distinct prime factors (`rad 1 = 1`). -/
def rad (n : Nat) : Nat := radBelow n (n + 1)

example : rad 72 = 6 := by decide
example : rad 30 = 30 := by decide

/-- The abc conjecture: for every `ε > 0` only finitely many coprime `a + b = c` have
`c > rad(abc)^(1+ε)`.  Equivalently (take `ε = 1/n`, and "finitely many" as a bound on `c`):
for every `n ≥ 1` there is an `N` such that every coprime `a, b ≥ 1` with `a + b ≥ N` has
`(a + b)^n ≤ rad(ab(a + b))^(n+1)`. -/
def ABCConjecture : Prop :=
  ∀ n, 1 ≤ n → ∃ N, ∀ a b, 1 ≤ a → 1 ≤ b → Nat.gcd a b = 1 → N ≤ a + b →
    (a + b) ^ n ≤ rad (a * b * (a + b)) ^ (n + 1)

end TinyCryptids
