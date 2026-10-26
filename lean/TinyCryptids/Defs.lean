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

/-- The twin prime conjecture: there are infinitely many primes `p` with `p + 2` prime. -/
def TwinPrimeConjecture : Prop := ∀ n, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)

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

end TinyCryptids
