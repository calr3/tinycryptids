/-!
# Mathematical definitions used in the theorem statements

Every machine's main theorem is stated with these definitions (core Lean only,
no Mathlib). Proofs may use other forms internally, linked to these by lemmas.
-/

namespace TinyCryptids

/-- `p` is prime: at least 2, and no `d` with `2 ≤ d < p` divides it. -/
def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → p % d ≠ 0

instance : DecidablePred Prime := fun p => by unfold Prime; exact inferInstance

/-- `f` applied `k` times. -/
def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => f (iterate f k x)

/-- The Collatz map: `x / 2` for even `x`, `3x + 1` for odd `x`. Its only known cycle on the
positive integers is `1 → 4 → 2 → 1`. -/
def collatz (x : Nat) : Nat := if x % 2 = 0 then x / 2 else 3 * x + 1

example : iterate collatz 3 1 = 1 := by decide
example : iterate collatz 7 3 = 1 := by decide

end TinyCryptids
