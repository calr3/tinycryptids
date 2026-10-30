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

/-- The Mersenne prime conjecture: there are infinitely many primes of the form `2 ^ k - 1`
(infinitely many `k` with `2 ^ k - 1` prime). -/
def MersennePrimeConjecture : Prop := ∀ n, ∃ k, n ≤ k ∧ Prime (2 ^ k - 1)

/-- `p` is a Sophie Germain prime: `p` and `2 p + 1` are both prime. -/
def SophieGermainPrime (p : Nat) : Prop := Prime p ∧ Prime (2 * p + 1)

/-- There are only finitely many Sophie Germain primes: all of them lie below some bound. -/
def FinitelyManySophieGermainPrimes : Prop := ∃ N, ∀ p, SophieGermainPrime p → p < N

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

/-! ## The theory T of the PA machine

First-order logic with `=` and `∈` (Tarski's system S2) plus one set existence scheme of
H. Friedman, as in LegionMammal978's `pa.py`.  T is equiconsistent with Peano arithmetic, and it
proves `¬ v0 ∈ v0` (an empty set exists), so it proves `v0 ∈ v0` iff it is inconsistent. -/

/-- Formulas of first-order logic with `=` and `∈`; variables are numbers (`v0, v1, …`). -/
inductive Wff
  | eq (x y : Nat)
  | el (x y : Nat)
  | imp (φ ψ : Wff)
  | neg (φ : Wff)
  | all (x : Nat) (φ : Wff)
  deriving DecidableEq

namespace Wff

/-- `∃x φ` is `¬∀x ¬φ`. -/
def ex (x : Nat) (φ : Wff) : Wff := neg (all x (neg φ))

/-- `φ ∧ ψ` is `¬(φ → ¬ψ)`. -/
def and (φ ψ : Wff) : Wff := neg (imp φ (neg ψ))

/-- The axioms of T: Tarski's S2 (B1–B3 propositional, B4–B8 for quantifiers and equality;
B6a needs `z` distinct from `x` and `y`) and Friedman's scheme E: for every formula `φ`,
`∃v1 ∀v0 (((¬ v0 ∈ v2 → v0 = v3) → (∀v1 φ → v0 ∈ v1)) ∧ (v0 ∈ v1 → ∀v1 φ))`. -/
inductive Axiom : Wff → Prop
  | b1 (φ ψ χ : Wff) : Axiom (imp (imp φ ψ) (imp (imp ψ χ) (imp φ χ)))
  | b2 (φ : Wff) : Axiom (imp (imp (neg φ) φ) φ)
  | b3 (φ ψ : Wff) : Axiom (imp φ (imp (neg φ) ψ))
  | b4 (x : Nat) (φ ψ : Wff) : Axiom (imp (all x (imp φ ψ)) (imp (all x φ) (all x ψ)))
  | b6a (x y z : Nat) : z ≠ x → z ≠ y →
      Axiom (and (imp (eq x y) (all z (eq x y))) (imp (el x y) (all z (el x y))))
  | b6b (x y : Nat) (φ : Wff) : Axiom (imp (all x (all y φ)) (all y (all x φ)))
  | b6c (x : Nat) (φ : Wff) : Axiom (imp (ex x (all x φ)) φ)
  | b7 (x y : Nat) : Axiom (ex x (eq x y))
  | b8a (x y z : Nat) : Axiom (imp (eq x y) (imp (eq x z) (eq y z)))
  | b8b (x y z : Nat) : Axiom (imp (eq x y) (imp (el x z) (el y z)))
  | b8c (x y z : Nat) : Axiom (imp (eq x y) (imp (el z x) (el z y)))
  | e (φ : Wff) : Axiom (ex 1 (all 0 (and
      (imp (imp (neg (el 0 2)) (eq 0 3)) (imp (all 1 φ) (el 0 1)))
      (imp (el 0 1) (all 1 φ)))))

/-- The theorems of T: closure of the axioms under modus ponens and generalisation. -/
inductive Provable : Wff → Prop
  | ax {φ : Wff} : Axiom φ → Provable φ
  | mp {φ ψ : Wff} : Provable (imp φ ψ) → Provable φ → Provable ψ
  | gen (x : Nat) {φ : Wff} : Provable φ → Provable (all x φ)

end Wff

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `p - (p/5)` with `(p/5)` the Legendre symbol: the index of the Fibonacci number in
the definition of a Wall–Sun–Sun prime. -/
def wssIndex (p : Nat) : Nat :=
  if p % 5 = 0 then p else if p % 5 = 1 ∨ p % 5 = 4 then p - 1 else p + 1

/-- There are infinitely many Wall–Sun–Sun primes (primes `p` with `p² ∣ F(p - (p/5))`). -/
def InfinitelyManyWallSunSunPrimes : Prop :=
  ∀ n, ∃ p, n ≤ p ∧ Prime p ∧ p * p ∣ fib (wssIndex p)

/-- Binomial coefficients by Pascal's rule. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

end TinyCryptids
