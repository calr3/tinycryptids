import TinyCryptids.Defs

/-!
# The statement

Lemoine's conjecture: every odd `n ≥ 7` is `p + 2q` with `p`, `q` prime. The machine searches
`q = 2, 3, …` with `p = n - 2q ≥ 1`; `Rep n` says it finds one.
-/

namespace TM.Lemoine

open TinyCryptids

/-- `n = p + 2q` with `q ≥ 2` (and then `p = n - 2q ≥ 1`) -/
def Rep (n : Nat) : Prop := ∃ q, 2 ≤ q ∧ 2 * q < n ∧ Prime (n - 2 * q) ∧ Prime q

theorem fails_iff (n : Nat) :
    (∀ p q, Prime p → Prime q → p + 2 * q ≠ n) ↔ ¬ Rep n := by
  constructor
  · rintro h ⟨q, _, h2, hp, hq⟩
    exact h _ _ hp hq (by omega)
  · intro h p q hp hq e
    exact h ⟨q, hq.two_le, by have := hp.two_le; omega, by rw [show n - 2 * q = p by omega]; exact hp, hq⟩

end TM.Lemoine
