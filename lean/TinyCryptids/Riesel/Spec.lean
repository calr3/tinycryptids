import TinyCryptids.Defs

/-!
# The statement and arithmetic facts

The Riesel problem below 509203: every odd `k < 509203` has some `n ≥ 1` with
`k·2^n - 1` prime (no Riesel number is below 509203). `Good k` says that `k`
has such an `n`.
-/

namespace TM.Riesel

open TinyCryptids

def Good (k : Nat) : Prop := ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)

theorem good_one : Good 1 := ⟨2, by decide, by
  refine ⟨by decide, fun d h1 h2 => ?_⟩
  have : d = 2 := by omega
  subst this; decide⟩

theorem good_three : Good 3 := ⟨1, Nat.le_refl _, by
  refine ⟨by decide, fun d h1 h2 => ?_⟩
  have : d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases this with rfl | rfl | rfl <;> decide⟩

theorem add_mod_self_left' (d x : Nat) : (d + x) % d = x % d := by
  rw [Nat.add_comm]; exact Nat.add_mod_right x d

/-- `(x + 1) % d` from `x % d` -/
theorem mod_succ (x d : Nat) :
    (x % d + 1 < d → (x + 1) % d = x % d + 1) ∧ (x % d + 1 = d → (x + 1) % d = 0) := by
  have e := Nat.div_add_mod x d
  constructor
  · intro h
    have : x + 1 = d * (x / d) + (x % d + 1) := by omega
    rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  · intro h
    have : x + 1 = d * (x / d + 1) := by rw [Nat.mul_add]; omega
    rw [this, Nat.mul_mod_right]

/-- the candidates are odd and at least 9 -/
theorem cand_odd (k n : Nat) (hk : k % 2 = 1) (hn : 1 ≤ n) : (k * 2 ^ n - 1) % 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : 1 ≤ k := by omega
  have : 1 ≤ 2 ^ m := Nat.pos_pow_of_pos m (show 0 < 2 by decide)
  have : 1 ≤ k * 2 ^ m := Nat.mul_le_mul ‹1 ≤ k› this
  rw [Nat.pow_succ, ← Nat.mul_assoc]; omega

theorem cand_ge (k n : Nat) (hk : 5 ≤ k) (hn : 1 ≤ n) : 9 ≤ k * 2 ^ n - 1 := by
  have : 2 ≤ 2 ^ n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.pow_succ]; have := Nat.pos_pow_of_pos m (show 0 < 2 by decide); omega
  have := Nat.mul_le_mul hk this
  omega

theorem cand_succ (k n : Nat) (hk : 1 ≤ k) : k * 2 ^ (n + 1) - 1 = 2 * (k * 2 ^ n - 1) + 1 := by
  have : 1 ≤ 2 ^ n := Nat.pos_pow_of_pos n (show 0 < 2 by decide)
  have : 1 ≤ k * 2 ^ n := Nat.mul_le_mul hk this
  rw [Nat.pow_succ, ← Nat.mul_assoc]; omega

end TM.Riesel
