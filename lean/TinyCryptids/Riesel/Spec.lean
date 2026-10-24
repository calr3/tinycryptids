import TinyCryptids.Defs

/-!
# The statement and arithmetic facts

The Riesel problem below 509203: every odd `k < 509203` has some `n ≥ 1` with
`k·2^n - 1` prime (no Riesel number is below 509203).  `Good k` says that `k`
has such an `n`.
-/

namespace TM.Riesel

open TinyCryptids

def Good (k : Nat) : Prop := ∃ n, 1 ≤ n ∧ Prime (k * 2 ^ n - 1)

theorem good_one : Good 1 := ⟨2, by decide, by
  refine ⟨by decide, fun d h1 h2 => ?_⟩
  have : d = 2 := by omega
  subst this; decide⟩

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

/-- the candidates of an odd `k` are odd -/
theorem cand_odd (k n : Nat) (hk : k % 2 = 1) (hn : 1 ≤ n) : (k * 2 ^ n - 1) % 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.pow_succ, ← Nat.mul_assoc]
  have h1 : 1 ≤ k * 2 ^ m :=
    Nat.mul_pos (by omega) (Nat.pos_pow_of_pos m (show 0 < 2 by decide))
  have e : k * 2 ^ m * 2 - 1 = 2 * (k * 2 ^ m - 1) + 1 := by omega
  rw [e, Nat.add_mod, Nat.mul_mod_right]

/-- the candidates are at least 5 -/
theorem cand_ge (k n : Nat) (hk : 3 ≤ k) (hn : 1 ≤ n) : 5 ≤ k * 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.pow_succ, ← Nat.mul_assoc]
  have hx : 3 ≤ k * 2 ^ m :=
    Nat.le_trans (show 3 ≤ 3 * 1 by omega)
      (Nat.mul_le_mul hk (Nat.pos_pow_of_pos m (show 0 < 2 by decide)))
  omega

theorem cand_succ (k n : Nat) (hk : 1 ≤ k) :
    k * 2 ^ (n + 1) - 1 = 2 * (k * 2 ^ n - 1) + 1 := by
  rw [Nat.pow_succ, ← Nat.mul_assoc]
  have h1 : 1 ≤ k * 2 ^ n :=
    Nat.mul_pos (by omega) (Nat.pos_pow_of_pos n (show 0 < 2 by decide))
  omega

end TM.Riesel
