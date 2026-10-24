import TinyCryptids.Defs

/-!
# Arithmetic for the twin prime machine

* `Good m e`: the trial divisor `e` divides neither `m` nor `m + 2`.
* `fail_iff`: after the mod walk for `d` the D hole is on cell `c = (m - 1) % d`, and `d`
  divides `m` or `m + 2` iff `c + 1 = d` or `c + 3 = d` (the cells the check reads).
* `twin_iff`: for `m ≥ 3`, `m` and `m + 2` are both prime iff every `e` with `2 ≤ e < m` is
  good.
-/

namespace TM.TwinPrimes

open TinyCryptids

def Good (m e : Nat) : Prop := m % e ≠ 0 ∧ (m + 2) % e ≠ 0

/-- `y % d` for `y < 2 * d` -/
theorem mod_two (y d : Nat) (h1 : d ≤ y) (h2 : y < 2 * d) : y % d = y - d := by
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

theorem fail_iff (d m : Nat) (hd : 2 ≤ d) (hm : 1 ≤ m) :
    ¬ Good m d ↔ ((m - 1) % d + 1 = d ∨ (m - 1) % d + 3 = d) := by
  have e := Nat.div_add_mod (m - 1) d
  have hc := Nat.mod_lt (m - 1) (show d > 0 by omega)
  generalize (m - 1) % d = c at e hc
  generalize (m - 1) / d = q at e
  have h1 : m % d = (c + 1) % d := by
    rw [show m = d * q + (c + 1) by omega, Nat.mul_add_mod]
  have h3 : (m + 2) % d = (c + 3) % d := by
    rw [show m + 2 = d * q + (c + 3) by omega, Nat.mul_add_mod]
  unfold Good
  rw [h1, h3]
  constructor
  · intro h
    apply Classical.byContradiction; intro hno
    apply h; constructor
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · rcases Nat.lt_or_ge (c + 3) d with hl | hl
      · rw [Nat.mod_eq_of_lt hl]; omega
      · rcases Nat.lt_or_ge (c + 3) (2 * d) with hl2 | hl2
        · rw [mod_two _ _ hl hl2]; omega
        · omega
  · rintro (h | h) ⟨ha, hb⟩
    · rw [h, Nat.mod_self] at ha; exact ha rfl
    · rw [h, Nat.mod_self] at hb; exact hb rfl

theorem twin_iff (m : Nat) (hm : 3 ≤ m) :
    (Prime m ∧ Prime (m + 2)) ↔ ∀ e, 2 ≤ e → e < m → Good m e := by
  constructor
  · rintro ⟨⟨_, hp⟩, ⟨_, hq⟩⟩ e h1 h2
    exact ⟨hp e h2 h1, hq e (by omega) h1⟩
  · intro h
    refine ⟨⟨by omega, fun e h1 h2 => (h e h2 h1).1⟩, ⟨by omega, fun e h1 h2 => ?_⟩⟩
    rcases Nat.lt_or_ge e m with he | he
    · exact (h e h2 he).2
    · rcases Nat.eq_or_lt_of_le he with rfl | he'
      · rw [show m + 2 = m * 1 + 2 by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        omega
      · obtain rfl : e = m + 1 := by omega
        rw [show m + 2 = (m + 1) * 1 + 1 by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        omega

end TM.TwinPrimes
