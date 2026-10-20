import TinyCryptids.WeakCollatz.Spec

/-!
# Cycles of the shortcut map and of the Collatz map

`tc x` is `collatz x` for even `x` and `collatz (collatz x)` for odd `x`, so an
orbit of `tc` is an orbit of `collatz` with the values `3x + 1` skipped.

* `tc_cycle_collatz`: a `tc`-cycle through `n` is a `collatz`-cycle through `n`.
* `collatz_cycle_tc`: a `collatz`-cycle through an odd `p` is a `tc`-cycle
  through `p` (odd values are never skipped).
* `counter_iff`: `tc` has a cycle through some `n ≥ 3` iff `collatz` has a cycle
  through some `n ∉ {1, 2, 4}`.
-/

namespace TM.WeakCollatz

open TinyCryptids

abbrev ci (k x : Nat) : Nat := iterate collatz k x

theorem ci_add (a b x : Nat) : ci (a + b) x = ci a (ci b x) := by
  induction a with
  | zero => simp [ci, iterate]
  | succ a ih => rw [Nat.add_right_comm]; show collatz (ci (a + b) x) = collatz (ci a (ci b x)); rw [ih]

theorem ci_succ' (k x : Nat) : ci (k + 1) x = ci k (collatz x) := by
  rw [ci_add]; rfl

theorem tc_eq_collatz (x : Nat) (h : x % 2 = 0) : tc x = collatz x := by
  unfold tc collatz; rw [if_pos h, if_pos h]

theorem tc_eq_collatz2 (x : Nat) (h : x % 2 = 1) : tc x = collatz (collatz x) := by
  have e : collatz x = 3 * x + 1 := by unfold collatz; rw [if_neg (by omega)]
  rw [tc_odd x h, e]; unfold collatz; rw [if_pos (by omega)]

/-- every `tc`-iterate is a `collatz`-iterate with at least as many steps -/
theorem it_ci : ∀ k x, ∃ k', k ≤ k' ∧ ci k' x = it k x := by
  intro k
  induction k with
  | zero => intro x; exact ⟨0, Nat.le_refl _, rfl⟩
  | succ k ih =>
    intro x
    obtain ⟨k', hk, e⟩ := ih (tc x)
    rw [it_succ', ← e]
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · exact ⟨k' + 1, by omega, by rw [ci_succ', tc_eq_collatz x hx]⟩
    · exact ⟨k' + 2, by omega, by rw [ci_succ', ci_succ', tc_eq_collatz2 x hx]⟩

theorem tc_cycle_collatz (n k : Nat) (hk : 0 < k) (h : it k n = n) : ∃ k', 0 < k' ∧ ci k' n = n := by
  obtain ⟨k', hk', e⟩ := it_ci k n
  exact ⟨k', by omega, by rw [e, h]⟩

/-- a `collatz`-iterate that is odd is a `tc`-iterate -/
theorem ci_it : ∀ m x p, ci m x = p → p % 2 = 1 → ∃ i, it i x = p ∧ (0 < m → 0 < i) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro x p hm hp
    rcases m with _ | m
    · exact ⟨0, hm, fun h => absurd h (by omega)⟩
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · rw [ci_succ', ← tc_eq_collatz x hx] at hm
      obtain ⟨i, hi, _⟩ := ih m (by omega) (tc x) p hm hp
      exact ⟨i + 1, by rw [it_succ']; exact hi, fun _ => by omega⟩
    · rcases m with _ | m
      · have : ci (0 + 1) x = 3 * x + 1 := by
          show collatz x = _; unfold collatz; rw [if_neg (by omega)]
        omega
      rw [ci_succ', ci_succ', ← tc_eq_collatz2 x hx] at hm
      obtain ⟨i, hi, _⟩ := ih m (by omega) (tc x) p hm hp
      exact ⟨i + 1, by rw [it_succ']; exact hi, fun _ => by omega⟩

theorem collatz_pos' (x : Nat) (h : 0 < x) : 0 < collatz x := by
  unfold collatz; split <;> omega

/-- every positive orbit reaches an odd value -/
theorem ci_odd : ∀ x, 0 < x → ∃ j, ci j x % 2 = 1 := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro hx
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have e : collatz x = x / 2 := by unfold collatz; rw [if_pos h]
      obtain ⟨j, hj⟩ := ih (x / 2) (by omega) (by omega)
      exact ⟨j + 1, by rw [ci_succ', e]; exact hj⟩
    · exact ⟨0, h⟩

theorem ci_mul (n k : Nat) (h : ci k n = n) : ∀ q, ci (k * q) n = n := by
  intro q
  induction q with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, ci_add, h, ih]

/-- the `collatz`-orbit of 1 is `1, 4, 2, 1, …` -/
theorem ci_one (t : Nat) : ci t 1 = 1 ∨ ci t 1 = 2 ∨ ci t 1 = 4 := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    show collatz (ci t 1) = 1 ∨ collatz (ci t 1) = 2 ∨ collatz (ci t 1) = 4
    rcases ih with h | h | h <;> rw [h] <;> decide

theorem counter_iff :
    Counter ↔ ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4 := by
  constructor
  · rintro ⟨n, k, hn, hk, h⟩
    obtain ⟨k', hk', e⟩ := tc_cycle_collatz n k hk h
    refine ⟨n, k', by omega, hk', e, by omega, by omega, ?_⟩
    -- the `tc`-orbit of 4 is `4, 2, 1, 2, 1, …`
    rintro rfl
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [it_succ'] at h
    have e2 : it k (tc 4) = it (k + 1) 1 := by rw [it_succ']; rfl
    rw [e2] at h
    rcases it_one (k + 1) with e | e <;> omega
  · rintro ⟨n0, k0, hn0, hk0, hc, h1, h2, h4⟩
    obtain ⟨j, hj⟩ := ci_odd n0 hn0
    -- `p` is odd and on the cycle
    have hp : ci k0 (ci j n0) = ci j n0 := by
      rw [← ci_add, Nat.add_comm, ci_add]; exact congrArg (ci j) hc
    have hp1 : ci j n0 ≠ 1 := by
      intro e
      have hq := ci_mul n0 k0 hc j
      rw [show k0 * j = (k0 * j - j) + j by
        have : j ≤ k0 * j := Nat.le_mul_of_pos_left j hk0
        omega, ci_add, e] at hq
      rcases ci_one (k0 * j - j) with e' | e' | e' <;> omega
    obtain ⟨i, hi, hi0⟩ := ci_it k0 (ci j n0) _ hp hj
    exact ⟨ci j n0, i, by omega, hi0 hk0, hi⟩

end TM.WeakCollatz
