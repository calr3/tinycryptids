import TinyCryptids.Defs

/-!
# The statement and its arithmetic

The machine beeps once for each `n` with `n < properDivSum n` and
`properDivSum (properDivSum n) = n`: the smaller number of an amicable pair (`Small n`).
`inf_iff`: there are infinitely many amicable numbers iff there are infinitely many such `n`.
-/

namespace TM.Amicable

open TinyCryptids

/-- `n` is the smaller number of an amicable pair -/
def Small (n : Nat) : Prop := n < properDivSum n ∧ properDivSum (properDivSum n) = n

instance (n : Nat) : Decidable (Small n) := by unfold Small; infer_instance


theorem properDivSum_eq (n : Nat) (hn : 1 ≤ n) : properDivSum n = divSumBelow n (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [properDivSum, divSumBelow]

theorem sub_mod_self (n d : Nat) (h : d ≤ n) : (n - d) % d = n % d := by
  have := Nat.add_mod_right (n - d) d
  rw [Nat.sub_add_cancel h] at this; exact this.symm

theorem divSumBelow_step (n d : Nat) (hd : 1 ≤ d) (hdn : d < n) :
    divSumBelow n (d - 1) + (if (n - d) % d = 0 then d else 0) = divSumBelow n d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [sub_mod_self n (e + 1) (by omega)]
  simp only [divSumBelow, Nat.add_sub_cancel, hdn, true_and]

theorem divSumBelow_le (n : Nat) : ∀ k, divSumBelow n k ≤ k * k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have := divSumBelow_le n k
    simp only [divSumBelow]
    split <;> rw [Nat.add_mul, Nat.mul_add] <;> omega

theorem properDivSum_le (n : Nat) : properDivSum n ≤ n * n := divSumBelow_le n n

theorem small_amicable {n : Nat} (h : Small n) : Amicable n := ⟨by have := h.1; omega, h.2⟩

/-- infinitely many amicable numbers iff infinitely many smaller numbers of amicable pairs -/
theorem inf_iff : InfinitelyManyAmicable ↔ ∀ N, ∃ n, N ≤ n ∧ Small n := by
  constructor
  · intro h N
    obtain ⟨n, hn, hne, hs⟩ := h (N * N + N + 1)
    rcases Nat.lt_or_ge n (properDivSum n) with hl | hg
    · exact ⟨n, by omega, hl, hs⟩
    · -- n is the larger number: its partner m is the smaller one, and m ≥ N
      have hlt : properDivSum n < n := by omega
      refine ⟨properDivSum n, ?_, by rw [hs]; exact hlt, by rw [hs]⟩
      apply Classical.byContradiction; intro hm
      have h1 := properDivSum_le (properDivSum n)
      rw [hs] at h1
      have : properDivSum n * properDivSum n ≤ N * N :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
  · intro h N
    obtain ⟨n, hn, hs⟩ := h N
    exact ⟨n, hn, small_amicable hs⟩

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

end TM.Amicable
