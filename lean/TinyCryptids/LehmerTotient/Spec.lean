import TinyCryptids.Carmichael.Spec

/-!
# The arithmetic of the Lehmer totient machine

* `φ(n)` counts the `k ∈ [1, n - 1]` with `gcd k (n - k) = 1` (`../Carmichael/Spec.lean`: `cp`,
  `cp_succ`, `cp_self`, `gcd_sub`); `k = 1` always counts (`cp_two`), and `cp n k < k` (`cp_lt`).
* A counterexample is a composite `n` with `φ(n) ∣ n - 1`: with `p = n - 1 - φ(n)`, iff `p ≥ 1`
  and `φ(n) ∣ p` (`bad_iff`).
-/

namespace TM.LehmerTotient
open TinyCryptids
open TM.Carmichael (cp cp_succ cp_one cp_self)

theorem cp_lt {n : Nat} (hn : 2 ≤ n) : ∀ k, 1 ≤ k → cp n k + 1 ≤ k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [cp_one hn]; omega
    · have := ih h; rw [cp_succ]; split <;> omega

theorem cp_mono (n a : Nat) : ∀ b, cp n a ≤ cp n (a + b) := by
  intro b
  induction b with
  | zero => exact Nat.le_refl _
  | succ b ih => rw [← Nat.add_assoc, cp_succ]; omega

theorem cp_two {n : Nat} (hn : 2 ≤ n) : cp n 2 = 1 := by
  rw [cp_succ, cp_one hn, if_pos (Nat.gcd_one_left n)]

theorem cp_pos {n : Nat} (hn : 2 ≤ n) (k : Nat) (hk : 2 ≤ k) : 1 ≤ cp n k := by
  have := cp_mono n 2 (k - 2); rw [cp_two hn, show 2 + (k - 2) = k by omega] at this; exact this

/-- `φ(n) ≥ 2` for `n ≥ 3`: `1` and `n - 1` -/
theorem totient_two {n : Nat} (hn : 3 ≤ n) : 2 ≤ totient n := by
  have h1 := cp_pos (show 2 ≤ n by omega) (n - 1) (by omega)
  have e := cp_succ n (n - 1)
  have hg : Nat.gcd (n - 1) n = 1 := by
    have := TM.Carmichael.gcd_sub (k := n - 1) (M := n) (by omega)
    rw [show n - (n - 1) = 1 by omega, Nat.gcd_one_right] at this; exact this.symm
  rw [if_pos hg, show n - 1 + 1 = n by omega, cp_self] at e
  omega

theorem totient_le {n : Nat} (hn : 2 ≤ n) : totient n + 1 ≤ n := by
  rw [← cp_self]; exact cp_lt hn n (by omega)

/-- Totatives of `n` below `j`. -/
def tc (n j : Nat) : Nat := ((List.range j).filter (fun k => Nat.gcd k n == 1)).length

theorem tc_succ (n j : Nat) : tc n (j + 1) = tc n j + (if Nat.gcd j n = 1 then 1 else 0) := by
  unfold tc
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : Nat.gcd j n = 1 <;> simp [h]

/-- A composite `n` misses at least the totatives `0` and a proper divisor `d`. -/
theorem totient_le_comp {n : Nat} (hn : 2 ≤ n) (hp : ¬ Prime n) : totient n + 2 ≤ n := by
  have : ∃ d, d < n ∧ 2 ≤ d ∧ n % d = 0 := by
    refine Classical.byContradiction fun hne => hp ⟨hn, fun d h1 h2 h3 => hne ⟨d, h1, h2, h3⟩⟩
  obtain ⟨d, hdn, hd2, hdd⟩ := this
  have hgd : Nat.gcd d n = d := Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero hdd)
  have key : ∀ j, tc n j + (if 0 < j then 1 else 0) + (if d < j then 1 else 0) ≤ j := by
    intro j
    induction j with
    | zero => simp [tc]
    | succ j ih =>
      rw [tc_succ]
      by_cases h0 : j = 0
      · subst h0
        have : Nat.gcd 0 n ≠ 1 := by rw [Nat.gcd_zero_left]; omega
        rw [if_neg this, if_pos (show 0 < 0 + 1 by omega), if_neg (show ¬ d < 0 + 1 by omega)]
        simp [tc]
      · by_cases hj : j = d
        · subst hj
          rw [if_neg (by omega)]
          simp only [if_pos (show 0 < j by omega), if_pos (show 0 < j + 1 by omega),
            if_neg (show ¬ j < j by omega), if_pos (show j < j + 1 by omega)] at ih ⊢
          omega
        · simp only [if_pos (show 0 < j by omega), if_pos (show 0 < j + 1 by omega)] at ih ⊢
          by_cases hdj : d < j
          · simp only [if_pos hdj, if_pos (show d < j + 1 by omega)] at ih ⊢; split <;> omega
          · simp only [if_neg hdj, if_neg (show ¬ d < j + 1 by omega)] at ih ⊢; split <;> omega
  have := key n
  rw [if_pos (by omega), if_pos hdn] at this
  exact this

/-- the test of the machine: `p = n - 1 - φ(n) ≥ 1` and `φ(n) ∣ p` -/
def Bad (n : Nat) : Prop := 1 ≤ n - 1 - totient n ∧ (n - 1 - totient n) % totient n = 0

theorem bad_iff {n : Nat} (hn : 2 ≤ n) : (¬ Prime n ∧ totient n ∣ n - 1) ↔ Bad n := by
  have hle := totient_le hn
  have hmod : (n - 1) % totient n = (n - 1 - totient n) % totient n := by
    rw [show n - 1 = (n - 1 - totient n) + totient n by omega, Nat.add_mod_right,
      Nat.add_sub_cancel]
  unfold Bad
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨by have := totient_le_comp hn hp; omega, by rw [← hmod]; exact Nat.mod_eq_zero_of_dvd hd⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun hp => ?_, Nat.dvd_of_mod_eq_zero (by rw [hmod]; exact h2)⟩
    rw [totient_prime hp] at h1; omega

end TM.LehmerTotient
