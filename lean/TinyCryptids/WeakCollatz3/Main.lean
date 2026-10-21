import TinyCryptids.WeakCollatz3.Step
import TinyCryptids.WeakCollatz.Cycle

/-!
# Main theorem: the 3-symbol machine halts iff the Collatz map has a nontrivial cycle
-/

namespace TM3.WeakCollatz

open TinyCryptids TM.WeakCollatz St Sym

/-- One round: from `RS n` the machine halts or reaches `RS (n + 1)`, as the
first `i` with `Cond n (it (i + 1) n)` says. -/
theorem round (n : Nat) (hn : 2 ≤ n) (i : Nat) (hfirst : ∀ j, j < i → ¬ Cond n (it (j + 1) n))
    (hc : Cond n (it (i + 1) n)) :
    (it (i + 1) n = n → HaltAt (RS n)) ∧ (it (i + 1) n ≠ n → Rch1 (RS n) (RS (n + 1))) := by
  rw [← cs_self]; exact round_run n i n hn (Nat.le_refl _) hfirst hc

/-- from the blank tape, `disp` acts as for `v = 1`: round 3 starts -/
theorem start_reach : Rch start (RS 3) := by
  unfold start RS
  refine blankR ?_
  gR
  refine blankR ?_
  gR
  refine blankR ?_
  gL
  exact go_home2 1 0 _

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- With a cycle of `tc` through some `n ≥ 3`, the machine reaches its halting state. -/
theorem haltAt_of_counter (h : Counter) : HaltAt start := by
  obtain ⟨M, hM2, hM, k, hk, hkM, hv⟩ := exists_top h
  -- the top of the cycle is not 2: `tc 2 = 1`
  have hM3 : 3 ≤ M := by
    have := (hv 1 hk).1
    rcases Nat.lt_or_ge M 3 with h3 | h3
    · obtain rfl : M = 2 := by omega
      exact absurd this (by decide)
    · exact h3
  -- round `M` halts
  have hlast : HaltAt (RS M) := by
    obtain ⟨i, hi, hfirst⟩ := first_index (P := fun i => Cond M (it (i + 1) M))
      ⟨k - 1, Or.inr (by rw [show k - 1 + 1 = k by omega, hkM]; exact Nat.le_refl _)⟩
    have hik : i + 1 ≤ k := by
      apply Classical.byContradiction; intro hik
      exact hfirst (k - 1) (by omega)
        (Or.inr (by rw [show k - 1 + 1 = k by omega, hkM]; exact Nat.le_refl _))
    have hval : it (i + 1) M = M := by
      have := hv (i + 1) hik; unfold Cond at hi; omega
    exact (round M hM2 i hfirst hi).1 hval
  -- every earlier round halts or passes to the next
  suffices H : ∀ d m, m + d = M → 3 ≤ m → HaltAt (RS m) from
    HaltAt.back start_reach (H (M - 3) 3 (by omega) (Nat.le_refl _))
  intro d
  induction d with
  | zero => intro m h _; subst h; exact hlast
  | succ d ih =>
    intro m h hm
    obtain ⟨i, hi, hfirst⟩ := first_index (round_stops m (by omega) (hM.mono (by omega)))
    rcases Classical.em (it (i + 1) m = m) with he | he
    · exact (round m (by omega) i hfirst hi).1 he
    · exact HaltAt.back ((round m (by omega) i hfirst hi).2 he).reach (ih (m + 1) (by omega) (by omega))

/-- the machine halts iff the shortcut map has a cycle other than `1 → 2 → 1` -/
theorem halts_iff_counter : Halts delta start ↔ Counter := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ n, 3 ≤ n ∧ c = RS n) → ∃ c', (∃ n, 3 ≤ n ∧ c' = RS n) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      obtain ⟨i, hi, hfirst⟩ := first_index (round_stops n (by omega) (nocyc_of_not hno n))
      have hne := round_no_return n (by omega) (nocyc_of_not hno (n + 1)) i hfirst
      exact ⟨RS (n + 1), ⟨n + 1, by omega, rfl⟩, (round n (by omega) i hfirst hi).2 hne⟩
    exact not_halts_of_progress delta _ prog _ ⟨3, Nat.le_refl _, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of_counter h).halts

/-- **Main theorem.** Started on a blank tape, the 10-state, 3-symbol machine halts if and only
if the Collatz map has a cycle other than `1 → 4 → 2 → 1`. -/
theorem halts_iff :
    Halts delta start ↔ ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4 :=
  halts_iff_counter.trans counter_iff

end TM3.WeakCollatz
