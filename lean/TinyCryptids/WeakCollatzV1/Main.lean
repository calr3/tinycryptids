import TinyCryptids.WeakCollatzV1.Step

/-!
# Main theorem: the design halts iff the Collatz map has a nontrivial cycle
-/

namespace TM.WeakCollatzV1

open TinyCryptids St

/-- One round: from `RS n` the machine halts or reaches `RS (n + 1)`, as the
first `i` with `Cond n (it (i + 1) n)` says. -/
theorem round (n : Nat) (hn : 1 ≤ n) (i : Nat) (hfirst : ∀ j, j < i → ¬ Cond n (it (j + 1) n))
    (hc : Cond n (it (i + 1) n)) :
    (it (i + 1) n = n → HaltAt (RS n)) ∧ (it (i + 1) n ≠ n → Rch1 (RS n) (RS (n + 1))) := by
  have r := round_run n i n hn (Nat.le_refl _) hfirst hc
  exact ⟨fun h => HaltAt.back (rs_pb n hn).reach (r.1 h),
    fun h => Reach1.trans_reach delta (rs_pb n hn) (r.2 h)⟩

theorem start_reach : Rch start (RS 1) := by
  unfold start RS
  refine blankR ?_; gR
  refine blankR ?_; gR
  refine blankR ?_; gL; gL
  fin

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- With a nontrivial cycle, the machine reaches its explicit halting state. -/
theorem haltAt_of_cycle (h : ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    HaltAt start := by
  obtain ⟨M, hM2, hM, k, hk, hkM, hv⟩ := exists_top h
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
    exact (round M (by omega) i hfirst hi).1 hval
  -- every earlier round halts or passes to the next
  suffices H : ∀ d m, m + d = M → 1 ≤ m → HaltAt (RS m) from
    HaltAt.back start_reach (H (M - 1) 1 (by omega) (Nat.le_refl _))
  intro d
  induction d with
  | zero => intro m h _; subst h; exact hlast
  | succ d ih =>
    intro m h hm
    obtain ⟨i, hi, hfirst⟩ := first_index (round_stops m hm (hM.mono (by omega)))
    rcases Classical.em (it (i + 1) m = m) with he | he
    · exact (round m hm i hfirst hi).1 he
    · exact HaltAt.back ((round m hm i hfirst hi).2 he).reach (ih (m + 1) (by omega) (by omega))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if the
Collatz map has a cycle other than `1 → 4 → 2 → 1`. -/
theorem halts_iff :
    Halts delta start ↔ ∃ n k, 0 < n ∧ 0 < k ∧ iterate collatz k n = n ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ n, 1 ≤ n ∧ c = RS n) → ∃ c', (∃ n, 1 ≤ n ∧ c' = RS n) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      obtain ⟨i, hi, hfirst⟩ := first_index (round_stops n hn (nocyc_of_not hno n))
      have hne := round_no_return n hn (nocyc_of_not hno (n + 1)) i hfirst
      exact ⟨RS (n + 1), ⟨n + 1, by omega, rfl⟩, (round n hn i hfirst hi).2 hne⟩
    exact not_halts_of_progress delta _ prog _ ⟨1, Nat.le_refl _, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of_cycle h).halts

end TM.WeakCollatzV1
