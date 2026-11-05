import TinyCryptids.Amicable.Round
import TinyCryptids.Core.Beep

/-!
# Main theorem: the design quasihalts iff there are finitely many amicable numbers

The beep is the transition of state `H5` reading 0. The round for `x = k + 1` starts at
`CS k`. If `x` is the smaller number of an amicable pair (`Small x`), the run (without
beeping) reaches `BeepCfg`, takes the beep transition, and reaches `CS (k + 1)`; otherwise
it reaches `CS (k + 1)` without beeping. `inf_iff` (`Spec.lean`): there are infinitely many
amicable numbers iff there are infinitely many `x` with `Small x`.
-/

namespace TM.Amicable

open TinyCryptids
open St

theorem ones_get_lt (a i : Nat) (X : Strm) (h : i < a) : ones a X i = true := by
  induction a generalizing i with
  | zero => omega
  | succ a ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem ones_get_self (a : Nat) (X : Strm) : ones a X a = X 0 := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

theorem CS_ne (k : Nat) : CS k ≠ CS (k + 1) := by
  intro h
  have := congrArg (fun c => c.L k) h
  simp only [CS] at this
  rw [ones_get_self, ones_get_lt _ _ _ (by omega)] at this
  exact absurd this (by simp [blank])

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {δ : St → Bool → Option (Bool × Dir × St)} {a b : Cfg St}
    (h : Reach δ a b) (hne : a ≠ b) : Reach1 δ a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

/-- every round leads to the next one -/
theorem round_step (k : Nat) : Reach1 delta (CS k) (CS (k + 1)) := by
  refine reach1_of_ne ?_ (CS_ne k)
  by_cases h : Small (k + 1)
  · obtain ⟨q, hq⟩ := round_beep k h
    exact Reach.trans delta (Reach.sub deltaNB_sub hq) (after_beep q (k + 1) (by omega))
  · exact Reach.sub deltaNB_sub (round_no k h)

/-- the start of round `k` is reached after at least `k` steps -/
theorem reach_cs : ∀ k, ∃ t, k ≤ t ∧ run delta t start = some (CS k) := by
  intro k
  induction k with
  | zero => exact ⟨0, Nat.le_refl _, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht, hr⟩ := ih
    obtain ⟨n, hn⟩ := round_step k
    exact ⟨t + (n + 1), by omega, by rw [run_add, hr]; exact hn⟩

/-- The design never halts. -/
theorem never_halts : ¬ Halts delta start := by
  intro hh
  have prog : ∀ c, (∃ k, c = CS k) → ∃ c', (∃ k, c' = CS k) ∧ Reach1 delta c c' := by
    rintro c ⟨k, rfl⟩
    exact ⟨CS (k + 1), ⟨k + 1, rfl⟩, round_step k⟩
  exact not_halts_of_progress delta _ prog _ ⟨0, rfl⟩ hh

/-- **Main theorem.** Started on a blank tape, the design takes its beep transition (state
`H5` reading 0) only finitely often if and only if there are only finitely many amicable
numbers. -/
theorem quasihalts_iff : QuasiHalts delta H5 false start ↔ ¬ InfinitelyManyAmicable := by
  rw [inf_iff]
  constructor
  · rintro ⟨N, hN⟩ hinf
    obtain ⟨x, hx, hs⟩ := hinf (N + 1)
    obtain ⟨t, ht, hr⟩ := reach_cs (x - 1)
    have hs' : Small (x - 1 + 1) := by rw [show x - 1 + 1 = x by omega]; exact hs
    obtain ⟨q, hq⟩ := round_beep (x - 1) hs'
    obtain ⟨s, hs⟩ := Reach.sub deltaNB_sub hq
    exact hN (t + s) (by omega)
      ⟨BeepCfg (x - 1 + 1) q, by rw [run_add, hr]; exact hs, rfl, rfl, fun h => Option.noConfusion h⟩
  · intro hn
    have hN : ∃ N, ∀ x, N ≤ x → ¬ Small x := by
      apply Classical.byContradiction; intro hno
      exact hn fun N => Classical.byContradiction fun hp =>
        hno ⟨N, fun x h1 h2 => hp ⟨x, h1, h2⟩⟩
    obtain ⟨N, hN⟩ := hN
    obtain ⟨t, _, hr⟩ := reach_cs N
    refine quasihalts_of_sub deltaNB_sub rfl ⟨t, hr⟩ ?_
    have prog : ∀ c, (∃ k, N ≤ k ∧ c = CS k) →
        ∃ c', (∃ k, N ≤ k ∧ c' = CS k) ∧ Reach1 deltaNB c c' := by
      rintro c ⟨k, hk, rfl⟩
      exact ⟨CS (k + 1), ⟨k + 1, by omega, rfl⟩,
        reach1_of_ne (round_no k (hN (k + 1) (by omega))) (CS_ne k)⟩
    exact not_halts_of_progress deltaNB _ prog _ ⟨N, Nat.le_refl _, rfl⟩

/-- Equivalently: the design beeps infinitely often iff there are infinitely many amicable
numbers. -/
theorem beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta H5 false start n) ↔ InfinitelyManyAmicable := by
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    exact not_quasiHalts h (quasihalts_iff.2 hn)
  · intro h N; apply Classical.byContradiction; intro hno
    refine quasihalts_iff.1 ⟨N, fun n hn hb => hno ⟨n, hn, hb⟩⟩ h

end TM.Amicable
