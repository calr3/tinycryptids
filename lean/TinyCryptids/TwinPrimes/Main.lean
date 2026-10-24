import TinyCryptids.TwinPrimes.Round
import TinyCryptids.TwinPrimes.Spec

/-!
# Main theorem: the design quasihalts iff the twin prime conjecture is false

The beep is the transition of state `G2` reading 0. Candidate `m` starts at `CS m`. If `m`
and `m + 2` are both prime, the run (without beeping) reaches `BeepCfg (m - 1)`, takes the
beep transition, and reaches `CS (m + 1)`; otherwise it reaches `CS (m + 1)` without beeping
(`deltaNB`, the design without its beep transition, runs from `CS m` to `CS (m + 1)`).
-/

namespace TM.TwinPrimes

open TinyCryptids
open St

/-! ## trial division of one candidate -/

/-- the tests for `d, d + 1, …, m - 1` (`m = d + r`), every `e < d` already passed: the run
reaches the beep if all of them pass, and the next candidate otherwise -/
theorem test : ∀ r d, 2 ≤ d → 1 ≤ r → (∀ e, 2 ≤ e → e < d → Good (d + r) e) →
    ((∀ e, d ≤ e → e < d + r → Good (d + r) e) → Rch (WS d r) (BeepCfg (d + r - 1))) ∧
    (¬ (∀ e, d ≤ e → e < d + r → Good (d + r) e) → Rch (WS d r) (CS (d + r + 1))) := by
  intro r
  induction r with
  | zero => intro d _ h; omega
  | succ r ih =>
    intro d hd _ hbelow
    have walk' := walk d (r + 1) (r + 1) (d - 1) (Nat.le_refl _) (by omega)
    have hc := Nat.mod_lt (d - 1 + (r + 1)) (show d > 0 by omega)
    have hf := fail_iff d (d + (r + 1)) hd (by omega)
    rw [show d + (r + 1) - 1 = d - 1 + (r + 1) by omega] at hf
    by_cases hg : Good (d + (r + 1)) d
    · -- d passes: shift
      obtain ⟨a, b, hab, hok⟩ := check_ok d (r + 1) _ hd hc (fun h => hf.2 h hg)
      have st := Rch.tr walk' hok
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · -- r + 1 = 1: d = m - 1 was the last divisor
        have := Rch.tr st (shift_beep a b)
        rw [hab] at this
        refine ⟨fun _ => by rw [show d + (0 + 1) - 1 = d by omega]; exact this, fun hn => ?_⟩
        exact absurd (fun e h1 h2 => by rw [show e = d by omega]; exact hg) hn
      · have st2 := Rch.tr st (shift_more a b (r + 1) (by omega))
        rw [hab, show r + 1 - 1 = r by omega] at st2
        have h := ih (d + 1) (by omega) hr (fun e h1 h2 => by
          rw [show d + 1 + r = d + (r + 1) by omega]
          rcases Nat.lt_or_ge e d with he | he
          · exact hbelow e h1 he
          · rw [show e = d by omega]; exact hg)
        rw [show d + 1 + r = d + (r + 1) by omega] at h
        refine ⟨fun hall => Rch.tr st2 (h.1 fun e h1 h2 => hall e (by omega) h2),
          fun hn => Rch.tr st2 (h.2 fun hall => hn fun e h1 h2 => ?_)⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | he
        · exact hg
        · exact hall e (by omega) h2
    · -- d divides m or m + 2: fail
      have := Rch.tr walk' (check_fail d (r + 1) _ hd (hf.1 hg))
      exact ⟨fun hall => absurd (hall d (Nat.le_refl _) (by omega)) hg, fun _ => this⟩

theorem cand_twin (m : Nat) (hm : 3 ≤ m) (h : Prime m ∧ Prime (m + 2)) :
    Rch (CS m) (BeepCfg (m - 1)) := by
  have t := test (m - 2) 2 (Nat.le_refl _) (by omega) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at t
  exact t.1 fun e h1 h2 => (twin_iff m hm).1 h e h1 h2

theorem cand_not (m : Nat) (hm : 3 ≤ m) (h : ¬ (Prime m ∧ Prime (m + 2))) :
    Rch (CS m) (CS (m + 1)) := by
  have t := test (m - 2) 2 (Nat.le_refl _) (by omega) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at t
  exact t.2 fun hall => h ((twin_iff m hm).2 fun e h1 h2 => hall e h1 h2)

/-- after the beep the walk ends at once and the check fails (`m` divides `m`) -/
theorem after_beep (m : Nat) (hm : 3 ≤ m) : Reach delta (BeepCfg (m - 1)) (CS (m + 1)) := by
  refine Reach.trans delta (beep_step (m - 1)) (Reach.sub deltaNB_sub ?_)
  have := check_fail (m - 1 + 1) 0 (m - 1) (by omega) (Or.inl rfl)
  rw [show m - 1 + 1 + 0 + 1 = m + 1 by omega] at this; exact this

/-! ## progress -/

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

theorem CS_ne (m : Nat) (hm : 3 ≤ m) : CS m ≠ CS (m + 1) := by
  intro h
  have := congrArg (fun c => c.L (m - 3)) h
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  simp only [CS, WS, show k + 3 - 2 = k + 1 by omega, show k + 3 + 1 - 2 = k + 1 + 1 by omega,
    W, show k + 3 - 3 = k by omega] at this
  rw [ones_get_self, ones_get_lt _ _ _ (by omega)] at this
  exact absurd this (by simp)

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {δ : St → Bool → Option (Bool × Dir × St)} {a b : Cfg St}
    (h : Reach δ a b) (hne : a ≠ b) : Reach1 δ a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

/-- every candidate leads to the next one -/
theorem cand_step (m : Nat) (hm : 3 ≤ m) : Reach1 delta (CS m) (CS (m + 1)) := by
  refine reach1_of_ne ?_ (CS_ne m hm)
  by_cases h : Prime m ∧ Prime (m + 2)
  · exact Reach.trans delta (Reach.sub deltaNB_sub (cand_twin m hm h)) (after_beep m hm)
  · exact Reach.sub deltaNB_sub (cand_not m hm h)

/-- the start of candidate `k + 3` is reached after at least `k` steps -/
theorem reach_cs : ∀ k, ∃ t, k ≤ t ∧ run delta t start = some (CS (k + 3)) := by
  intro k
  induction k with
  | zero => obtain ⟨t, ht⟩ := Reach.sub deltaNB_sub seed; exact ⟨t, Nat.zero_le _, ht⟩
  | succ k ih =>
    obtain ⟨t, ht, hr⟩ := ih
    obtain ⟨n, hn⟩ := cand_step (k + 3) (by omega)
    exact ⟨t + (n + 1), by omega, by rw [run_add, hr]; exact hn⟩

/-! ## the main theorem -/

/-- The design never halts. -/
theorem never_halts : ¬ Halts delta start := by
  intro hh
  have prog : ∀ c, (∃ m, 3 ≤ m ∧ c = CS m) → ∃ c', (∃ m, 3 ≤ m ∧ c' = CS m) ∧ Reach1 delta c c' := by
    rintro c ⟨m, hm, rfl⟩
    exact ⟨CS (m + 1), ⟨m + 1, by omega, rfl⟩, cand_step m hm⟩
  obtain ⟨t, _, hr⟩ := reach_cs 0
  exact not_halts_of_progress delta _ prog _ ⟨3, Nat.le_refl _, rfl⟩
    (Sys.Halts.of_reach ⟨t, hr⟩ hh)

/-- **Main theorem.** Started on a blank tape, the design takes its beep transition (state
`G2` reading 0) only finitely often if and only if the twin prime conjecture is false. -/
theorem quasihalts_iff : QuasiHalts delta G2 false start ↔ ¬ TwinPrimeConjecture := by
  constructor
  · rintro ⟨N, hN⟩ htpc
    obtain ⟨p, hp, hpp⟩ := htpc (N + 3)
    obtain ⟨t, ht, hr⟩ := reach_cs (p - 3)
    rw [show p - 3 + 3 = p by omega] at hr
    obtain ⟨s, hs⟩ := Reach.sub deltaNB_sub (cand_twin p (by omega) hpp)
    exact hN (t + s) (by omega)
      ⟨BeepCfg (p - 1), by rw [run_add, hr]; exact hs, rfl, rfl, by simp [delta]⟩
  · intro hn
    have hN : ∃ N, ∀ p, N ≤ p → ¬ (Prime p ∧ Prime (p + 2)) := by
      apply Classical.byContradiction; intro hno
      exact hn fun n => Classical.byContradiction fun hp => hno ⟨n, fun p h1 h2 => hp ⟨p, h1, h2⟩⟩
    obtain ⟨N, hN⟩ := hN
    obtain ⟨t, _, hr⟩ := reach_cs N
    refine quasihalts_of_sub deltaNB_sub rfl ⟨t, hr⟩ ?_
    have prog : ∀ c, (∃ m, N + 3 ≤ m ∧ c = CS m) →
        ∃ c', (∃ m, N + 3 ≤ m ∧ c' = CS m) ∧ Reach1 deltaNB c c' := by
      rintro c ⟨m, hm, rfl⟩
      exact ⟨CS (m + 1), ⟨m + 1, by omega, rfl⟩,
        reach1_of_ne (cand_not m (by omega) (hN m (by omega))) (CS_ne m (by omega))⟩
    exact not_halts_of_progress deltaNB _ prog _ ⟨N + 3, Nat.le_refl _, rfl⟩

/-- Equivalently: the design beeps infinitely often iff the twin prime conjecture holds. -/
theorem beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta G2 false start n) ↔ TwinPrimeConjecture := by
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    exact not_quasiHalts h (quasihalts_iff.2 hn)
  · intro h N; apply Classical.byContradiction; intro hno
    refine quasihalts_iff.1 ⟨N, fun n hn hb => hno ⟨n, hn, hb⟩⟩ h

end TM.TwinPrimes
