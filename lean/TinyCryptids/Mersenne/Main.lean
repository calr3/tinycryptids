import TinyCryptids.Mersenne.Round
import TinyCryptids.Mersenne.Spec

/-!
# Main theorem: the design quasihalts iff the Mersenne prime conjecture is false

The beep is the transition of state `G0` reading 0. Candidate `m` (odd, `m ≥ 5`) starts at
`CS m`. If `m` is a Mersenne prime, the run (without beeping) reaches `BeepCfg (m - 1)`,
takes the beep transition, and reaches `CS (m + 2)`; otherwise it reaches `CS (m + 2)`
without beeping (`deltaNB`, the design without its beep transition, runs from `CS m` to
`CS (m + 2)`). The start beeps for `m = 3` and reaches `CS 5`.
-/

namespace TM.Mersenne

open TinyCryptids
open St

/-- after the walk for `d` (with `m = d + r + 1`) the D hole is on cell `r % d`; `d` divides
`m` or `m + 1` iff that is D's last or second-to-last cell (the cells the check reads) -/
theorem fail_iff (d r : Nat) (hd : 3 ≤ d) :
    ¬ Good (d + r + 1) d ↔ (r % d + 1 = d ∨ r % d + 2 = d) := by
  have e := Nat.div_add_mod r d
  have hc := Nat.mod_lt r (show d > 0 by omega)
  generalize r % d = c at e hc
  generalize r / d = q at e
  have h1 : (d + r + 1) % d = (c + 1) % d := by
    rw [show d + r + 1 = d * (q + 1) + (c + 1) by rw [Nat.mul_add]; omega, Nat.mul_add_mod]
  have h2 : (d + r + 1 + 1) % d = (c + 2) % d := by
    rw [show d + r + 1 + 1 = d * (q + 1) + (c + 2) by rw [Nat.mul_add]; omega, Nat.mul_add_mod]
  unfold Good
  rw [h1, h2]
  constructor
  · intro h
    apply Classical.byContradiction; intro hno
    exact h ⟨by rw [Nat.mod_eq_of_lt (by omega)]; omega,
      by rcases Nat.lt_or_ge (c + 2) d with hl | hl
         · rw [Nat.mod_eq_of_lt hl]; omega
         · rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega)]; omega⟩
  · rintro (h | h) ⟨ha, hb⟩
    · rw [h, Nat.mod_self] at ha; exact ha rfl
    · rw [h, Nat.mod_self] at hb; exact hb rfl

/-! ## trial division of one candidate -/

/-- the round for `d` (`r = 2 t + 1`, `m = d + r + 1`), every odd `e < d` already passed:
the run reaches the beep if every odd `e` with `d ≤ e < m` passes, and the next candidate
otherwise -/
theorem test : ∀ t d, 3 ≤ d → d % 2 = 1 →
    (∀ e, 3 ≤ e → e < d → e % 2 = 1 → Good (d + 2 * t + 2) e) →
    ((∀ e, d ≤ e → e < d + 2 * t + 2 → e % 2 = 1 → Good (d + 2 * t + 2) e) →
      Rch (WS d (2 * t + 1)) (BeepCfg (d + 2 * t + 1))) ∧
    (¬ (∀ e, d ≤ e → e < d + 2 * t + 2 → e % 2 = 1 → Good (d + 2 * t + 2) e) →
      Rch (WS d (2 * t + 1)) (CS (d + 2 * t + 4))) := by
  intro t
  induction t with
  | zero =>
    intro d hd hdo _
    have w := Rch.tr (walk_all d 1 (by omega)) (walk_end d 0 (1 % d))
    have hc : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
    have hf := fail_iff d 1 hd
    rw [hc] at w hf
    by_cases hg : Good (d + 2 * 0 + 2) d
    · have h1 : 1 + 1 ≠ d := fun h => hf.2 (Or.inl h) hg
      have h2 : 1 + 2 ≠ d := fun h => hf.2 (Or.inr h) hg
      have := Rch.tr w (check_ok d 0 1 (by omega))
      exact ⟨fun _ => this, fun hn => absurd (fun e h1 h2 h3 => by
        rw [show e = d by omega]; exact hg) hn⟩
    · have := Rch.tr w (check_fail d 0 1 hd (hf.1 hg))
      exact ⟨fun hall => absurd (hall d (Nat.le_refl _) (by omega) hdo) hg,
        fun _ => by rw [show d + 0 + 1 + 3 = d + 2 * 0 + 4 by omega] at this; exact this⟩
  | succ t ih =>
    intro d hd hdo hbelow
    have hc := Nat.mod_lt (2 * (t + 1) + 1) (show d > 0 by omega)
    have w := Rch.tr (walk_all d (2 * (t + 1) + 1) (by omega))
      (walk_end d (2 * (t + 1)) ((2 * (t + 1) + 1) % d))
    have hf := fail_iff d (2 * (t + 1) + 1) hd
    rw [show d + (2 * (t + 1) + 1) + 1 = d + 2 * (t + 1) + 2 by omega] at hf
    generalize (2 * (t + 1) + 1) % d = c at w hf hc
    by_cases hg : Good (d + 2 * (t + 1) + 2) d
    · -- d passes: d := d + 2
      have h1 : c + 1 ≠ d := fun h => hf.2 (Or.inl h) hg
      have h2 : c + 2 ≠ d := fun h => hf.2 (Or.inr h) hg
      have st := Rch.tr w (check_ok d _ _ (by omega))
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega] at st
      have st2 := Rch.tr st (shift d (2 * t + 1) (by omega))
      have h := ih (d + 2) (by omega) (by omega) (fun e h1 h2 h3 => by
        rw [show d + 2 + 2 * t + 2 = d + 2 * (t + 1) + 2 by omega]
        rcases Nat.lt_or_ge e d with he | he
        · exact hbelow e h1 he h3
        · rw [show e = d by omega]; exact hg)
      rw [show d + 2 + 2 * t + 2 = d + 2 * (t + 1) + 2 by omega,
        show d + 2 + 2 * t + 1 = d + 2 * (t + 1) + 1 by omega,
        show d + 2 + 2 * t + 4 = d + 2 * (t + 1) + 4 by omega] at h
      refine ⟨fun hall => Rch.tr st2 (h.1 fun e h1 h2 h3 => hall e (by omega) h2 h3),
        fun hn => Rch.tr st2 (h.2 fun hall => hn fun e h1 h2 h3 => ?_)⟩
      rcases Nat.lt_or_ge e (d + 2) with he | he
      · rw [show e = d by omega]; exact hg
      · exact hall e he h2 h3
    · -- d divides m or m + 1: fail
      have := Rch.tr w (check_fail d _ _ hd (hf.1 hg))
      rw [show d + 2 * (t + 1) + 1 + 3 = d + 2 * (t + 1) + 4 by omega] at this
      exact ⟨fun hall => absurd (hall d (Nat.le_refl _) (by omega) hdo) hg, fun _ => this⟩

theorem cand_mp (m : Nat) (hm : 5 ≤ m) (ho : m % 2 = 1) (h : MP m) :
    Rch (CS m) (BeepCfg (m - 1)) := by
  have t := test ((m - 5) / 2) 3 (Nat.le_refl _) rfl (fun e h1 h2 _ => by omega)
  rw [show 3 + 2 * ((m - 5) / 2) + 2 = m by omega, show 2 * ((m - 5) / 2) + 1 = m - 4 by omega,
    show 3 + 2 * ((m - 5) / 2) + 1 = m - 1 by omega] at t
  exact t.1 fun e h1 h2 h3 => (mersenne_iff m (by omega) ho).1 h e (by omega) h2 h3

theorem cand_not (m : Nat) (hm : 5 ≤ m) (ho : m % 2 = 1) (h : ¬ MP m) :
    Rch (CS m) (CS (m + 2)) := by
  have t := test ((m - 5) / 2) 3 (Nat.le_refl _) rfl (fun e h1 h2 _ => by omega)
  rw [show 3 + 2 * ((m - 5) / 2) + 2 = m by omega, show 2 * ((m - 5) / 2) + 1 = m - 4 by omega,
    show 3 + 2 * ((m - 5) / 2) + 4 = m + 2 by omega] at t
  exact t.2 fun hall => h ((mersenne_iff m (by omega) ho).2 fun e h1 h2 h3 => hall e h1 h2 h3)

/-- the beep and the rebuild: from `BeepCfg (m - 1)` to the next candidate -/
theorem after_beep (n : Nat) (hn : 2 ≤ n) : Reach delta (BeepCfg n) (CS (n + 3)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine Reach.trans delta (beep_step k) (Reach.sub deltaNB_sub ?_)
  have := rebuild k 1 (Nat.le_refl _) (by omega)
  rw [show k + 1 + 3 = k + 1 + 3 from rfl] at this; exact this

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

theorem CS_ne (m : Nat) (hm : 5 ≤ m) : CS m ≠ CS (m + 2) := by
  intro h
  have := congrArg (fun c => c.R (m - 4)) h
  simp only [CS, WS, W, Nat.sub_zero, show m + 2 - 4 = m - 4 + 2 by omega] at this
  rw [ones_get_self, ones_get_lt _ _ _ (by omega)] at this
  exact absurd this (by simp [blank])

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {δ : St → Bool → Option (Bool × Dir × St)} {a b : Cfg St}
    (h : Reach δ a b) (hne : a ≠ b) : Reach1 δ a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

/-- every candidate leads to the next one -/
theorem cand_step (m : Nat) (hm : 5 ≤ m) (ho : m % 2 = 1) : Reach1 delta (CS m) (CS (m + 2)) := by
  refine reach1_of_ne ?_ (CS_ne m hm)
  by_cases h : MP m
  · have := after_beep (m - 1) (by omega)
    rw [show m - 1 + 3 = m + 2 by omega] at this
    exact Reach.trans delta (Reach.sub deltaNB_sub (cand_mp m hm ho h)) this
  · exact Reach.sub deltaNB_sub (cand_not m hm ho h)

/-- the start of candidate `2 k + 5` is reached after at least `k` steps -/
theorem reach_cs : ∀ k, ∃ t, k ≤ t ∧ run delta t start = some (CS (2 * k + 5)) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨t, ht⟩ := Reach.trans delta (Reach.sub deltaNB_sub seed) (after_beep 2 (by omega))
    exact ⟨t, Nat.zero_le _, ht⟩
  | succ k ih =>
    obtain ⟨t, ht, hr⟩ := ih
    obtain ⟨n, hn⟩ := cand_step (2 * k + 5) (by omega) (by omega)
    exact ⟨t + (n + 1), by omega, by
      rw [run_add, hr, show 2 * (k + 1) + 5 = 2 * k + 5 + 2 by omega]; exact hn⟩

/-! ## the main theorem -/

/-- The design never halts. -/
theorem never_halts : ¬ Halts delta start := by
  intro hh
  have prog : ∀ c, (∃ m, 5 ≤ m ∧ m % 2 = 1 ∧ c = CS m) →
      ∃ c', (∃ m, 5 ≤ m ∧ m % 2 = 1 ∧ c' = CS m) ∧ Reach1 delta c c' := by
    rintro c ⟨m, hm, ho, rfl⟩
    exact ⟨CS (m + 2), ⟨m + 2, by omega, by omega, rfl⟩, cand_step m hm ho⟩
  obtain ⟨t, _, hr⟩ := reach_cs 0
  exact not_halts_of_progress delta _ prog _ ⟨5, Nat.le_refl _, rfl, rfl⟩
    (Sys.Halts.of_reach ⟨t, hr⟩ hh)

theorem MP.odd {m : Nat} (h : MP m) (h3 : 3 ≤ m) : m % 2 = 1 := by
  have := h.1.2 2 (by omega) (Nat.le_refl _)
  omega

/-- **Main theorem.** Started on a blank tape, the design takes its beep transition (state
`G0` reading 0) only finitely often if and only if the Mersenne prime conjecture is false. -/
theorem quasihalts_iff : QuasiHalts delta G0 false start ↔ ¬ MersennePrimeConjecture := by
  rw [mpc_iff]
  constructor
  · rintro ⟨N, hN⟩ hmpc
    obtain ⟨m, hm, hmp⟩ := hmpc (2 * N + 5)
    have ho := hmp.odd (by omega)
    obtain ⟨t, ht, hr⟩ := reach_cs ((m - 5) / 2)
    rw [show 2 * ((m - 5) / 2) + 5 = m by omega] at hr
    obtain ⟨s, hs⟩ := Reach.sub deltaNB_sub (cand_mp m (by omega) ho hmp)
    exact hN (t + s) (by omega)
      ⟨BeepCfg (m - 1), by rw [run_add, hr]; exact hs, rfl, rfl, by simp [delta]⟩
  · intro hn
    have hN : ∃ N, ∀ m, N ≤ m → ¬ MP m := by
      apply Classical.byContradiction; intro hno
      exact hn fun N => Classical.byContradiction fun hp =>
        hno ⟨N, fun m h1 h2 => hp ⟨m, h1, h2⟩⟩
    obtain ⟨N, hN⟩ := hN
    obtain ⟨t, _, hr⟩ := reach_cs N
    refine quasihalts_of_sub deltaNB_sub rfl ⟨t, hr⟩ ?_
    have prog : ∀ c, (∃ m, 2 * N + 5 ≤ m ∧ m % 2 = 1 ∧ c = CS m) →
        ∃ c', (∃ m, 2 * N + 5 ≤ m ∧ m % 2 = 1 ∧ c' = CS m) ∧ Reach1 deltaNB c c' := by
      rintro c ⟨m, hm, ho, rfl⟩
      exact ⟨CS (m + 2), ⟨m + 2, by omega, by omega, rfl⟩,
        reach1_of_ne (cand_not m (by omega) ho (hN m (by omega))) (CS_ne m (by omega))⟩
    exact not_halts_of_progress deltaNB _ prog _ ⟨2 * N + 5, Nat.le_refl _, by omega, rfl⟩

/-- Equivalently: the design beeps infinitely often iff the Mersenne prime conjecture holds. -/
theorem beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta G0 false start n) ↔ MersennePrimeConjecture := by
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    exact not_quasiHalts h (quasihalts_iff.2 hn)
  · intro h N; apply Classical.byContradiction; intro hno
    refine quasihalts_iff.1 ⟨N, fun n hn hb => hno ⟨n, hn, hb⟩⟩ h

end TM.Mersenne
