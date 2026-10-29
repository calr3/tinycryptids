import TinyCryptids.TwinPrimes4.Round
import TinyCryptids.TwinPrimes.Spec

/-!
# Main theorem: the 4-symbol machine quasihalts iff the twin prime conjecture is false

The beep is the transition of state `beep` reading 0. Candidate `m` starts at `CS m`. If `m`
and `m + 2` are both prime, the run (without beeping) reaches `BeepAt (m - 1) 1`, beeps, and
reaches `CS (m + 3)`; otherwise it reaches `CS (m + 1)` without beeping. The blank tape beeps
once and reaches `CS 3`. So the candidates run through every `m ≥ 3` except `p + 1` and `p + 2`
for each lesser twin prime `p`; only the twin prime 5 is skipped (`twin_gap`), and the
machine beeps at every other one (`reach_twin`).
-/

namespace TMK.TwinPrimes4

open TinyCryptids TM.TwinPrimes St

/-- `m` is a lesser twin prime -/
def Tw (m : Nat) : Prop := Prime m ∧ Prime (m + 2)

/-! ## trial division of one candidate -/

/-- the tests for `d, d + 1, …, m - 1` (`m = d + r`), every `e < d` already passed: the run
reaches the beep if all of them pass, and the next candidate otherwise -/
theorem test : ∀ r d, 2 ≤ d → (∀ e, 2 ≤ e → e < d → Good (d + r) e) →
    ((∀ e, d ≤ e → e < d + r → Good (d + r) e) → Rch (ZS d r) (BeepAt (d + r - 1) 1)) ∧
    (¬ (∀ e, d ≤ e → e < d + r → Good (d + r) e) → Rch (ZS d r) (CS (d + r + 1))) := by
  intro r
  induction r with
  | zero =>
    intro d hd _
    exact ⟨fun _ => zs_beep d (by omega), fun hn => absurd (fun e h1 h2 => by omega) hn⟩
  | succ r ih =>
    intro d hd hbelow
    have w := Rch.tr (walk_start d (r + 1))
      (walk d (r + 1) (r + 1) (d - 1) (by omega) (Nat.le_refl _))
    have hc := Nat.mod_lt (d - 1 + (r + 1)) (show d > 0 by omega)
    have hf := fail_iff d (d + (r + 1)) hd (by omega)
    rw [show d + (r + 1) - 1 = d - 1 + (r + 1) by omega] at hf
    by_cases hg : Good (d + (r + 1)) d
    · -- d passes: the walk for d + 1
      have st := Rch.tr w (check_ok d (r + 1) _ hd hc (by omega)
        (fun h => hf.2 (Or.inl h) hg) (fun h => hf.2 (Or.inr h) hg))
      rw [show r + 1 - 1 = r by omega] at st
      have h := ih (d + 1) (by omega) (fun e h1 h2 => by
        rw [show d + 1 + r = d + (r + 1) by omega]
        rcases Nat.lt_or_ge e d with he | he
        · exact hbelow e h1 he
        · rw [show e = d by omega]; exact hg)
      rw [show d + 1 + r = d + (r + 1) by omega] at h
      refine ⟨fun hall => Rch.tr st (h.1 fun e h1 h2 => hall e (by omega) h2),
        fun hn => Rch.tr st (h.2 fun hall => hn fun e h1 h2 => ?_)⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | he
      · exact hg
      · exact hall e (by omega) h2
    · -- d divides m or m + 2: the next candidate
      have := Rch.tr w (check_fail d (r + 1) _ hd hc (by omega) (hf.1 hg))
      exact ⟨fun hall => absurd (hall d (Nat.le_refl _) (by omega)) hg, fun _ => this⟩

theorem cand_twin (m : Nat) (hm : 3 ≤ m) (h : Tw m) : Rch (CS m) (BeepAt (m - 1) 1) := by
  have t := test (m - 2) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at t
  exact t.1 fun e h1 h2 => (twin_iff m hm).1 h e h1 h2

theorem cand_not (m : Nat) (hm : 3 ≤ m) (h : ¬ Tw m) : Rch (CS m) (CS (m + 1)) := by
  have t := test (m - 2) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at t
  exact t.2 fun hall => h ((twin_iff m hm).2 fun e h1 h2 => hall e h1 h2)

/-- the beep and the candidate after it, `m + 3` -/
theorem beep_next (n j : Nat) : Reach1 delta (BeepAt n j) (ZS 2 (n + j + 1)) :=
  Sys.Reach1.trans_reach (beep_step n j) (Reach.sub deltaNB_sub (after_beep n j))

/-! ## progress -/

theorem CS_ne (m : Nat) (hm : 3 ≤ m) : CS m ≠ CS (m + 1) := by
  intro h
  have := congrArg (fun c => c.R (m - 2)) h
  simp only [CS, ZS, show m + 1 - 2 = m - 2 + 1 by omega] at this
  rw [rp_get_self, rp_get_lt _ _ _ _ (by omega)] at this
  exact absurd this (by simp)

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {δ : St → Nat → Option (Nat × TM.Dir × St)} {a b : Cfg St}
    (h : Reach δ a b) (hne : a ≠ b) : Reach1 δ a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem step_not (m : Nat) (hm : 3 ≤ m) (h : ¬ Tw m) : Reach1 deltaNB (CS m) (CS (m + 1)) :=
  reach1_of_ne (cand_not m hm h) (CS_ne m hm)

theorem step_twin (m : Nat) (hm : 3 ≤ m) (h : Tw m) : Reach1 delta (CS m) (CS (m + 3)) := by
  have := Sys.Reach.trans_reach1 (Reach.sub deltaNB_sub (cand_twin m hm h)) (beep_next (m - 1) 1)
  rwa [show m - 1 + 1 + 1 = m + 3 - 2 by omega] at this

/-- every candidate leads to a later one -/
theorem cand_step (m : Nat) (hm : 3 ≤ m) :
    ∃ m', m < m' ∧ m' ≤ m + 3 ∧ Reach1 delta (CS m) (CS m') := by
  by_cases h : Tw m
  · exact ⟨m + 3, by omega, Nat.le_refl _, step_twin m hm h⟩
  · exact ⟨m + 1, by omega, by omega, Reach1.sub deltaNB_sub (step_not m hm h)⟩

theorem start_cs : Reach1 delta start (CS 3) :=
  Sys.Reach.trans_reach1 (Reach.sub deltaNB_sub start_beep) (beep_next 0 0)

/-- Every `m ≥ 3` is a candidate (reached at a step `t` with `m ≤ 3 t + 3`), or lies just
after a lesser twin prime candidate `q` (`q < m < q + 3`). -/
theorem reach_cand : ∀ m, 3 ≤ m → ∃ q t, 3 ≤ q ∧ q ≤ m ∧ q ≤ 3 * t + 3 ∧
    run delta t start = some (CS q) ∧ (q = m ∨ (Tw q ∧ m < q + 3)) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  clear hm
  induction k with
  | zero =>
    obtain ⟨t, ht⟩ := start_cs
    exact ⟨3, t + 1, Nat.le_refl _, Nat.le_refl _, by omega, ht, Or.inl rfl⟩
  | succ k ih =>
    obtain ⟨q, t, hq3, hqm, hqt, hr, hq⟩ := ih
    have next : ∀ q', q < q' → q' ≤ q + 3 → Reach1 delta (CS q) (CS q') →
        ∃ t', q' ≤ 3 * t' + 3 ∧ run delta t' start = some (CS q') := by
      intro q' h1 h2 ⟨n, hn⟩
      exact ⟨t + (n + 1), by omega, by
        show Sys.run (step delta) (t + (n + 1)) start = some (CS q')
        rw [Sys.run_add, show Sys.run (step delta) t start = some (CS q) from hr]; exact hn⟩
    rcases hq with hqe | ⟨htw, hlt⟩
    · by_cases htw : Tw q
      · exact ⟨q, t, hq3, by omega, hqt, hr, Or.inr ⟨htw, by omega⟩⟩
      · obtain ⟨t', h1, h2⟩ := next (q + 1) (by omega) (by omega)
          (Reach1.sub deltaNB_sub (step_not q hq3 htw))
        exact ⟨q + 1, t', by omega, by omega, h1, h2, Or.inl (by omega)⟩
    · by_cases he : k + 1 + 3 < q + 3
      · exact ⟨q, t, hq3, by omega, hqt, hr, Or.inr ⟨htw, he⟩⟩
      · obtain ⟨t', h1, h2⟩ := next (q + 3) (by omega) (Nat.le_refl _) (step_twin q hq3 htw)
        exact ⟨q + 3, t', by omega, by omega, h1, h2, Or.inl (by omega)⟩

/-- two lesser twin primes `q < p < q + 3` are 3 and 5 -/
theorem twin_gap (q p : Nat) (hq : Tw q) (hp : Tw p) (h1 : q < p) (h2 : p < q + 3) : p = 5 := by
  obtain ⟨⟨hq2, hq⟩, ⟨_, hq'⟩⟩ := hq
  obtain ⟨⟨hp2, hp⟩, ⟨_, hp'⟩⟩ := hp
  rcases Nat.lt_or_ge 2 q with h | h
  · -- q and p are odd, so p = q + 2; one of q, q + 2, q + 4 is divisible by 3
    have a2 := hq 2 h (Nat.le_refl _)
    have b2 := hp 2 (by omega) (Nat.le_refl _)
    obtain rfl : p = q + 2 := by omega
    have c1 := hq' 3 (by omega) (by omega)
    have c2 := hp' 3 (by omega) (by omega)
    rcases Nat.lt_or_ge 3 q with h3 | h3
    · have c0 := hq 3 h3 (by omega); omega
    · omega
  · -- q = 2: 2 + 2 = 4 is not prime
    exact absurd (hq' 2 (by omega) (Nat.le_refl _)) (by omega)

/-- every lesser twin prime other than 5 is a candidate, reached at a step `t` with
`p ≤ 3 t + 3` -/
theorem reach_twin (p : Nat) (hp : Tw p) (h5 : p ≠ 5) :
    ∃ t, p ≤ 3 * t + 3 ∧ run delta t start = some (CS p) := by
  have hp3 : 3 ≤ p := by
    obtain ⟨⟨h2, _⟩, ⟨_, h'⟩⟩ := hp
    rcases Nat.lt_or_ge p 3 with h | h
    · obtain rfl : p = 2 := by omega
      exact absurd (h' 2 (by omega) (Nat.le_refl _)) (by omega)
    · exact h
  obtain ⟨q, t, _, hqp, hqt, hr, hq⟩ := reach_cand p hp3
  rcases hq with rfl | ⟨htw, hlt⟩
  · exact ⟨t, hqt, hr⟩
  · rcases Nat.eq_or_lt_of_le hqp with rfl | hlt'
    · exact ⟨t, hqt, hr⟩
    · exact absurd (twin_gap q p htw hp hlt' hlt) h5

/-! ## the main theorem -/

/-- The machine never halts. -/
theorem never_halts : ¬ Halts delta start := by
  intro hh
  have prog : ∀ c, (∃ m, 3 ≤ m ∧ c = CS m) →
      ∃ c', (∃ m, 3 ≤ m ∧ c' = CS m) ∧ Reach1 delta c c' := by
    rintro c ⟨m, hm, rfl⟩
    obtain ⟨m', h1, _, h⟩ := cand_step m hm
    exact ⟨CS m', ⟨m', by omega, rfl⟩, h⟩
  exact Sys.not_halts_of_progress (f := step delta) _ prog _ ⟨3, Nat.le_refl _, rfl⟩
    (Sys.Halts.of_reach (Sys.Reach1.reach start_cs) hh)

/-- **Main theorem.** Started on a blank tape, the machine takes its beep transition (state
`beep` reading 0) only finitely often if and only if the twin prime conjecture is false. -/
theorem quasihalts_iff : QuasiHalts delta beep 0 start ↔ ¬ TwinPrimeConjecture := by
  constructor
  · rintro ⟨N, hN⟩ htpc
    obtain ⟨p, hp, hpp⟩ := htpc (3 * N + 7)
    obtain ⟨t, ht, hr⟩ := reach_twin p hpp (by omega)
    obtain ⟨s, hs⟩ := Reach.sub deltaNB_sub (cand_twin p (by omega) hpp)
    refine hN (t + s) (by omega) ⟨BeepAt (p - 1) 1, ?_, rfl, rfl, by simp [delta]⟩
    show Sys.run (step delta) (t + s) start = some _
    rw [Sys.run_add, show Sys.run (step delta) t start = some (CS p) from hr]; exact hs
  · intro hn
    have hN : ∃ N, ∀ p, N ≤ p → ¬ Tw p := by
      apply Classical.byContradiction; intro hno
      exact hn fun n => Classical.byContradiction fun hp => hno ⟨n, fun p h1 h2 => hp ⟨p, h1, h2⟩⟩
    obtain ⟨N, hN⟩ := hN
    obtain ⟨q, t, hq3, hqm, _, hr, hq⟩ := reach_cand (N + 5) (by omega)
    have hqN : N + 3 ≤ q := by rcases hq with h | ⟨_, h⟩ <;> omega
    refine quasihalts_of_sub deltaNB_sub deltaNB_beep ⟨t, hr⟩ ?_
    have prog : ∀ c, (∃ m, N + 3 ≤ m ∧ c = CS m) →
        ∃ c', (∃ m, N + 3 ≤ m ∧ c' = CS m) ∧ Reach1 deltaNB c c' := by
      rintro c ⟨m, hm, rfl⟩
      exact ⟨CS (m + 1), ⟨m + 1, by omega, rfl⟩, step_not m (by omega) (hN m (by omega))⟩
    exact Sys.not_halts_of_progress (f := step deltaNB) _ prog _ ⟨q, hqN, rfl⟩

/-- The beep transition: `beep` reading 0 writes 0, moves left and goes to `reb`. -/
theorem beep_transition : delta beep 0 = some (0, TM.Dir.L, reb) := rfl

/-- Equivalently: the machine beeps infinitely often iff the twin prime conjecture holds. -/
theorem beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta beep 0 start n) ↔ TwinPrimeConjecture := by
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    obtain ⟨N, hN⟩ := quasihalts_iff.2 hn
    obtain ⟨n, h1, h2⟩ := h N
    exact hN n h1 h2
  · intro h N; apply Classical.byContradiction; intro hno
    exact quasihalts_iff.1 ⟨N, fun n hn hb => hno ⟨n, hn, hb⟩⟩ h

end TMK.TwinPrimes4
