import TinyCryptids.SophieGermain.Round
import TinyCryptids.SophieGermain.Spec

/-!
# Main theorem: the design quasihalts iff there are finitely many Sophie Germain primes

The beep is the transition of state `G0` reading 0. Candidate `n` (odd, `n ≥ 5`) starts at
`CS n`. If `n` is a Sophie Germain prime, the run (without beeping) reaches
`BeepCfg (n - 1)`, takes the beep transition, and reaches `CS (n + 2)`; otherwise it reaches
`CS (n + 2)` without beeping (`deltaNB`, the design without its beep transition, runs from
`CS n` to `CS (n + 2)`). The start beeps for `n = 3` and reaches `CS 5`.
-/

namespace TM.SophieGermain

open TinyCryptids
open St

/-- for odd `d`, `d ∣ n` iff `d ∣ 2 n` -/
theorem mod_two_mul (d n : Nat) (hd : d % 2 = 1) : n % d = 0 ↔ (2 * n) % d = 0 := by
  constructor
  · intro h; rw [Nat.mul_mod, h]; simp
  · intro h
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
    have hk2 : k % 2 = 0 := by
      have : (d * k) % 2 = 0 := by rw [← hk]; omega
      rw [Nat.mul_mod, hd] at this; simpa using this
    obtain ⟨k', rfl⟩ : ∃ k', k = 2 * k' := ⟨k / 2, by omega⟩
    exact Nat.mod_eq_zero_of_dvd ⟨k', by
      rw [← Nat.mul_assoc, Nat.mul_comm d 2, Nat.mul_assoc] at hk; omega⟩

/-- `x` between 2 and `d + 2`: `d ∣ x` iff `x = d` -/
theorem mod_zero_iff (d x : Nat) (hd : 3 ≤ d) (h1 : 1 ≤ x) (h2 : x ≤ d + 2) :
    x % d = 0 ↔ x = d := by
  rcases Nat.lt_or_ge x d with hl | hl
  · rw [Nat.mod_eq_of_lt hl]; omega
  · rw [Nat.mod_eq_sub_mod hl, Nat.mod_eq_of_lt (by omega)]; omega

/-- after the walk for odd `d` (with `n = d + r + 1`) the D hole is on cell `2 r % d`; `d`
divides `n` or `2 n + 1` iff that is cell `d - 2` or `d - 3` -/
theorem fail_iff (d r : Nat) (hd : 3 ≤ d) (hdo : d % 2 = 1) :
    ¬ Good (d + r + 1) d ↔ ((2 * r) % d + 2 = d ∨ (2 * r) % d + 3 = d) := by
  have e := Nat.div_add_mod (2 * r) d
  have hc := Nat.mod_lt (2 * r) (show d > 0 by omega)
  generalize (2 * r) % d = c at e hc
  generalize (2 * r) / d = q at e
  have h1 : (2 * (d + r + 1)) % d = (c + 2) % d := by
    rw [show 2 * (d + r + 1) = d * (q + 2) + (c + 2) by rw [Nat.mul_add d q 2]; omega, Nat.mul_add_mod]
  have h2 : (2 * (d + r + 1) + 1) % d = (c + 3) % d := by
    rw [show 2 * (d + r + 1) + 1 = d * (q + 2) + (c + 3) by rw [Nat.mul_add d q 2]; omega,
      Nat.mul_add_mod]
  unfold Good
  simp only [ne_eq]
  rw [mod_two_mul d _ hdo, h1, h2, mod_zero_iff d _ hd (by omega) (by omega),
    mod_zero_iff d _ hd (by omega) (by omega)]
  omega

/-- the check after the walk, either way -/
theorem check (d j c : Nat) (hd : 3 ≤ d) (hc : c < d) :
    ((c + 2 = d ∧ 1 ≤ j) ∨ c + 3 = d → Rch (KC d c j) (CS (d + j + 1 + 3))) ∧
    (¬ (c + 2 = d ∨ c + 3 = d) → Rch (KC d c j) ⟨G0, ones (d + 1) blank, ones j blank⟩) := by
  refine ⟨check_fail d j c hd, fun h => ?_⟩
  rcases Nat.lt_or_ge (c + 3) d with hl | hl
  · exact check_ok d j c (by omega)
  · obtain rfl : c = d - 1 := by omega
    exact check_ok1 d j (by omega)

/-! ## trial division of one candidate -/

/-- the round for `d` (`r = 2 t + 1`, `n = d + r + 1`), every odd `e < d` already passed:
the run reaches the beep if every odd `e` with `d ≤ e < n` passes, and the next candidate
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
    have w := Rch.tr (walk_all d 1 hd) (walk_end d 0 ((2 * 1) % d))
    have hc : (2 * 1) % d = 2 := Nat.mod_eq_of_lt (by omega)
    have hf := fail_iff d 1 hd hdo
    rw [hc] at w hf
    have ck := check d 0 2 hd (by omega)
    by_cases hg : Good (d + 2 * 0 + 2) d
    · have := Rch.tr w (ck.2 fun h => hf.2 h hg)
      exact ⟨fun _ => this, fun hn => absurd (fun e h1 h2 h3 => by
        rw [show e = d by omega]; exact hg) hn⟩
    · have := Rch.tr w (ck.1 (by have := hf.1 hg; omega))
      exact ⟨fun hall => absurd (hall d (Nat.le_refl _) (by omega) hdo) hg,
        fun _ => by rw [show d + 0 + 1 + 3 = d + 2 * 0 + 4 by omega] at this; exact this⟩
  | succ t ih =>
    intro d hd hdo hbelow
    have hc := Nat.mod_lt (2 * (2 * (t + 1) + 1)) (show d > 0 by omega)
    have w := Rch.tr (walk_all d (2 * (t + 1) + 1) hd)
      (walk_end d (2 * (t + 1)) ((2 * (2 * (t + 1) + 1)) % d))
    have hf := fail_iff d (2 * (t + 1) + 1) hd hdo
    rw [show d + (2 * (t + 1) + 1) + 1 = d + 2 * (t + 1) + 2 by omega] at hf
    generalize (2 * (2 * (t + 1) + 1)) % d = c at w hf hc
    have ck := check d (2 * (t + 1)) c hd hc
    by_cases hg : Good (d + 2 * (t + 1) + 2) d
    · -- d passes: d := d + 2
      have st := Rch.tr w (ck.2 fun h => hf.2 h hg)
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
    · -- d divides n or 2 n + 1: fail
      have := Rch.tr w (ck.1 (by have := hf.1 hg; omega))
      rw [show d + 2 * (t + 1) + 1 + 3 = d + 2 * (t + 1) + 4 by omega] at this
      exact ⟨fun hall => absurd (hall d (Nat.le_refl _) (by omega) hdo) hg, fun _ => this⟩

theorem cand_sg (n : Nat) (hn : 5 ≤ n) (ho : n % 2 = 1) (h : SophieGermainPrime n) :
    Rch (CS n) (BeepCfg (n - 1)) := by
  have t := test ((n - 5) / 2) 3 (Nat.le_refl _) rfl (fun e h1 h2 _ => by omega)
  rw [show 3 + 2 * ((n - 5) / 2) + 2 = n by omega, show 2 * ((n - 5) / 2) + 1 = n - 4 by omega,
    show 3 + 2 * ((n - 5) / 2) + 1 = n - 1 by omega] at t
  exact t.1 fun e h1 h2 h3 => (sg_iff n hn ho).1 h e (by omega) (by omega) h3

theorem cand_not (n : Nat) (hn : 5 ≤ n) (ho : n % 2 = 1) (h : ¬ SophieGermainPrime n) :
    Rch (CS n) (CS (n + 2)) := by
  have t := test ((n - 5) / 2) 3 (Nat.le_refl _) rfl (fun e h1 h2 _ => by omega)
  rw [show 3 + 2 * ((n - 5) / 2) + 2 = n by omega, show 2 * ((n - 5) / 2) + 1 = n - 4 by omega,
    show 3 + 2 * ((n - 5) / 2) + 4 = n + 2 by omega] at t
  exact t.2 fun hall => h ((sg_iff n hn ho).2 fun e h1 h2 h3 => hall e h1 (by omega) h3)

/-- the beep and the rebuild: from `BeepCfg (n - 1)` to the next candidate -/
theorem after_beep (k : Nat) (hk : 2 ≤ k) : Reach delta (BeepCfg k) (CS (k + 3)) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  refine Reach.trans delta (beep_step k) (Reach.sub deltaNB_sub ?_)
  exact rebuild (k + 1) 0 (by omega)

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

theorem CS_ne (n : Nat) (hn : 5 ≤ n) : CS n ≠ CS (n + 2) := by
  intro h
  have := congrArg (fun c => c.R (n - 4)) h
  simp only [CS, WS, W, Nat.sub_zero, show n + 2 - 4 = n - 4 + 2 by omega] at this
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
theorem cand_step (n : Nat) (hn : 5 ≤ n) (ho : n % 2 = 1) :
    Reach1 delta (CS n) (CS (n + 2)) := by
  refine reach1_of_ne ?_ (CS_ne n hn)
  by_cases h : SophieGermainPrime n
  · have := after_beep (n - 1) (by omega)
    rw [show n - 1 + 3 = n + 2 by omega] at this
    exact Reach.trans delta (Reach.sub deltaNB_sub (cand_sg n hn ho h)) this
  · exact Reach.sub deltaNB_sub (cand_not n hn ho h)

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
  have prog : ∀ c, (∃ n, 5 ≤ n ∧ n % 2 = 1 ∧ c = CS n) →
      ∃ c', (∃ n, 5 ≤ n ∧ n % 2 = 1 ∧ c' = CS n) ∧ Reach1 delta c c' := by
    rintro c ⟨n, hn, ho, rfl⟩
    exact ⟨CS (n + 2), ⟨n + 2, by omega, by omega, rfl⟩, cand_step n hn ho⟩
  obtain ⟨t, _, hr⟩ := reach_cs 0
  exact not_halts_of_progress delta _ prog _ ⟨5, Nat.le_refl _, rfl, rfl⟩
    (Sys.Halts.of_reach ⟨t, hr⟩ hh)

theorem sg_odd {n : Nat} (h : SophieGermainPrime n) (h3 : 3 ≤ n) :
    n % 2 = 1 := by
  have := h.1.2 2 (by omega) (Nat.le_refl _)
  omega

/-- **Main theorem.** Started on a blank tape, the design takes its beep transition (state
`G0` reading 0) only finitely often if and only if there are only finitely many Sophie
Germain primes. -/
theorem quasihalts_iff : QuasiHalts delta G0 false start ↔ FinitelyManySophieGermainPrimes := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨2 * N + 5, fun n hsg => Classical.byContradiction fun hlt => ?_⟩
    have ho := sg_odd hsg (by omega)
    obtain ⟨t, ht, hr⟩ := reach_cs ((n - 5) / 2)
    rw [show 2 * ((n - 5) / 2) + 5 = n by omega] at hr
    obtain ⟨s, hs⟩ := Reach.sub deltaNB_sub (cand_sg n (by omega) ho hsg)
    exact hN (t + s) (by omega)
      ⟨BeepCfg (n - 1), by rw [run_add, hr]; exact hs, rfl, rfl, by simp [delta]⟩
  · rintro ⟨N, hN⟩
    obtain ⟨t, _, hr⟩ := reach_cs N
    refine quasihalts_of_sub deltaNB_sub rfl ⟨t, hr⟩ ?_
    have prog : ∀ c, (∃ n, 2 * N + 5 ≤ n ∧ n % 2 = 1 ∧ c = CS n) →
        ∃ c', (∃ n, 2 * N + 5 ≤ n ∧ n % 2 = 1 ∧ c' = CS n) ∧ Reach1 deltaNB c c' := by
      rintro c ⟨n, hn, ho, rfl⟩
      exact ⟨CS (n + 2), ⟨n + 2, by omega, by omega, rfl⟩,
        reach1_of_ne (cand_not n (by omega) ho fun h => absurd (hN n h) (by omega))
          (CS_ne n (by omega))⟩
    exact not_halts_of_progress deltaNB _ prog _ ⟨2 * N + 5, Nat.le_refl _, by omega, rfl⟩

/-- Equivalently: the design beeps infinitely often iff there are infinitely many Sophie
Germain primes. -/
theorem beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta G0 false start n) ↔
      ∀ N, ∃ p, N ≤ p ∧ SophieGermainPrime p := by
  constructor
  · intro h N; apply Classical.byContradiction; intro hno
    refine not_quasiHalts h (quasihalts_iff.2 ⟨N, fun p hp => ?_⟩)
    exact Classical.byContradiction fun hl => hno ⟨p, by omega, hp⟩
  · intro h N; apply Classical.byContradiction; intro hno
    obtain ⟨M, hM⟩ := quasihalts_iff.1 ⟨N, fun n hn hb => hno ⟨n, hn, hb⟩⟩
    obtain ⟨p, hp, hsg⟩ := h M
    exact absurd (hM p hsg) (by omega)

end TM.SophieGermain
