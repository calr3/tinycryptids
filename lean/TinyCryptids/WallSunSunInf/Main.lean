import TinyCryptids.WallSunSunInf.Round
import TinyCryptids.WallSunSun2.InfBridge

/-!
# Main theorem: the design quasihalts iff there are finitely many Wall–Sun–Sun primes

The beep is `q9` reading 0. Round `m` starts in `RS m`. For `m ≥ 2` the round (proved for
`deltaNB`, the design without its beep) runs the odometer, `N m = fib (idx m)` ticks, and the
check takes the beep iff `m² ∣ N m`; either way it reaches `RS (m + 1)` (`round`). The seed
(the merged machine's seed run, unrolled) reaches `RS 1`, and round 1 beeps once
(`round1`, a concrete run). So the design beeps once per `m ≥ 2` with `m² ∣ F (idx m)`, plus
once for `m = 1`, and `inf_bridge` (`../WallSunSun2/InfBridge.lean`) turns "infinitely many
such `m`" into "infinitely many Wall–Sun–Sun primes".
-/

namespace TM.WallSunSunInf
open St TinyCryptids TM.Zeckendorf

local notation "F" => false

/-- the Fibonacci number counted by the odometer in round `m` -/
def N (p : Nat) : Nat := if Hole p then fib (p - 1) else fib (p + 1)

theorem N_idx (p : Nat) : N p = fib (TM.WallSunSun2.idx p) := by
  unfold N TM.WallSunSun2.idx Hole; split <;> rfl

theorem N_pos (p : Nat) (hp : 2 ≤ p) : 1 ≤ N p := by
  unfold N; split <;> exact fib_pos _ (by omega)

/-- the ticks of the odometer: `val 0 (start0 p) + 1 + (N p - 1) = fib (p + 1)` -/
theorem ticks (p : Nat) (hp : 2 ≤ p) :
    (start0 p).length = p - 1 ∧ Valid (start0 p) ∧ val 0 (start0 p) + 1 + (N p - 1) = fib (p - 1 + 2) := by
  by_cases h : Hole p
  · have hN : N p = fib (p - 1) := by unfold N; rw [if_pos h]
    have h1 := fib_pos (p - 1) (by omega)
    simp only [start0, if_pos h, hN]
    refine ⟨by simp; omega, valid_msb _, ?_⟩
    rw [val_msb, show p - 2 + 0 + 2 = p by omega, TM.Zeckendorf.fib_add_two (p - 1), show p - 1 + 1 = p by omega]
    omega
  · have hN : N p = fib (p + 1) := by unfold N; rw [if_neg h]
    have h1 := fib_pos (p + 1) (by omega)
    simp only [start0, if_neg h, hN]
    refine ⟨by simp, valid_replicate _, ?_⟩
    rw [val_replicate, show p - 1 + 2 = p + 1 by omega]
    omega

/-- the base-`p` digits of `p - 1 + n` are `p - 1` and `0` iff `p² ∣ n` -/
theorem digits (p n : Nat) (hp : 2 ≤ p) :
    ((p - 1 + n) % p = p - 1 ∧ (p - 1 + n) / p % p = 0) ↔ p * p ∣ n := by
  have hp0 : 0 < p := by omega
  have hM : p ≤ p * p := Nat.le_mul_of_pos_left p hp0
  rw [Nat.dvd_iff_mod_eq_zero]
  have hx : (p - 1 + n) % (p * p) = (p - 1 + n % (p * p)) % (p * p) := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (show p - 1 < p * p by omega)]
  have hm := @Nat.mod_mul p p (p - 1 + n)
  have hlt := Nat.mod_lt (p - 1 + n) hp0
  have hy := Nat.mod_lt n (show 0 < p * p by omega)
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, h2, Nat.mul_zero, Nat.add_zero] at hm
    rw [hm] at hx
    generalize n % (p * p) = y at hx hy ⊢
    generalize p * p = M at hx hy hM ⊢
    rcases Nat.lt_or_ge (p - 1 + y) M with h | h
    · rw [Nat.mod_eq_of_lt h] at hx; omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at hx; omega
  · intro h0
    rw [h0, Nat.add_zero, Nat.mod_eq_of_lt (show p - 1 < p * p by omega)] at hx
    rw [hx] at hm
    generalize (p - 1 + n) / p % p = z at hm ⊢
    generalize (p - 1 + n) % p = w at hm hlt ⊢
    rcases Nat.eq_zero_or_pos z with hz | hz
    · subst hz; omega
    · have : p ≤ p * z := Nat.le_mul_of_pos_right p hz
      omega

/-! ## the rounds -/

/-- the beep configuration `c` is reached in `deltaNB`, and after the beep, the next round -/
def Beeps (a b : Cfg St) : Prop := ∃ c, Rch a c ∧ c.q = q9 ∧ c.R 0 = false ∧ Reach delta c b

theorem round (m : Nat) (hm : 2 ≤ m) :
    (¬ m * m ∣ N m → Rch (RS m) (RS (m + 1))) ∧ (m * m ∣ N m → Beeps (RS m) (RS (m + 1))) := by
  obtain ⟨hl, hv, ht⟩ := ticks m hm
  have r1 : Rch (RS m) (OV (m + 1) (F ::: F ::: EV m (m - 1 + N m))) := by
    have lp := loop m (m - 1) hm (N m - 1) (start0 m) m hl hv ht
    rw [show m - 1 + 2 = m + 1 by omega, show m + (N m - 1) = m - 1 + N m by
      have := N_pos m hm; omega] at lp
    exact Rch.tr (RS_PX m) (Rch.tr (init m hm) lp)
  have ch := check m (m - 1 + N m) hm
  have d := digits m (N m) hm
  refine ⟨fun hok => Rch.tr r1 (ch.2 fun h => hok (d.1 h)), fun h => ?_⟩
  obtain ⟨c, hc, h1, h2, h3⟩ := ch.1 (d.2 h)
  exact ⟨c, Rch.tr r1 hc, h1, h2, h3⟩

macro "gL0" : tactic => `(tactic| refine Rch.tr (stepL (δ := deltaNB) (by rfl)) ?_)
macro "step1" : tactic => `(tactic| first | gR | gL | gL0 | (refine blankR ?_; gR) | (refine blankR ?_; gL0) |
  (refine blankL ?_; gL))

/-- round 1 (B without inner cells) beeps once and reaches round 2 -/
theorem round1 : Beeps (RS 1) (RS 2) := by
  refine ⟨?c, ?r, ?hq, ?hb, ?rest⟩
  case r =>
    unfold RS XE
    iterate 65 step1
    fin
  case hq => rfl
  case hb => rfl
  case rest =>
    refine Reach.trans delta (stepL (δ := delta) (by rfl)) (Reach.sub deltaNB_sub ?_)
    iterate 34 step1
    unfold RS XE
    simp only [tl_blank, cons_blank]
    fin

theorem seed_reach : Rch start (RS 1) := by
  unfold start
  iterate 45 step1
  unfold RS XE
  simp only [tl_blank, cons_blank]
  fin

theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem ones_blank_get (a i : Nat) : ones a blank i = decide (i < a) := by
  induction a generalizing i with
  | zero => simp [blank]
  | succ a ih => cases i with
    | zero => show true = _; simp
    | succ i => show ones a blank i = _; rw [ih]; simp

theorem reach1_of_ne' {a b : Cfg St} (h : Reach delta a b) (hne : a ≠ b) : Reach1 delta a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem RS_ne (m : Nat) : RS m ≠ RS (m + 1) := by
  intro e
  have := congrArg (fun c : Cfg St => c.R (m + 2)) e
  have h1 : (RS m).R (m + 2) = ones m blank m := rfl
  have h2 : (RS (m + 1)).R (m + 2) = ones (m + 1) blank m := rfl
  simp only at this
  rw [h1, h2, ones_blank_get, ones_blank_get] at this
  simp at this

theorem Beeps.reach {a b : Cfg St} (h : Beeps a b) : Reach delta a b := by
  obtain ⟨_, h1, _, _, h3⟩ := h; exact Reach.trans delta (Reach.sub deltaNB_sub h1) h3

/-- every round leads to the next -/
theorem next (m : Nat) (hm : 1 ≤ m) : Reach1 delta (RS m) (RS (m + 1)) := by
  refine reach1_of_ne' ?_ (RS_ne m)
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    exact round1.reach
  · by_cases hd : m * m ∣ N m
    · exact ((round m h).2 hd).reach
    · exact Reach.sub deltaNB_sub ((round m h).1 hd)

/-- the start of round `k + 1` is reached after at least `k` steps -/
theorem reach_rs : ∀ k, ∃ t, k ≤ t ∧ run delta t start = some (RS (k + 1)) := by
  intro k
  induction k with
  | zero =>
    obtain ⟨t, ht⟩ := Reach.sub deltaNB_sub seed_reach
    exact ⟨t, Nat.zero_le _, ht⟩
  | succ k ih =>
    obtain ⟨t, ht, hr⟩ := ih
    obtain ⟨n, hn⟩ := next (k + 1) (by omega)
    exact ⟨t + (n + 1), by omega, by rw [run_add, hr]; exact hn⟩

/-- The design never halts. -/
theorem never_halts : ¬ Halts delta start := by
  intro hh
  obtain ⟨t, _, hr⟩ := reach_rs 0
  refine not_halts_of_progress delta (fun c => ∃ m, 1 ≤ m ∧ c = RS m) ?_ _ ⟨1, Nat.le_refl _, rfl⟩
    (Sys.Halts.of_reach ⟨t, hr⟩ hh)
  rintro c ⟨m, hm, rfl⟩
  exact ⟨RS (m + 1), ⟨m + 1, by omega, rfl⟩, next m hm⟩

theorem beep_none : deltaNB q9 false = none := rfl
theorem beep_some : delta q9 false = some (false, Dir.L, q10) := rfl

/-- **Main theorem.** Started on a blank tape, the design takes its beep transition (`q9`
reading 0) only finitely often if and only if there are only finitely many Wall–Sun–Sun
primes. -/
theorem quasihalts_iff : QuasiHalts delta q9 false start ↔ ¬ InfinitelyManyWallSunSunPrimes := by
  rw [← TM.WallSunSun2.inf_bridge]
  constructor
  · rintro ⟨T, hT⟩ hinf
    obtain ⟨m, hm, hm2, hd⟩ := hinf (T + 2)
    rw [← N_idx] at hd
    obtain ⟨t, ht, hr⟩ := reach_rs (m - 1)
    rw [show m - 1 + 1 = m by omega] at hr
    obtain ⟨c, ⟨s, hs⟩, hq, hb, _⟩ := (round m hm2).2 hd
    have hs' := run_sub deltaNB_sub s _ _ hs
    exact hT (t + s) (by omega) ⟨c, by rw [run_add, hr]; exact hs', hq, hb, by rw [beep_some]; exact Option.some_ne_none _⟩
  · intro hn
    have hN : ∃ K, ∀ m, K ≤ m → 2 ≤ m → ¬ m * m ∣ N m := by
      apply Classical.byContradiction; intro hno
      exact hn fun K => Classical.byContradiction fun hp =>
        hno ⟨K, fun m h1 h2 h3 => hp ⟨m, h1, h2, by rw [← N_idx]; exact h3⟩⟩
    obtain ⟨K, hK⟩ := hN
    obtain ⟨t, _, hr⟩ := reach_rs (K + 1)
    refine quasihalts_of_sub deltaNB_sub beep_none ⟨t, hr⟩ ?_
    refine not_halts_of_progress deltaNB (fun c => ∃ m, K + 2 ≤ m ∧ c = RS m) ?_ _ ⟨K + 2, Nat.le_refl _, rfl⟩
    rintro c ⟨m, hm, rfl⟩
    exact ⟨RS (m + 1), ⟨m + 1, by omega, rfl⟩,
      reach1_of_ne ((round m (by omega)).1 (hK m (by omega) (by omega))) (RS_ne m)⟩

/-- Equivalently: the design beeps infinitely often iff there are infinitely many
Wall–Sun–Sun primes. -/
theorem beeps_forever_iff :
    (∀ N, ∃ n, N ≤ n ∧ BeepsAt delta q9 false start n) ↔ InfinitelyManyWallSunSunPrimes := by
  constructor
  · intro h; apply Classical.byContradiction; intro hn
    exact not_quasiHalts h (quasihalts_iff.2 hn)
  · intro h N; apply Classical.byContradiction; intro hno
    exact quasihalts_iff.1 ⟨N, fun n hn hb => hno ⟨n, hn, hb⟩⟩ h

end TM.WallSunSunInf
