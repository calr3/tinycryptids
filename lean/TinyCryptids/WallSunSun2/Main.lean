import TinyCryptids.WallSunSun2.Round
import TinyCryptids.WallSunSun2.Bridge

/-!
# Main theorem: the design halts iff a Wall–Sun–Sun prime exists

Round `m` starts in `RS m`, for every `m ≥ 2` (no primality test). It runs the odometer from
`start0 m` (`N m = fib (idx m)` ticks), so the counter ends at `V = m - 1 + N m`; the check
halts iff `V`'s base-`m` digits are `m - 1` and `0`, i.e. iff `m² ∣ N m`. So the machine halts
iff some `m ≥ 2` has `m² ∣ fib (idx m)`, which by `bridge` (`Bridge.lean`) holds iff a
Wall–Sun–Sun prime exists.
-/

namespace TM.WallSunSun2
open St TinyCryptids TM.Zeckendorf

local notation "F" => false

/-- the Fibonacci number counted by the odometer in round `m` -/
def N (p : Nat) : Nat := if Hole p then fib (p - 1) else fib (p + 1)

theorem N_idx (p : Nat) : N p = fib (idx p) := by
  unfold N idx Hole; split <;> rfl

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

/-! ## one round -/

theorem round (m : Nat) (hm : 2 ≤ m) :
    (¬ m * m ∣ N m → Rch (RS m) (RS (m + 1))) ∧ (m * m ∣ N m → HaltAt (RS m)) := by
  obtain ⟨hl, hv, ht⟩ := ticks m hm
  have r1 : Rch (RS m) (OV (m + 1) (F ::: F ::: EV m (m - 1 + N m))) := by
    have lp := loop m (m - 1) hm (N m - 1) (start0 m) m hl hv ht
    rw [show m - 1 + 2 = m + 1 by omega, show m + (N m - 1) = m - 1 + N m by
      have := N_pos m hm; omega] at lp
    exact Rch.tr (RS_PX m) (Rch.tr (init m hm) lp)
  have ch := check m (m - 1 + N m) hm
  have d := digits m (N m) hm
  exact ⟨fun hok => Rch.tr r1 (ch.2 fun h => hok (d.1 h)), fun h => HaltAt.back r1 (ch.1 (d.2 h))⟩

/-! ## the invariant and the main theorem -/

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

theorem RS_ne (m : Nat) : RS m ≠ RS (m + 1) := by
  intro e
  have := congrArg (fun c : Cfg St => c.R (m + 2)) e
  have h1 : (RS m).R (m + 2) = ones m blank m := rfl
  have h2 : (RS (m + 1)).R (m + 2) = ones (m + 1) blank m := rfl
  simp only at this
  rw [h1, h2, ones_blank_get, ones_blank_get] at this
  simp at this

macro "gL0" : tactic => `(tactic| refine Rch.tr (stepL (δ := delta) (by rfl)) ?_)

theorem seed_reach : Rch start (RS 2) := by
  unfold start
  iterate 21 (first | gR | gL | gL0 | (refine blankR ?_; gR) | (refine blankR ?_; gL0))
  unfold RS XE
  simp only [tl_blank, cons_blank]
  fin

/-- before round `2 + k`, if no earlier round halted -/
theorem reach_k : ∀ k, (∀ j, j < k → ¬ (2 + j) * (2 + j) ∣ N (2 + j)) → Rch start (RS (2 + k))
  | 0, _ => seed_reach
  | k + 1, h => Rch.tr (reach_k k (fun j hj => h j (by omega)))
      ((round (2 + k) (by omega)).1 (h k (by omega)))

theorem haltAt_of' (h : ∃ m, 2 ≤ m ∧ m * m ∣ fib (idx m)) : HaltAt start := by
  obtain ⟨m, hm2, hd⟩ := h
  rw [← N_idx] at hd
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 + k := ⟨m - 2, by omega⟩
  clear hm2
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hj : ∃ j, j < k ∧ (2 + j) * (2 + j) ∣ N (2 + j)
    · obtain ⟨j, hjk, hj⟩ := hj
      exact ih j hjk hj
    · have r := reach_k k (fun j hjk e => hj ⟨j, hjk, e⟩)
      exact HaltAt.back r ((round (2 + k) (by omega)).2 hd)

/-- a counterexample: the machine reaches its halting state -/
theorem haltAt_of (h : ∃ p, Prime p ∧ p * p ∣ fib (wssIndex p)) : HaltAt start :=
  haltAt_of' (bridge.2 h)

/-- The design halts iff some `m ≥ 2` has `m² ∣ F (m ∓ 1)`. -/
theorem halts_iff_idx : Halts delta start ↔ ∃ m, 2 ≤ m ∧ m * m ∣ fib (idx m) := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hn
    have hall : ∀ m, 2 ≤ m → ¬ m * m ∣ N m := fun m hm hd => hn ⟨m, hm, by rw [← N_idx]; exact hd⟩
    refine not_halts_of_progress delta (fun c => ∃ m, 2 ≤ m ∧ c = RS m) ?_ (RS 2) ⟨2, by omega, rfl⟩
      (Sys.Halts.of_reach seed_reach hH)
    rintro c ⟨m, hm, rfl⟩
    exact ⟨RS (m + 1), ⟨m + 1, by omega, rfl⟩,
      reach1_of_ne ((round m hm).1 (hall m hm)) (RS_ne m)⟩
  · intro h; exact (haltAt_of' h).halts

/-- **Main theorem.** Started on a blank tape, the design halts if and only if a
Wall–Sun–Sun prime exists. -/
theorem halts_iff : Halts delta start ↔ ∃ p, Prime p ∧ p * p ∣ fib (wssIndex p) :=
  halts_iff_idx.trans bridge

end TM.WallSunSun2
