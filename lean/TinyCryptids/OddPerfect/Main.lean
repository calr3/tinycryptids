import TinyCryptids.OddPerfect.Round
import TinyCryptids.OddPerfect.Spec

/-!
# Main theorem: the design halts iff an odd perfect number exists
-/

namespace TM.OddPerfect

open TinyCryptids
open St

local notation "F" => false

/-! ## one round -/

/-- a run between two different configurations takes at least one step -/
theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem ones_get (a : Nat) (s : Strm) (i : Nat) (h : i < a) : ones a s i = true := by
  induction a generalizing i with
  | zero => omega
  | succ a ih => cases i with
    | zero => rfl
    | succ i => exact ih i (by omega)

theorem ones_get_end (a : Nat) (s : Strm) : ones a s a = s 0 := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih

theorem RE_ne (Y Y' : Strm) (n : Nat) : RE Y n ≠ RE Y' (n + 2) := by
  intro e
  have := congrFun (congrArg Cfg.L e) (n + 4)
  simp only [RE] at this
  change ones n (F ::: Y) n = ones (n + 2) (F ::: Y') n at this
  rw [ones_get_end, ones_get _ _ _ (by omega)] at this
  exact Bool.false_ne_true this

/-- the end of the round for `n`: T (`n + 3` cells) holds `min (properDivSum n) (n + 1)` -/
def RN (n : Nat) : Cfg St := RE (F ::: TX (n + 2) (min (properDivSum n) (n + 1))) n

/-- the candidates `d, …, n - 1` of the round for `n`, from the walk for `d` with T holding
the divisors below `d` -/
theorem dloop (n : Nat) (hn : 2 ≤ n) : ∀ k d, n - 1 - d = k → 1 ≤ d → d ≤ n - 1 →
    Rch (MW (F ::: TX (n + 2) (min (divSumBelow n (d - 1)) (n + 1))) d (n - 1 - d) d 0) (RN n) := by
  have upd : ∀ d, 1 ≤ d → d < n →
      (if (n - 1 - d + 1) % d = 0 then min (min (divSumBelow n (d - 1)) (n + 1) + d) (n + 2 - 1)
        else min (divSumBelow n (d - 1)) (n + 1)) = min (divSumBelow n d) (n + 1) := by
    intro d hd hdn
    rw [← divSumBelow_step n d hd hdn, show n - 1 - d + 1 = n - d by omega]
    by_cases h : (n - d) % d = 0
    · rw [if_pos h, if_pos h]; omega
    · rw [if_neg h, if_neg h]; omega
  intro k
  induction k with
  | zero =>
    intro d h hd hdn
    obtain rfl : d = n - 1 := by omega
    have := dstep (n + 2) (min (divSumBelow n (n - 1 - 1)) (n + 1)) (n - 1) (n - 1 - (n - 1))
      (by omega) (by omega) hd
    rw [upd (n - 1) hd (by omega), ← properDivSum_eq n (by omega), Nat.sub_self] at this
    rw [Nat.sub_self]
    refine Rch.tr this ?_
    have := shift_end (F ::: TX (n + 2) (min (properDivSum n) (n + 1))) (n - 1)
    rw [show n - 1 + 1 = n by omega] at this
    exact this
  | succ k ih =>
    intro d h hd hdn
    have := dstep (n + 2) (min (divSumBelow n (d - 1)) (n + 1)) d (n - 1 - d) (by omega) (by omega) hd
    rw [upd d hd (by omega)] at this
    refine Rch.tr this ?_
    rw [show n - 1 - d = (n - 1 - (d + 1)) + 1 by omega]
    refine Rch.tr (shift _ d _) ?_
    have := ih (d + 1) (by omega) (by omega) (by omega)
    rw [show d + 1 - 1 = d by omega] at this
    exact this

/-- after the round for `n`: halt if `n` is perfect, otherwise the end of the round for `n + 2` -/
theorem cycle (n : Nat) (hn : 1 ≤ n) :
    (properDivSum n = n → HaltAt (RN n)) ∧ (properDivSum n ≠ n → Rch1 (RN n) (RN (n + 2))) := by
  have re := round_end n (min (properDivSum n) (n + 1)) hn (by omega)
  refine ⟨fun h => re.1 (by omega), fun h => ?_⟩
  have st := re.2 (by omega)
  have lp := dloop (n + 2) (by omega) n 1 (by omega) (Nat.le_refl _) (by omega)
  rw [show min (divSumBelow (n + 2) (1 - 1)) (n + 2 + 1) = 0 by simp [divSumBelow],
    show n + 2 + 2 = n + 4 by omega, show n + 2 - 1 - 1 = n by omega] at lp
  exact reach1_of_ne (Rch.tr st lp) (RE_ne _ _ n)

/-! ## the main theorem -/

theorem start_reach : Rch start (RN 1) := by
  unfold RN
  rw [show min (properDivSum 1) (1 + 1) = 0 by decide]
  exact seed_reach

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- If an odd perfect number exists, the machine reaches its explicit halting state. -/
theorem haltAt_of_opn (h : ∃ n, n % 2 = 1 ∧ properDivSum n = n) : HaltAt start := by
  obtain ⟨n, hodd, hn⟩ := h
  obtain ⟨M, rfl⟩ : ∃ M, n = 2 * M + 1 := ⟨n / 2, by omega⟩
  suffices H : ∀ k m, m + k = M → HaltAt (RN (2 * m + 1)) from
    HaltAt.back start_reach (H M 0 (by omega))
  intro k
  induction k with
  | zero => intro m h; subst h; exact (cycle _ (by omega)).1 hn
  | succ k ih =>
    intro m h
    by_cases hp : properDivSum (2 * m + 1) = 2 * m + 1
    · exact (cycle _ (by omega)).1 hp
    · have := ih (m + 1) (by omega)
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega] at this
      exact HaltAt.back ((cycle _ (by omega)).2 hp).reach this

/-- **Main theorem.** Started on a blank tape, the design halts if and only if
an odd perfect number exists. -/
theorem halts_iff :
    Halts delta start ↔ ∃ n, n % 2 = 1 ∧ properDivSum n = n := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ m, c = RN (2 * m + 1)) → ∃ c', (∃ m, c' = RN (2 * m + 1)) ∧ Rch1 c c' := by
      rintro c ⟨m, rfl⟩
      refine ⟨RN (2 * (m + 1) + 1), ⟨m + 1, rfl⟩, ?_⟩
      have := (cycle (2 * m + 1) (by omega)).2 (fun h => hno ⟨2 * m + 1, by omega, h⟩)
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega]; exact this
    exact not_halts_of_progress delta _ prog _ ⟨0, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of_opn h).halts

end TM.OddPerfect
