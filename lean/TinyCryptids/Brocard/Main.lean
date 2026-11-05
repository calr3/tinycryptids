import TinyCryptids.Brocard.Round
import TinyCryptids.Brocard.Spec

/-!
# Main theorem: the design halts iff `n! + 1 = m²` for some `n ≥ 8`
-/

namespace TM.Brocard

open TinyCryptids
open St

local notation "F" => false

/-- the square test of `v + 1`, after `u = j² + c` units -/
theorem test_all (n v : Nat) : ∀ k u j c, v + 1 - u = k → u ≤ v + 1 → c < 2 * j + 1 → u = j * j + c →
    ((∃ m, v + 1 = m * m) → HaltAt (TP n v u (2 * j + 1) c)) ∧
    ((¬ ∃ m, v + 1 = m * m) → Rch (TP n v u (2 * j + 1) c) (G n 0 0 v 0)) := by
  intro k
  induction k with
  | zero =>
    intro u j c h hu hc hju
    obtain rfl : u = v + 1 := by omega
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · exact ⟨fun _ => test_halt n v _ (by omega), fun hn => absurd ⟨j, by omega⟩ hn⟩
    · refine ⟨fun ⟨m, hm⟩ => absurd ⟨m, by omega⟩ (not_square_between j c hc0 hc),
        fun _ => test_no n v _ c hc0 hc⟩
  | succ k ih =>
    intro u j c h hu hc hju
    by_cases hw : c + 1 < 2 * j + 1
    · have := ih (u + 1) j (c + 1) (by omega) (by omega) hw (by omega)
      have st := test_step n v u (2 * j + 1) c (by omega) hw
      exact ⟨fun hs => HaltAt.back st (this.1 hs), fun hs => Rch.tr st (this.2 hs)⟩
    · have := ih (u + 1) (j + 1) 0 (by omega) (by omega) (by omega) (by rw [sq_succ]; omega)
      have st := test_wrap n v u (2 * j + 1) (by omega) (by omega)
      rw [show 2 * j + 1 - 1 = c by omega, show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega] at st
      exact ⟨fun hs => HaltAt.back st (this.1 hs), fun hs => Rch.tr st (this.2 hs)⟩

/-- multiplication, merge, growth of N, with the gate -/
theorem mult_round (n w v : Nat) (hn : 1 ≤ n) (hv : 1 ≤ v) :
    Rch (G n w 0 v 0) (cfgL v3 (ones w blank)
      (F ::: ones (n + 3) (F ::: F ::: ones (v + n * v + 4) blank))) := by
  refine Rch.tr (multiply n w v hn hv) ?_
  have := Nat.mul_le_mul hn hv
  exact merge_pre n w v (n * v) (by omega)

/-- start of a test round for `n` -/
def RS (n : Nat) : Cfg St := TP n (fact n) 0 1 0

theorem ones_blank_get (a i : Nat) : ones a blank i = decide (i < a) := by
  induction a generalizing i with
  | zero => simp [blank]
  | succ a ih => cases i with
    | zero => show true = _; simp
    | succ i => show ones a blank i = _; rw [ih]; simp

theorem reach1_of_ne {a b : Cfg St} (h : Rch a b) (hne : a ≠ b) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; exact absurd hn hne
  | succ n => exact ⟨n, hn⟩

theorem RS_ne (n : Nat) : RS n ≠ RS (n + 1) := by
  intro h
  have := congrArg (fun c => c.L (n + 5)) h
  simp only [RS, TP] at this
  have e : ∀ m, (ones (0 + 1) (false ::: false ::: ones (m + 2) blank)) (n + 5) = ones (m + 2) blank (n + 2) := by
    intro m; rfl
  rw [e, e, ones_blank_get, ones_blank_get] at this
  simp at this

theorem round (n : Nat) (hn : 1 ≤ n) :
    ((∃ m, fact n + 1 = m * m) → HaltAt (RS n)) ∧
    ((¬ ∃ m, fact n + 1 = m * m) → Rch1 (RS n) (RS (n + 1))) := by
  have t := test_all n (fact n) (fact n + 1) 0 0 0 (by omega) (by omega) (by omega) rfl
  refine ⟨t.1, fun hs => reach1_of_ne ?_ (RS_ne n)⟩
  refine Rch.tr (t.2 hs) (Rch.tr (mult_round n 0 (fact n) hn (fact_pos n)) ?_)
  have := gate_test n 0 (fact n + n * fact n) (by omega)
  unfold RS; rw [fact_succ']; exact this

/-- warm-up rounds: no test, down to `RS 8` -/
theorem warm : ∀ w n, n + w = 8 → 1 ≤ w → 1 ≤ n → Rch (G n w 0 (fact n) 0) (RS 8) := by
  intro w
  induction w with
  | zero => intro n _ h; omega
  | succ w ih =>
    intro n h _ hn
    refine Rch.tr (mult_round n (w + 1) (fact n) hn (fact_pos n)) ?_
    rcases w with _ | w
    · have := gate_test n 1 (fact n + n * fact n) (by omega)
      obtain rfl : n = 7 := by omega
      unfold RS; rw [show fact 8 = fact 7 + 7 * fact 7 from fact_succ' 7]; exact this
    · have := gate_warm n w (fact n + n * fact n)
      refine Rch.tr this ?_
      rw [← fact_succ']
      exact ih (n + 1) (by omega) (by omega) (by omega)

theorem start_reach : Rch start (RS 8) := by
  refine Rch.tr seed_reach (Rch.tr (copies 1 7 1 (by omega) 0 0 0 0 rfl (by omega) (by omega)) ?_)
  refine Rch.tr (merge_pre 1 7 1 (0 + 0 + 1) (by omega)) ?_
  refine Rch.tr (gate_warm 1 5 (1 + (0 + 0 + 1))) ?_
  exact warm 6 2 (by omega) (by omega) (by omega)

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- If there is a solution with `n ≥ 8`, the machine reaches its explicit halting state. -/
theorem haltAt_of_sol (h : ∃ n m, 8 ≤ n ∧ fact n + 1 = m * m) : HaltAt start := by
  obtain ⟨N, M, hN, hM⟩ := h
  suffices H : ∀ k n, 8 ≤ n → n + k = N → HaltAt (RS n) from
    HaltAt.back start_reach (H (N - 8) 8 (by omega) (by omega))
  intro k
  induction k with
  | zero => intro n _ h; subst h; exact (round _ (by omega)).1 ⟨M, hM⟩
  | succ k ih =>
    intro n hn h
    by_cases hs : ∃ m, fact n + 1 = m * m
    · exact (round n (by omega)).1 hs
    · exact HaltAt.back ((round n (by omega)).2 hs).reach (ih (n + 1) (by omega) (by omega))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if
`n! + 1 = m²` has a solution with `n ≥ 8` (beyond Brocard's 4, 5, 7). -/
theorem halts_iff :
    Halts delta start ↔ ∃ n m, 8 ≤ n ∧ fact n + 1 = m * m := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ n, 8 ≤ n ∧ c = RS n) → ∃ c', (∃ n, 8 ≤ n ∧ c' = RS n) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      exact ⟨RS (n + 1), ⟨n + 1, by omega, rfl⟩,
        (round n (by omega)).2 (fun ⟨m, hm⟩ => hno ⟨n, m, hn, hm⟩)⟩
    exact not_halts_of_progress delta _ prog _ ⟨8, Nat.le_refl _, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of_sol h).halts

end TM.Brocard
