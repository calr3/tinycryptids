import TinyCryptids.AgohGiuga.Round

/-!
# Main theorem: the design halts iff the Agoh–Giuga conjecture fails

`It n m`: round `n`, `m` bases done (the next base is `i = n - 1 - m`): S's hole at
`gsum n m % n + 1`, the flag `fl n m` (`J` one cell longer, `K` one cell shorter).  A base
leads to `It n (m + 1)` (`base`); the last base (`i = 2`, `m = n - 3`) ends the round: HALT iff
`Bad n`, otherwise `It (n + 1) 0` (`last`).
-/

namespace TM.AgohGiuga

open TinyCryptids
open St

local notation "F" => false
local notation "T" => true

attribute [local instance] Classical.propDecidable

/-- `1` once the flag is set -/
def fb (b : Bool) : Nat := if b then 1 else 0

def It (n m : Nat) : Cfg St :=
  IC n (n - 1 - m) (m + 1 + fb (fl n m)) (2 - fb (fl n m)) (gsum n m % n + 1)

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-- the counter after a base -/
theorem hole_next (n m : Nat) (hn : 2 ≤ n) (hm : m + 3 ≤ n) :
    nxs n (gsum n m % n + 1) ((n - 1 - m) ^ (n - 1) - 1) = gsum n (m + 1) % n + 1 := by
  rw [show gsum n m % n + 1 = (gsum n m % n) % n + 1 by rw [Nat.mod_mod], nxs_mod n (by omega)]
  show _ = (gsum n m + ((n - (m + 1)) ^ (n - 1) - 1)) % n + 1
  rw [show n - 1 - m = n - (m + 1) by omega, Nat.add_mod (gsum n m), Nat.add_mod (gsum n m % n),
    Nat.mod_mod]

/-- a base: the Horner run, `B += R - 1`, the check, and (for `i ≥ 3`) the shift; or (for `i = 2`)
the tape at the end of the round -/
theorem base_run (n m : Nat) (hn : 4 ≤ n) (hm : m + 3 ≤ n) :
    Rch1 (It n m) (tc n (n - 1 - m) (m + 1 + fb (fl n (m + 1))) (2 - fb (fl n (m + 1)))
      (gsum n (m + 1) % n + 1)) := by
  have hB := Nat.mod_lt (gsum n m) (show 0 < n by omega)
  have hB' := Nat.mod_lt (gsum n (m + 1)) (show 0 < n by omega)
  have hf : fb (fl n m) ≤ 1 := by unfold fb; split <;> omega
  have e1 := run_cons n (n - 1 - m) (m + 1 + fb (fl n m)) (2 - fb (fl n m)) (gsum n m % n + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hole_next n m (by omega) hm] at e1
  refine Reach1.trans_reach delta (reach1_of e1 (by unfold It IC eAtC CL; simp)) ?_
  refine Rch.tr (cons_done _ _ _ (by omega) (by omega)) ?_
  have hfl : fl n (m + 1) = (fl n m || gsum n (m + 1) % n != 0) := rfl
  by_cases hz : gsum n (m + 1) % n = 0
  · rw [hz]
    have : fl n (m + 1) = fl n m := by rw [hfl, hz]; simp
    rw [this]
    exact check_zero n _ _ _ (by omega) (by omega)
  · have hfl1 : fl n (m + 1) = true := by rw [hfl]; simp [hz]
    rw [hfl1]
    have hc := check_flag n (n - 1 - m) (m + 1 + fb (fl n m)) (2 - fb (fl n m)) (gsum n (m + 1) % n + 1)
      (by omega) (by omega) (by cases h : fl n m <;> simp [fb, h])
    rw [show gsum n (m + 1) % n + 1 - 1 = gsum n (m + 1) % n by omega] at hc
    rw [show m + 1 + fb (fl n m) + (2 - fb (fl n m)) - 1 = m + 1 + fb true by
      cases h : fl n m <;> simp [fb]] at hc
    exact hc

/-- a base with `i ≥ 3`: the next base -/
theorem base (n m : Nat) (hn : 4 ≤ n) (hm : m + 4 ≤ n) : Rch1 (It n m) (It n (m + 1)) := by
  refine Reach1.trans_reach delta (base_run n m hn (by omega)) ?_
  have := shift n (n - 1 - m) (m + 1 + fb (fl n (m + 1))) (2 - fb (fl n (m + 1))) (gsum n (m + 1) % n + 1)
    (by omega) (by omega)
  unfold It
  rw [show n - 1 - (m + 1) = n - 1 - m - 1 by omega, show m + 1 + 1 + fb (fl n (m + 1)) =
    m + 1 + fb (fl n (m + 1)) + 1 by omega]
  exact this

/-- the last base (`i = 2`): HALT iff `Bad n`, otherwise round `n + 1` -/
theorem last (n m : Nat) (hn : 4 ≤ n) (hm : m + 3 = n) :
    (Bad n → HaltAt (It n m)) ∧ (¬ Bad n → Rch1 (It n m) (It (n + 1) 0)) := by
  have e0 := base_run n m hn (by omega)
  rw [show n - 1 - m = 2 by omega, show m + 1 = n - 2 by omega] at e0
  have hB := Nat.mod_lt (gsum n (n - 2)) (show 0 < n by omega)
  have hf : fb (fl n (n - 2)) ≤ 1 := by unfold fb; split <;> omega
  have e1 := round_pz n (n - 2 + fb (fl n (n - 2))) (2 - fb (fl n (n - 2))) (gsum n (n - 2) % n + 1)
    (by omega) (by omega) (by omega)
  have hres : ∀ b, Rch ⟨h1, T ::: F ::: F ::: Lw2 n (n - 2 + fb (fl n (n - 2))) (2 - fb (fl n (n - 2))),
      b ::: ones n Rr⟩ (It (n + 1) 0) := fun b => by
    have := round_reset n (n - 2 + fb (fl n (n - 2))) (2 - fb (fl n (n - 2))) b (by omega)
      (by cases h : fl n (n - 2) <;> simp [fb] <;> omega)
    unfold It
    simpa [gsum, fl, fb] using this
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨hf1, hg⟩ := hb
    rw [hf1, hg] at e1
    rw [hf1, hg] at e0
    simp only [fb, if_true, Nat.zero_add, show n + 1 - 1 = n by omega, show 2 - 1 = 1 from rfl,
      show n - 2 + 1 = n - 1 by omega] at e0 e1
    exact HaltAt.back (Rch.tr (Reach1.reach delta e0) e1) (round_halt n (n - 1))
  · refine Reach1.trans_reach delta e0 ?_
    refine Rch.tr e1 ?_
    by_cases hz : gsum n (n - 2) % n = 0
    · have hfl : fl n (n - 2) = false := by
        cases h : fl n (n - 2)
        · rfl
        · exact absurd ⟨h, hz⟩ hb
      rw [hfl] at hres ⊢
      simp only [fb, Bool.false_eq_true, if_false, Nat.zero_add, Nat.add_zero, Nat.sub_zero,
        show n + 1 - 1 = n by omega] at hres ⊢
      simp only [hz, Nat.zero_add, show n + 1 - 1 = n by omega]
      exact Rch.tr (round_a n (n - 2)) (hres F)
    · exact Rch.tr (round_b n _ _ _ (by omega) (by omega)) (hres T)

theorem seed_reach : Rch start (It 4 0) := by
  have h := round_reset 3 1 2 T (by omega) (Or.inr ⟨rfl, rfl⟩)
  have e : It 4 0 = IC 4 3 1 2 1 := by simp [It, gsum, fl, fb]
  rw [e]
  refine Rch.tr ?_ h
  unfold start Lw2 Rr
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  refine blankR ?_
  gL; gL; gL; gL; gL
  sLn 5
  gR; gR
  simp only [cons_blank]
  fin

/-- the bases of a round up to the last one -/
theorem to_last (n : Nat) (hn : 4 ≤ n) : ∀ k m, n - 3 - m = k → m + 3 ≤ n → Rch (It n m) (It n (n - 3)) := by
  intro k
  induction k with
  | zero => intro m hk hm; rw [show n - 3 = m by omega]; fin
  | succ k ih =>
    intro m hk hm
    exact Rch.tr (base n m hn (by omega)).reach (ih (m + 1) (by omega) (by omega))

theorem halt_from (N : Nat) (hN : Bad N) :
    ∀ j n, N - n = j → 4 ≤ n → n ≤ N → HaltAt (It n 0) := by
  intro j
  induction j with
  | zero =>
    intro n hj h4 hn
    obtain rfl : n = N := by omega
    exact HaltAt.back (to_last n h4 _ 0 rfl (by omega)) ((last n (n - 3) h4 (by omega)).1 hN)
  | succ j ih =>
    intro n hj h4 hn
    refine HaltAt.back (to_last n h4 _ 0 rfl (by omega)) ?_
    by_cases hb : Bad n
    · exact (last n (n - 3) h4 (by omega)).1 hb
    · exact HaltAt.back ((last n (n - 3) h4 (by omega)).2 hb).reach (ih (n + 1) (by omega) (by omega) (by omega))

/-- If the Agoh–Giuga conjecture fails, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ n, 2 ≤ n ∧ ¬ Prime n ∧ n ∣ powSum n (n - 1) + 1) : HaltAt start := by
  obtain ⟨N, h4, hN⟩ := bad_iff.2 h
  exact HaltAt.back seed_reach (halt_from N hN _ 4 rfl (Nat.le_refl 4) h4)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if some composite
`n ≥ 2` divides `1^(n-1) + 2^(n-1) + … + (n-1)^(n-1) + 1`. -/
theorem halts_iff : Halts delta start ↔ ∃ n, 2 ≤ n ∧ ¬ Prime n ∧ n ∣ powSum n (n - 1) + 1 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    let I : Cfg St → Prop := fun c => ∃ n m, 4 ≤ n ∧ m + 3 ≤ n ∧ c = It n m
    have prog : ∀ c, I c → ∃ c', I c' ∧ Rch1 c c' := by
      rintro c ⟨n, m, h4, hm, rfl⟩
      by_cases hl : m + 3 = n
      · have hb : ¬ Bad n := fun hb => hno (bad_iff.1 ⟨n, h4, hb⟩)
        exact ⟨_, ⟨n + 1, 0, by omega, by omega, rfl⟩, (last n m h4 hl).2 hb⟩
      · exact ⟨_, ⟨n, m + 1, h4, by omega, rfl⟩, base n m h4 (by omega)⟩
    exact not_halts_of_progress delta I prog _ ⟨4, 0, Nat.le_refl 4, by omega, rfl⟩
      (Sys.Halts.of_reach seed_reach hH)
  · intro h; exact (haltAt_of h).halts

end TM.AgohGiuga
