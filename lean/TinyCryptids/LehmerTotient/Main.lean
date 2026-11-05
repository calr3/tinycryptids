import TinyCryptids.LehmerTotient.Round
import TinyCryptids.LehmerTotient.Spec

/-!
# Main theorem: the design halts iff Lehmer's totient problem has a counterexample
-/

namespace TM.LehmerTotient

open TinyCryptids
open St
open TM.Carmichael (cp cp_succ cp_self gcd_sub)

local notation "F" => false

attribute [local instance] Classical.propDecidable

/-- round `n` starts: K/R `(2, n - 2)`, the pair `(1, n - 2)` -/
def Cn (n : Nat) : Cfg St := TK 0 1 0 (n - 3) (F ::: F ::: PR 1 (n - 2))

/-- the test of `(k, r)` and the count -/
theorem test_count (k r d p : Nat) (hk : 1 ≤ k) (hr : 1 ≤ r) (hd : 1 ≤ d) (hp : 1 ≤ p) :
    Rch (TK 0 (k - 1) 0 (r - 1) (F ::: F ::: PR d p))
      ⟨EC1, PostL (k - 1), ones (r - 1) (F ::: F ::: PR (d + if Nat.gcd k r = 1 then 1 else 0)
        (p - if Nat.gcd k r = 1 then 1 else 0))⟩ := by
  have ht := test k r hk hr (F ::: PR d p)
  unfold Res at ht
  by_cases h : Nat.gcd k r = 1
  · rw [if_pos h] at ht; rw [if_pos h]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    exact Rch.tr ht (coprime (k - 1) (r - 1) d q hd)
  · rw [if_neg h] at ht; rw [if_neg h]; exact ht

/-- the tests of `k, k + 1, …, n - 1` against `n - k`, …, `1` -/
theorem sweep (n : Nat) (hn : 3 ≤ n) : ∀ m k, k + m = n - 1 → 2 ≤ k →
    Rch (TK 0 (k - 1) 0 (n - k - 1) (F ::: F ::: PR (cp n k) (n - 1 - cp n k)))
      ⟨EC1, PostL (n - 2), F ::: F ::: PR (totient n) (n - 1 - totient n)⟩ := by
  intro m
  induction m with
  | zero =>
    intro k hk hk2
    have hlt := cp_lt (show 2 ≤ n by omega) k (by omega)
    have := test_count k (n - k) (cp n k) (n - 1 - cp n k) (by omega) (by omega)
      (cp_pos (show 2 ≤ n by omega) k hk2) (by omega)
    rw [gcd_sub (by omega), ← cp_succ, show k + 1 = n by omega, cp_self,
      show n - k - 1 = 0 by omega, show k - 1 = n - 2 by omega] at this
    rw [show n - k - 1 = 0 by omega, show k - 1 = n - 2 by omega]
    have e : n - 1 - cp n k - (if Nat.gcd k n = 1 then 1 else 0) = n - 1 - totient n := by
      have := cp_succ n k; rw [show k + 1 = n by omega, cp_self] at this; omega
    rw [e] at this; exact this
  | succ m ih =>
    intro k hk hk2
    have hlt := cp_lt (show 2 ≤ n by omega) k (by omega)
    have := test_count k (n - k) (cp n k) (n - 1 - cp n k) (by omega) (by omega)
      (cp_pos (show 2 ≤ n by omega) k hk2) (by omega)
    have e : n - 1 - cp n k - (if Nat.gcd k n = 1 then 1 else 0) = n - 1 - cp n (k + 1) := by
      have := cp_succ n k; omega
    rw [gcd_sub (by omega), ← cp_succ, e, show n - k - 1 = (n - (k + 1) - 1) + 1 by omega] at this
    rw [show n - k - 1 = (n - (k + 1) - 1) + 1 by omega]
    refine Rch.tr this (Rch.tr (shift _ _ _) ?_)
    have := ih (k + 1) (by omega) (by omega)
    rwa [show k + 1 - 1 = k - 1 + 1 by omega] at this

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-- after the test (not halting): D := 1, P gets a cell, K/R `(2, n - 1)` -/
theorem next_tail (n k a b : Nat) (hn : 3 ≤ n) (h : k + a + b = n + 2) :
    Rch (cfgL r1 (ones k (F ::: F ::: ones a (F ::: ones b (F ::: F ::: ones (n - 1) (PostL 0)))))
      (true ::: blank)) (Cn (n + 1)) := by
  refine Rch.tr (norm_ret k a b (n - 1) _ (by omega)) ?_
  rw [show n - 1 = (n - 2) + 1 by omega]
  refine Rch.tr (shift _ _ _) ?_
  unfold Cn PR
  rw [show k + a + b - 2 = n by omega, show n + 1 - 3 = n - 2 by omega, show n + 1 - 2 = n - 2 + 1 by omega,
    ← ones_succ', show n = n - 2 + 1 + 1 by omega]
  fin

/-- one round: halt at a counterexample, else the next round -/
theorem round (n : Nat) (hn : 3 ≤ n) :
    (Bad n → HaltAt (Cn n)) ∧ (¬ Bad n → Rch1 (Cn n) (Cn (n + 1))) := by
  have hs := sweep n hn (n - 3) 2 (by omega) (Nat.le_refl _)
  rw [cp_two (by omega), show n - 1 - 1 = n - 2 by omega, show n - 2 - 1 = n - 3 by omega] at hs
  have ht2 := totient_two hn
  have hle := totient_le (show 2 ≤ n by omega)
  have e1 := Rch.tr hs (to_test n (totient n) (n - 1 - totient n) (by omega) (by omega))
  have e1' : Rch1 (Cn n) _ := reach1_of e1 (by unfold Cn TK SHT; simp)
  generalize hp : n - 1 - totient n = p at e1 e1'
  rcases Nat.eq_zero_or_pos p with rfl | hp1
  · refine ⟨fun hb => by unfold Bad at hb; omega, fun _ => ?_⟩
    refine Reach1.trans_reach delta e1' (Rch.tr (prime_next _ _) ?_)
    exact next_tail n 2 (totient n) 1 hn (by omega)
  · have ot := one_test (F ::: ones (n - 1) (PostL 0)) blank (totient n) p ht2 hp1
    refine ⟨fun hb => ?_, fun hb => ?_⟩
    · unfold Bad at hb; rw [hp] at hb
      exact HaltAt.back e1'.reach (ot.1 hb.2)
    · have h0 : p % totient n ≠ 0 := fun h => hb ⟨by omega, by rw [hp]; exact h⟩
      have hc : (p - 1) % totient n + 1 < totient n := by
        have ms := mod_succ (p - 1) (totient n)
        rw [show p - 1 + 1 = p by omega] at ms
        have := Nat.mod_lt (p - 1) (show totient n > 0 by omega)
        rcases Nat.lt_or_ge ((p - 1) % totient n + 1) (totient n) with h | h
        · exact h
        · exact absurd (ms.2 (by omega)) h0
      refine Reach1.trans_reach delta e1' (Rch.tr (ot.2 h0) (Rch.tr (nodiv_next _ _ _ _ hc) ?_))
      exact next_tail n (p + 2) _ _ hn (by omega)

/-- the seed writes round 3 -/
theorem seed_reach : Rch start (Cn 3) := by
  unfold start Cn TK PR
  iterate 16 (refine Rch.tr (stepL (δ := delta) rfl) ?_)
  refine Rch.tr (stepR (δ := delta) rfl) ?_
  simp only [tl_blank]
  fin

theorem halt_from (N : Nat) (hN : Bad N) : ∀ j n, N - n = j → 3 ≤ n → n ≤ N → HaltAt (Cn n) := by
  intro j
  induction j with
  | zero => intro n hj h3 hn; rw [show n = N by omega]; exact (round N (by omega)).1 hN
  | succ j ih =>
    intro n hj h3 hn
    by_cases hb : Bad n
    · exact (round n h3).1 hb
    · exact HaltAt.back ((round n h3).2 hb).reach (ih (n + 1) (by omega) (by omega) (by omega))

/-- If Lehmer's totient problem has a counterexample, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ n, 2 ≤ n ∧ ¬ Prime n ∧ totient n ∣ n - 1) : HaltAt start := by
  obtain ⟨N, h2, hp, hd⟩ := h
  have hb := (bad_iff h2).1 ⟨hp, hd⟩
  have h3 : 3 ≤ N := by
    rcases Nat.lt_or_ge N 3 with h | h
    · obtain rfl : N = 2 := by omega
      unfold Bad at hb; have : totient 2 = 1 := rfl; omega
    · exact h
  exact HaltAt.back seed_reach (halt_from N hb _ 3 rfl (Nat.le_refl _) h3)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if some composite
`n` has `φ(n) ∣ n - 1`. -/
theorem halts_iff : Halts delta start ↔ ∃ n, 2 ≤ n ∧ ¬ Prime n ∧ totient n ∣ n - 1 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have good : ∀ n, 3 ≤ n → ¬ Bad n := fun n h3 hb =>
      hno ⟨n, by omega, (bad_iff (by omega)).2 hb⟩
    let I : Cfg St → Prop := fun c => ∃ n, 3 ≤ n ∧ c = Cn n
    have prog : ∀ c, I c → ∃ c', I c' ∧ Rch1 c c' := by
      rintro c ⟨n, h3, rfl⟩
      exact ⟨Cn (n + 1), ⟨n + 1, by omega, rfl⟩, (round n h3).2 (good n h3)⟩
    exact not_halts_of_progress delta I prog _ ⟨3, Nat.le_refl _, rfl⟩
      (Sys.Halts.of_reach seed_reach hH)
  · intro h; exact (haltAt_of h).halts

end TM.LehmerTotient
