import TinyCryptids.Andrica.Round
import TinyCryptids.Andrica.Spec

/-!
# Main theorem: the design halts iff Andrica's conjecture fails

Round `m` starts at `RS m t x u`: H has `t + 1` cells (`IsT m t`) with its hole at `x`
(`Hinv m t x`), `|U| = u` and the countdown `|T| = t - u = tp + 1 - (m - p)` for the last prime
`p < m` and `IsT p tp` (`Inv`). A prime resets the countdown to `t`, a composite counts down,
and the machine stops at a composite `m` with `|T| = 1`, i.e. `m - p = tp`: exactly when
`Bad m`.
-/

namespace TM.Andrica

open TinyCryptids
open St

local notation "F" => false

attribute [local instance] Classical.propDecidable

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

/-- the invariant at the start of round `m` -/
def Inv (m t x u : Nat) : Prop :=
  Hinv m t x ∧ u + 1 ≤ t ∧ ∃ tp, IsT (lpb m) tp ∧ (t - u) + (m - lpb m) = tp + 1

/-- U after the phase step: U grows with H -/
def un (t x u : Nat) : Nat := if x + 3 ≤ t then u else u + 1

theorem un_eq (t x u : Nat) : un t x u + t = u + tn t x := by
  unfold un tn; split <;> omega

/-- the phase step and the way back -/
theorem after (t x u d r : Nat) (hx1 : 1 ≤ x) (hxt : x + 1 ≤ t) (hu : u + 1 ≤ t)
    (hd : 2 ≤ d) : Rch (HE t x u (F ::: Dst d r)) (RS (d + r + 1) (tn t x) (xn t x) (un t x u)) := by
  unfold RS tn xn un
  rw [show d + r + 1 - 2 = d + r - 1 by omega]
  by_cases hw : x + 3 ≤ t
  · simp only [if_pos hw]
    exact Rch.tr (hadv t x u _ hx1 hw) (ret t (x + 2) u d r hu hd)
  · simp only [if_neg hw]
    exact Rch.tr (hwrap t x u _ (by omega) (by omega) hx1) (ret (t + 1) 1 (u + 1) d r (by omega) hd)

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-- the stop condition is `Bad m` -/
theorem inv_bad {m t x u : Nat} (hm : 3 ≤ m) (hI : Inv m t x u) : Bad m ↔ ¬ Prime m ∧ u + 1 = t := by
  obtain ⟨_, hu, tp, htp, he⟩ := hI
  have hl := lpb_spec m hm
  unfold Bad
  rw [isT_le_iff htp]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- one round: halt when `m` is composite and T has one cell, else the next round -/
theorem round (m t x u : Nat) (hm : 3 ≤ m) (hI : Inv m t x u) :
    (¬ Prime m ∧ u + 1 = t → HaltAt (RS m t x u)) ∧
    (¬ (¬ Prime m ∧ u + 1 = t) → Inv (m + 1) (tn t x) (xn t x) (un t x (if Prime m then 0 else u + 1)) ∧
      Rch1 (RS m t x u) (RS (m + 1) (tn t x) (xn t x) (un t x (if Prime m then 0 else u + 1)))) := by
  obtain ⟨hH, hu, tp, htp, he⟩ := hI
  have hT := hinv_isT hH
  have hn := hinv_next hH
  obtain ⟨h2, hx, hxt, _⟩ := hH
  obtain ⟨hp, hlt, _⟩ := lpb_spec m hm
  have hun := un_eq t x
  have htn := tn_ge t x
  have tst := test (Lx t x u) blank (m - 2) 2 (Nat.le_refl 2) (fun e h1 h2 => by omega)
  rw [show 2 + (m - 2) = m by omega] at tst
  by_cases hpm : Prime m
  · refine ⟨fun hc => absurd hpm hc.1, fun _ => ?_⟩
    simp only [if_pos hpm]
    refine ⟨⟨hn, ?_, t, ?_, ?_⟩, ?_⟩
    · have := hun 0; omega
    · rw [lpb, if_pos hpm]; exact hT
    · rw [lpb, if_pos hpm]; have := hun 0; omega
    · have e2 := after t x 0 m 0 (by omega) hxt (by omega) (by omega)
      exact Reach1.trans_reach delta (reach1_of (tst.1 hpm) (by unfold RS SHT CP cfgL; simp))
        (Rch.tr (prime t x u m hu (by omega)) e2)
  · obtain ⟨d, r, hdr, hd, ek⟩ := tst.2 hpm
    refine ⟨fun hc => HaltAt.back ek (comp_halt t x u d r hc.2), fun hc => ?_⟩
    have hu2 : u + 2 ≤ t := by
      rcases Nat.lt_or_ge (u + 1) t with h' | h'
      · exact h'
      · exact absurd ⟨hpm, by omega⟩ hc
    simp only [if_neg hpm]
    refine ⟨⟨hn, ?_, tp, ?_, ?_⟩, ?_⟩
    · have := hun (u + 1); omega
    · rw [lpb, if_neg hpm]; exact htp
    · rw [lpb, if_neg hpm]; have := hun (u + 1); omega
    · have e2 := after t x (u + 1) d r (by omega) hxt (by omega) hd
      rw [hdr] at e2
      exact Reach1.trans_reach delta (reach1_of ek (by unfold RS SHT CK cfgL; simp))
        (Rch.tr (comp t x u d r hu2) e2)

/-- the seed writes the tape for `m = 2`; it is prime, and round 3 starts -/
theorem seed_reach : Rch start (RS 3 4 1 1) := by
  have e1 : Rch start (CP (Lx 3 1 0) blank 2) := by
    unfold start CP Lx Hr
    gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
    gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
    refine blankR ?_; gL
    fin
  exact Rch.tr e1 (Rch.tr (prime 3 1 0 2 (by omega) (by omega))
    (after 3 1 0 2 0 (by omega) (by omega) (by omega) (by omega)))

theorem inv_three : Inv 3 4 1 1 := by
  have hl : lpb 3 = 2 := lpb_eq prime_two (by omega) (fun r h1 h2 => by omega)
  refine ⟨⟨by omega, rfl, by omega, rfl⟩, by omega, 3, ?_, ?_⟩ <;> rw [hl]
  · exact ⟨by decide, by decide⟩

theorem halt_from (N : Nat) (hN : Bad N) :
    ∀ j m t x u, N - m = j → 3 ≤ m → m ≤ N → Inv m t x u → HaltAt (RS m t x u) := by
  intro j
  induction j with
  | zero =>
    intro m t x u hj h3 hm hI
    obtain rfl : m = N := by omega
    exact (round m t x u h3 hI).1 ((inv_bad h3 hI).1 hN)
  | succ j ih =>
    intro m t x u hj h3 hm hI
    by_cases hc : ¬ Prime m ∧ u + 1 = t
    · exact (round m t x u h3 hI).1 hc
    · obtain ⟨hI', e⟩ := (round m t x u h3 hI).2 hc
      exact HaltAt.back e.reach (ih (m + 1) _ _ _ (by omega) (by omega) (by omega) hI')

/-- If Andrica's conjecture fails, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧
    4 * p ≤ (q - p - 1) ^ 2) : HaltAt start := by
  obtain ⟨N, h3, hN⟩ := bad_iff.2 h
  exact HaltAt.back seed_reach (halt_from N hN _ 3 4 1 1 rfl (Nat.le_refl 3) h3 inv_three)

/-- **Main theorem.** Started on a blank tape, the design halts if and only if some consecutive
primes `p < q` have `4p ≤ (q - p - 1)²`, i.e. `√q - √p ≥ 1`. -/
theorem halts_iff : Halts delta start ↔
    ∃ p q, Prime p ∧ Prime q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ Prime r) ∧ 4 * p ≤ (q - p - 1) ^ 2 := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    let I : Cfg St → Prop := fun c => ∃ m t x u, 3 ≤ m ∧ Inv m t x u ∧ c = RS m t x u
    have prog : ∀ c, I c → ∃ c', I c' ∧ Rch1 c c' := by
      rintro c ⟨m, t, x, u, h3, hI, rfl⟩
      have hc : ¬ (¬ Prime m ∧ u + 1 = t) := fun hc => hno (bad_iff.1 ⟨m, h3, (inv_bad h3 hI).2 hc⟩)
      obtain ⟨hI', e⟩ := (round m t x u h3 hI).2 hc
      exact ⟨_, ⟨m + 1, _, _, _, by omega, hI', rfl⟩, e⟩
    exact not_halts_of_progress delta I prog _ ⟨3, 4, 1, 1, Nat.le_refl 3, inv_three, rfl⟩
      (Sys.Halts.of_reach seed_reach hH)
  · intro h; exact (haltAt_of h).halts

end TM.Andrica
