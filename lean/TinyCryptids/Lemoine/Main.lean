import TinyCryptids.Lemoine.Round
import TinyCryptids.Lemoine.Spec

/-!
# Main theorem: the design halts iff Lemoine's conjecture fails
-/

namespace TM.Lemoine

open TinyCryptids
open St

local notation "F" => false

attribute [local instance] Classical.propDecidable

/-- the checkpoint of `(n, q)`: P holds `n - 2q + 2` (two cells still to go), Q holds `q` -/
def Chk (n q : Nat) (c : Cfg St) : Prop :=
  ∃ dp rp dq rq, 2 ≤ dq ∧ dp + rp = n - 2 * q + 2 ∧ dq + rq = q ∧ c = K q dp rp dq rq

/-- the seed writes the checkpoint of `(7, 2)` -/
theorem seed_reach : Rch start (K 2 2 3 2 0) := by
  unfold start K PL LS
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  refine blankR ?_; gL; gL; gL
  fin

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

/-- one checkpoint: halt (`p = 1`), the next `n` (both prime), or the next `q` -/
theorem round (n q : Nat) (c : Cfg St) (hc : Chk n q c) (hq : 2 ≤ q) (h2q : 2 * q < n) :
    (n - 2 * q = 1 → HaltAt c) ∧
    (3 ≤ n - 2 * q → Prime (n - 2 * q) → Prime q → ∃ c', Chk (n + 2) 2 c' ∧ Rch1 c c') ∧
    (3 ≤ n - 2 * q → ¬ (Prime (n - 2 * q) ∧ Prime q) → ∃ c', Chk n (q + 1) c' ∧ Rch1 c c') := by
  obtain ⟨dp, rp, dq, rq, hdq, hpp, hqq, rfl⟩ := hc
  have e1 := chk_norm q dp rp dq rq (by omega) (by omega)
  refine ⟨fun h1 => HaltAt.back e1 (norm_halt _ _ dp rp (by omega)), fun h3 hp hqp => ?_,
    fun h3 hno => ?_⟩
  all_goals
    have e2 := Rch.tr e1 (norm LS (RyP q dq rq) dp rp (by omega))
    have e2' : Rch1 (K q dp rp dq rq) (SHT LS (RyP q dq rq) 2 (dp + rp - 4)) := reach1_of e2 (by
      unfold K SHT cfgL; simp)
    have t := test LS (RyP q dq rq) (dp + rp - 4) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
    rw [show 2 + (dp + rp - 4) = n - 2 * q by omega] at t
  · -- p prime, q prime
    have e3 := Rch.tr (t.1 hp) (p_prime q (n - 2 * q) dq rq (by omega) hdq)
    have e4 := Rch.tr e3 (norm (LxQ q (n - 2 * q) 0) LS dq (rq + 2) (by omega))
    have tq := test (LxQ q (n - 2 * q) 0) LS (dq + (rq + 2) - 4) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
    rw [show 2 + (dq + (rq + 2) - 4) = q by omega] at tq
    refine ⟨_, ⟨n - 2 * q, 2 * q, 2, 0, Nat.le_refl _, by omega, rfl, rfl⟩,
      Reach1.trans_reach delta e2' (Rch.tr e4 (Rch.tr (tq.1 hqp) (q_prime q (n - 2 * q) (by omega))))⟩
  · by_cases hp : Prime (n - 2 * q)
    · -- p prime, q composite
      have hqc : ¬ Prime q := fun h => hno ⟨hp, h⟩
      have e3 := Rch.tr (t.1 hp) (p_prime q (n - 2 * q) dq rq (by omega) hdq)
      have e4 := Rch.tr e3 (norm (LxQ q (n - 2 * q) 0) LS dq (rq + 2) (by omega))
      have tq := test (LxQ q (n - 2 * q) 0) LS (dq + (rq + 2) - 4) 2 (Nat.le_refl _) (fun e h1 h2 => by omega)
      rw [show 2 + (dq + (rq + 2) - 4) = q by omega] at tq
      obtain ⟨d', r', h1, h2, h3⟩ := tq.2 hqc
      refine ⟨_, ⟨n - 2 * q, 0, d', r' + 1, h2, by omega, by omega, rfl⟩,
        Reach1.trans_reach delta e2' (Rch.tr e4 (Rch.tr h3 (q_comp q (n - 2 * q) d' r' (by omega) h2)))⟩
    · -- p composite
      obtain ⟨d', r', h1, h2, h3⟩ := t.2 hp
      refine ⟨_, ⟨d', r', dq, rq + 1, hdq, by omega, by omega, rfl⟩,
        Reach1.trans_reach delta e2' (Rch.tr h3 (p_comp q d' r' dq rq (by omega) hdq))⟩

theorem seed_chk : Chk 7 2 (K 2 2 3 2 0) := ⟨2, 3, 2, 0, Nat.le_refl _, rfl, rfl, rfl⟩

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- some odd `n ≥ 7` up to `N`, from `q`, is not searched past: the machine halts -/
theorem halt_from (N : Nat) (hN : ¬ Rep N) (hNo : N % 2 = 1) :
    ∀ M n q c, (N + 2 - n) * (N + 2) + (n - 2 * q) = M → Chk n q c → n % 2 = 1 → n ≤ N →
      2 ≤ q → 2 * q < n → HaltAt c := by
  intro M
  induction M using Nat.strongRecOn with
  | _ M ih =>
    intro n q c hM hc hn hnN hq h2q
    have r := round n q c hc hq h2q
    by_cases h1 : n - 2 * q = 1
    · exact r.1 h1
    have h3 : 3 ≤ n - 2 * q := by omega
    by_cases hb : Prime (n - 2 * q) ∧ Prime q
    · obtain ⟨c', hc', hr⟩ := r.2.1 h3 hb.1 hb.2
      have hnN' : n + 2 ≤ N := by
        have : n ≠ N := fun e => hN ⟨q, hq, e ▸ h2q, e ▸ hb.1, hb.2⟩
        omega
      refine HaltAt.back hr.reach (ih _ ?_ (n + 2) 2 c' rfl hc' (by omega) hnN' (Nat.le_refl _) (by omega))
      rw [← hM]
      have : (N + 2 - (n + 2)) * (N + 2) + (N + 2) ≤ (N + 2 - n) * (N + 2) := by
        rw [show N + 2 - n = N + 2 - (n + 2) + 2 by omega, Nat.add_mul]; omega
      omega
    · obtain ⟨c', hc', hr⟩ := r.2.2 h3 hb
      exact HaltAt.back hr.reach (ih _ (by omega) n (q + 1) c' rfl hc' hn hnN (by omega) (by omega))

/-- If Lemoine's conjecture fails, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ n, 7 ≤ n ∧ n % 2 = 1 ∧ ∀ p q, Prime p → Prime q → p + 2 * q ≠ n) :
    HaltAt start := by
  obtain ⟨N, h7, ho, hN⟩ := h
  exact HaltAt.back seed_reach
    (halt_from N ((fails_iff N).1 hN) ho _ 7 2 _ rfl seed_chk rfl h7 (Nat.le_refl _) (by omega))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if Lemoine's
conjecture is false. -/
theorem halts_iff : Halts delta start ↔
    ∃ n, 7 ≤ n ∧ n % 2 = 1 ∧ ∀ p q, Prime p → Prime q → p + 2 * q ≠ n := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have rep : ∀ n, 7 ≤ n → n % 2 = 1 → Rep n := fun n h7 ho =>
      Classical.byContradiction fun hr => hno ⟨n, h7, ho, (fails_iff n).2 hr⟩
    let I : Cfg St → Prop := fun c => ∃ n q, Chk n q c ∧ 7 ≤ n ∧ n % 2 = 1 ∧ 2 ≤ q ∧ 2 * q < n ∧
      ∀ q', 2 ≤ q' → q' < q → ¬ (Prime (n - 2 * q') ∧ Prime q')
    have prog : ∀ c, I c → ∃ c', I c' ∧ Rch1 c c' := by
      rintro c ⟨n, q, hc, h7, ho, hq, h2q, hbelow⟩
      have r := round n q c hc hq h2q
      obtain ⟨q', hq', h2q', hp', hqp'⟩ := rep n h7 ho
      have hge : q ≤ q' := Nat.le_of_not_lt fun h => hbelow q' hq' h ⟨hp', hqp'⟩
      have h3 : 3 ≤ n - 2 * q := by
        rcases Nat.lt_or_ge (n - 2 * q) 3 with h | h
        · exfalso
          have : n - 2 * q = 1 := by omega
          have : q' = q := by omega
          subst this
          have := hp'.two_le; omega
        · exact h
      by_cases hb : Prime (n - 2 * q) ∧ Prime q
      · obtain ⟨c', hc', hr⟩ := r.2.1 h3 hb.1 hb.2
        exact ⟨c', ⟨n + 2, 2, hc', by omega, by omega, Nat.le_refl _, by omega,
          fun q'' h1 h2 => absurd h2 (by omega)⟩, hr⟩
      · obtain ⟨c', hc', hr⟩ := r.2.2 h3 hb
        refine ⟨c', ⟨n, q + 1, hc', h7, ho, by omega, by omega, fun q'' h1 h2 => ?_⟩, hr⟩
        rcases Nat.lt_or_ge q'' q with h | h
        · exact hbelow q'' h1 h
        · rw [show q'' = q by omega]; exact hb
    have hI : I (K 2 2 3 2 0) := ⟨7, 2, seed_chk, Nat.le_refl _, rfl, Nat.le_refl _, by omega,
      fun q'' h1 h2 => absurd h2 (by omega)⟩
    exact not_halts_of_progress delta I prog _ hI (halts_det hH seed_reach)
  · intro h; exact (haltAt_of h).halts

end TM.Lemoine
