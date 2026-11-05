import TinyCryptids.BrocardPrimes.Cycle
namespace TM.BrocardPrimes
open St

/-! # Main theorem -/

/-- the machine halts at checkpoint `m` -/
def Stop (m n c : Nat) : Prop := m + 1 = (n+1)*(n+1) ∧ PrimeDvd (n+1) ∧ 2 ≤ n ∧ c < 4

/-- One increment, all cases: halt exactly under `HC`, otherwise strictly progress. -/
theorem cycle (m n c : Nat) (hI : Inv m n c) :
    (Stop m n c → HaltAt (chk m n c)) ∧
    (¬ Stop m n c → ∃ n' c', Inv (m+1) n' c' ∧ Rch1 (chk m n c) (chk (m+1) n' c')) := by
  by_cases hp : PrimeDvd (m+1)
  · have hns : m + 1 ≠ (n+1)*(n+1) := fun e => sq_not_prime n hI.2.1 (e ▸ hp)
    refine ⟨fun h => absurd h.1 hns, fun _ => ?_⟩
    obtain ⟨h1, h2⟩ := cyc_prime m n c hI hp
    exact ⟨n, c+1, h2, h1⟩
  · by_cases hs : m + 1 = (n+1)*(n+1)
    · by_cases hb : PrimeDvd (n+1) ∧ 2 ≤ n
      · by_cases hc : c < 4
        · exact ⟨fun _ => cyc_halt m n c hI hs hb.1 hb.2 hc, fun h => absurd ⟨hs, hb.1, hb.2, hc⟩ h⟩
        · refine ⟨fun h => absurd h.2.2.2 hc, fun _ => ?_⟩
          obtain ⟨h1, h2⟩ := cyc_bd m n c hI hs hb.1 hb.2 (by omega)
          exact ⟨n+1, 0, h2, h1⟩
      · refine ⟨fun h => absurd ⟨h.2.1, h.2.2.1⟩ hb, fun _ => ?_⟩
        obtain ⟨h1, h2⟩ := cyc_sq m n c hI hs hb
        exact ⟨n+1, c, h2, h1⟩
    · refine ⟨fun h => absurd h.1 hs, fun _ => ?_⟩
      obtain ⟨h1, h2⟩ := cyc_comp m n c hI hp hs
      exact ⟨n, c, h2, h1⟩

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

theorem prime_two : PrimeDvd 2 := (primeDvd_iff 2).2 (by decide)
theorem not_prime_one : ¬ PrimeDvd 1 := fun h => by have := h.1; omega

theorem primesDesc_two : primesDesc 2 = [2] := by
  rw [primesDesc_prime 1 prime_two, show 1 = 0 + 1 from rfl, primesDesc_comp 0 not_prime_one]; rfl

theorem pc_val (x : Nat) : pc x = TinyCryptids.primeCount x := pc_eq_primeCount x

/-- From a blank tape, the 24-cell seed is written and the checkpoint m = 2 reached. -/
theorem seed_reach : Rch start (chk 2 1 1) := by
  unfold start
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gRb; gRb; gRb; gRb; gRb
  refine blankR ?_; gL
  show Rch (cfgL hg1 (app [true, F, true, true, F, true, true, F, F, F, true, F, true, true, F, F, true, F, F, true, true, true] (true ::: blank)) (app [true] blank)) _
  have hw : Clean3 [true, F, true, true, F, true, true, F, F, F, true, F, true, true, F, F, true, F, F, true, true, true] := by
    repeat (first | exact Clean3.nil | apply Clean3.one | apply Clean3.z1 | apply Clean3.z2 | apply Clean3.z3)
  refine Rch.tr (home_chk hw [true]) ?_
  have e : CW 2 1 1 = true :: List.reverse [true, F, true, true, F, true, true, F, F, F, true, F, true, true, F, F, true, F, F, true, true, true] ++ [true] := by
    simp [CW, upB, loB, up, lo, primesDesc_two, sv, pb, sx, sy, tailW, pzList, blkList]
  unfold chk; rw [e]; fin

theorem inv_two : Inv 2 1 1 := by
  have h1 : base 1 = 1 := by unfold base; rw [lp_one]; simp
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rw [h1, pc_val, pc_val]; decide

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

theorem reach_all (k : Nat) :
    HaltAt start ∨ ∃ n c, Inv (k+2) n c ∧ Rch start (chk (k+2) n c) := by
  induction k with
  | zero => exact Or.inr ⟨1, 1, inv_two, seed_reach⟩
  | succ k ih =>
    rcases ih with h | ⟨n, c, hI, hr⟩
    · exact Or.inl h
    · have cy := cycle (k+2) n c hI
      by_cases hh : Stop (k+2) n c
      · exact Or.inl (HaltAt.back hr (cy.1 hh))
      · obtain ⟨n', c', hI', hr'⟩ := cy.2 hh
        exact Or.inr ⟨n', c', hI', Rch.tr hr hr'.reach⟩

/-- consecutive primes `3 ≤ p < q` with fewer than 4 primes between their squares -/
def Counterex (p q : Nat) : Prop :=
  3 ≤ p ∧ PrimeDvd p ∧ PrimeDvd q ∧ p < q ∧ (∀ r, p < r → r < q → ¬ PrimeDvd r) ∧
    pc (q*q) - pc (p*p) < 4

theorem isqrt_eq {m n q : Nat} (h1 : n*n ≤ m) (h2 : m < (n+1)*(n+1)) (h3 : q*q ≤ m) (h4 : m < (q+1)*(q+1)) :
    n = q := by
  rcases Nat.lt_trichotomy n q with h | h | h
  · have := Nat.mul_le_mul (show n + 1 ≤ q by omega) (show n + 1 ≤ q by omega); omega
  · exact h
  · have := Nat.mul_le_mul (show q + 1 ≤ n by omega) (show q + 1 ≤ n by omega); omega

theorem lp_eq {p n : Nat} (hn : 2 ≤ n) (hp : PrimeDvd p) (hpn : p ≤ n)
    (hgap : ∀ r, p < r → r ≤ n → ¬ PrimeDvd r) : lp n = p := by
  obtain ⟨h1, h2, h3⟩ := lp_spec n hn
  rcases Nat.lt_trichotomy (lp n) p with h | h | h
  · exact absurd hp (h3 p h hpn)
  · exact h
  · exact absurd h1 (hgap _ h h2)

theorem pc_sq_pred (q : Nat) (hq : 2 ≤ q) : pc (q*q - 1) = pc (q*q) := by
  have := pc_succ (q*q - 1)
  have h4 : 4 ≤ q*q := Nat.mul_le_mul hq hq
  rw [show q*q - 1 + 1 = q*q by omega] at this
  have hnp : ¬ PrimeDvd (q*q) := by
    have := sq_not_prime (q-1) (by omega); rwa [show q - 1 + 1 = q by omega] at this
  rw [if_neg hnp] at this; omega

/-- the halting condition at a reachable checkpoint is exactly a counterexample -/
theorem stop_iff (m n c : Nat) (hI : Inv m n c) :
    Stop m n c ↔ Counterex (lp n) (n+1) ∧ m + 1 = (n+1)*(n+1) := by
  obtain ⟨hm2, hn, h1, h2, hc⟩ := hI
  constructor
  · rintro ⟨hs, hp, h2n, hc4⟩
    obtain ⟨l1, l2, l3⟩ := lp_spec n h2n
    have hpm : m = (n+1)*(n+1) - 1 := by omega
    by_cases h3 : 3 ≤ lp n
    · have hb : base n = lp n * lp n := by unfold base; rw [if_pos h3]
      refine ⟨⟨h3, l1, hp, by omega, fun r hr1 hr2 => l3 r hr1 (by omega), ?_⟩, hs⟩
      rw [hc, hb, hpm, pc_sq_pred (n+1) (by omega)] at hc4; exact hc4
    · exfalso
      have hl2 := l1.1
      have hn2 : n = 2 := by
        apply Classical.byContradiction; intro hne
        exact l3 3 (by omega) (by omega) ((primeDvd_iff 3).2 (by decide))
      subst hn2
      have hb : base 2 = 1 := by unfold base; rw [if_neg h3]
      rw [hc, hb, show m = 8 by omega, pc_val, pc_val] at hc4
      revert hc4; decide
  · rintro ⟨⟨h3, hp, hq, hpq, hgap, hlt⟩, hs⟩
    refine ⟨hs, hq, by omega, ?_⟩
    have hb : base n = lp n * lp n := by unfold base; rw [if_pos h3]
    have hpm : m = (n+1)*(n+1) - 1 := by omega
    rw [hc, hb, hpm, pc_sq_pred (n+1) (by omega)]; exact hlt

theorem haltAt_of_counterex (p q : Nat) (h : Counterex p q) : HaltAt start := by
  obtain ⟨h3, hp, hq, hpq, hgap, hlt⟩ := h
  have hq5 : 4 ≤ q := by omega
  have hqq : 16 ≤ q * q := Nat.mul_le_mul hq5 hq5
  rcases reach_all (q*q - 3) with h | ⟨n, c, hI, hr⟩
  · exact h
  · rw [show q*q - 3 + 2 = q*q - 1 by omega] at hI hr
    have hn : n = q - 1 := by
      have := sq_succ (q-1)
      rw [show q - 1 + 1 = q by omega] at this
      exact isqrt_eq hI.2.2.1 hI.2.2.2.1 (by omega) (by rw [show q - 1 + 1 = q by omega]; omega)
    subst hn
    have hq1 : q - 1 + 1 = q := by omega
    have hlp : lp (q - 1) = p := lp_eq (by omega) hp (by omega) (fun r h1 h2 => hgap r h1 (by omega))
    have hs : Stop (q*q - 1) (q-1) c := by
      refine (stop_iff _ _ c hI).2 ⟨?_, ?_⟩
      · rw [hlp, hq1]; exact ⟨h3, hp, hq, hpq, hgap, hlt⟩
      · rw [hq1]; omega
    exact HaltAt.back hr ((cycle _ _ c hI).1 hs)

/-- Halting in terms of `PrimeDvd` and `pc`. -/
theorem halts_iff_dvd : Halts delta start ↔ ∃ p q, Counterex p q := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ x, (∃ m n c, Inv m n c ∧ x = chk m n c) →
        ∃ x', (∃ m n c, Inv m n c ∧ x' = chk m n c) ∧ Rch1 x x' := by
      rintro x ⟨m, n, c, hI, rfl⟩
      have cy := cycle m n c hI
      by_cases hh : Stop m n c
      · exact absurd ⟨_, _, ((stop_iff m n c hI).1 hh).1⟩ hno
      · obtain ⟨n', c', hI', hr⟩ := cy.2 hh
        exact ⟨_, ⟨m+1, n', c', hI', rfl⟩, hr⟩
    exact not_halts_of_progress delta _ prog _ ⟨2, 1, 1, inv_two, rfl⟩ (halts_det hH seed_reach)
  · rintro ⟨p, q, h⟩
    exact (haltAt_of_counterex p q h).halts

theorem haltAt_of (h : ∃ p q, 3 ≤ p ∧ TinyCryptids.Prime p ∧ TinyCryptids.Prime q ∧ p < q ∧
    (∀ r, p < r → r < q → ¬ TinyCryptids.Prime r) ∧
    TinyCryptids.primeCount (q ^ 2) - TinyCryptids.primeCount (p ^ 2) < 4) : HaltAt start := by
  obtain ⟨p, q, h3, hp, hq, hpq, hgap, hlt⟩ := h
  refine haltAt_of_counterex p q ⟨h3, (primeDvd_iff p).2 hp, (primeDvd_iff q).2 hq, hpq,
    fun r h1 h2 hr => hgap r h1 h2 ((primeDvd_iff r).1 hr), ?_⟩
  rw [pc_val, pc_val, ← Nat.pow_two, ← Nat.pow_two]; exact hlt

/-- **Main theorem.** Started on a blank tape, the design machine halts if and only if
Brocard's conjecture is false: some consecutive primes `3 ≤ p < q` have fewer than 4 primes
between `p²` and `q²`. -/
theorem halts_iff : Halts delta start ↔ ∃ p q, 3 ≤ p ∧ TinyCryptids.Prime p ∧ TinyCryptids.Prime q ∧
    p < q ∧ (∀ r, p < r → r < q → ¬ TinyCryptids.Prime r) ∧
    TinyCryptids.primeCount (q ^ 2) - TinyCryptids.primeCount (p ^ 2) < 4 := by
  rw [halts_iff_dvd]
  constructor
  · rintro ⟨p, q, h3, hp, hq, hpq, hgap, hlt⟩
    refine ⟨p, q, h3, (primeDvd_iff p).1 hp, (primeDvd_iff q).1 hq, hpq,
      fun r h1 h2 hr => hgap r h1 h2 ((primeDvd_iff r).2 hr), ?_⟩
    rw [pc_val, pc_val] at hlt; rw [Nat.pow_two, Nat.pow_two]; exact hlt
  · intro h
    obtain ⟨p, q, h3, hp, hq, hpq, hgap, hlt⟩ := h
    refine ⟨p, q, h3, (primeDvd_iff p).2 hp, (primeDvd_iff q).2 hq, hpq,
      fun r h1 h2 hr => hgap r h1 h2 ((primeDvd_iff r).1 hr), ?_⟩
    rw [pc_val, pc_val, ← Nat.pow_two, ← Nat.pow_two]; exact hlt

end TM.BrocardPrimes
