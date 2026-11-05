import TinyCryptids.LegendreSieve.Cycle
namespace TM.LegendreSieve
open St

/-! ## Main theorem -/

/-- One increment, all cases: halt exactly when `m+1 = (n+1)²` and no prime was
seen since `n²`; otherwise strictly progress to the next checkpoint. -/
theorem cycle (m n : Nat) (f : Bool) (hI : Inv m n f) :
    (m + 1 = (n+1)*(n+1) ∧ f = false → HaltAt (chk m n f)) ∧
    (¬ (m + 1 = (n+1)*(n+1) ∧ f = false) →
      ∃ n' f', Inv (m+1) n' f' ∧ Rch1 (chk m n f) (chk (m+1) n' f')) := by
  by_cases hp : PrimeDvd (m+1)
  · have hns : m + 1 ≠ (n+1)*(n+1) := fun e => sq_not_prime n hI.1 (e ▸ hp)
    refine ⟨fun h => absurd h.1 hns, fun _ => ?_⟩
    obtain ⟨h1, h2⟩ := cyc_prime m n f hI hp
    exact ⟨n, true, h2, h1⟩
  · by_cases hs : m + 1 = (n+1)*(n+1)
    · cases f with
      | false => exact ⟨fun _ => cyc_halt m n hI hs, fun h => absurd ⟨hs, rfl⟩ h⟩
      | true =>
        refine ⟨fun h => absurd h.2 (by simp), fun _ => ?_⟩
        obtain ⟨h1, h2⟩ := cyc_square m n hI hs
        exact ⟨n+1, false, h2, h1⟩
    · refine ⟨fun h => absurd h.1 hs, fun _ => ?_⟩
      obtain ⟨h1, h2⟩ := cyc_comp m n f hI hp hs
      exact ⟨n, f, h2, h1⟩

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

theorem not_prime_one : ¬ PrimeDvd 1 := fun h => by have := h.1; omega

theorem blocks_one : blocks 1 = [] := by
  simp [blocks, primesDesc, not_prime_one]

/-- From a blank tape, the 11-cell seed is written and the first checkpoint (m = 1) reached. -/
theorem seed_reach : Rch start (chk 1 1 false) := by
  unfold start
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  refine blankR ?_; gL
  show Rch (cfgL hg1 (app [F, true, true, true, F, F, F, true, true] (true ::: blank)) (app [true] blank)) _
  have hw : Clean3 [F, true, true, true, F, F, F, true, true] :=
    Clean3.z1 (Clean3.one (Clean3.one (Clean3.z3 (Clean3.one Clean3.nil))))
  refine Rch.tr (home_chk hw [true]) ?_
  have e : CW 1 1 false = [true, true, true, F, F, F, true, true, true, F, true] ++ [F, F] := by
    simp [CW, blocks_one, pzList, blkList]
  unfold chk; rw [e]; unfold chkW; rw [app_FF]; exact Reach.refl delta _

theorem inv_one : Inv 1 1 false := by
  refine ⟨Nat.le_refl _, by decide, by decide, ?_⟩
  simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
  intro p _ h1 h2; omega

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

theorem sq_eq (n : Nat) : n ^ 2 = n * n := by simp [Nat.pow_succ]

/-- `n ≥ 1` is a counterexample to Legendre's conjecture -/
def Counterex (n : Nat) : Prop := 1 ≤ n ∧ ∀ p, n * n < p → p < (n+1)*(n+1) → ¬ PrimeDvd p

theorem reach_all (k : Nat) :
    HaltAt start ∨ ∃ n f, Inv (k+1) n f ∧ Rch start (chk (k+1) n f) := by
  induction k with
  | zero => exact Or.inr ⟨1, false, inv_one, seed_reach⟩
  | succ k ih =>
    rcases ih with h | ⟨n, f, hI, hr⟩
    · exact Or.inl h
    · have c := cycle (k+1) n f hI
      by_cases hh : k + 1 + 1 = (n+1)*(n+1) ∧ f = false
      · exact Or.inl (HaltAt.back hr (c.1 hh))
      · obtain ⟨n', f', hI', hr'⟩ := c.2 hh
        exact Or.inr ⟨n', f', hI', Rch.tr hr hr'.reach⟩

theorem haltAt_of_counterex (n0 : Nat) (h : Counterex n0) : HaltAt start := by
  obtain ⟨hn0, hce⟩ := h
  have hsq := sq_succ n0
  have hnn : 1 ≤ n0 * n0 := Nat.mul_le_mul hn0 hn0
  rcases reach_all (n0*n0 + 2*n0 - 1) with h | ⟨n, f, hI, hr⟩
  · exact h
  · have hk : n0*n0 + 2*n0 - 1 + 1 = n0*n0 + 2*n0 := by omega
    rw [hk] at hI hr
    obtain ⟨hn, h1, h2, hf⟩ := hI
    have hn_eq : n = n0 := by
      rcases Nat.lt_or_ge n n0 with hl | hl
      · have := Nat.mul_le_mul (show n + 1 ≤ n0 by omega) (show n + 1 ≤ n0 by omega)
        omega
      · rcases Nat.lt_or_ge n0 n with hl2 | hl2
        · have := Nat.mul_le_mul (show n0 + 1 ≤ n by omega) (show n0 + 1 ≤ n by omega)
          omega
        · omega
    subst hn_eq
    have hf' : f = false := by
      cases f with
      | false => rfl
      | true =>
        obtain ⟨p, hp, hp1, hp2⟩ := hf.1 rfl
        exact absurd hp (hce p hp1 (by omega))
    subst hf'
    exact HaltAt.back hr (cyc_halt _ n ⟨hn, h1, h2, hf⟩ (by omega))

theorem haltAt_of_false_dvd (h : ∃ n, 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n+1) ^ 2 → ¬ PrimeDvd p) :
    HaltAt start := by
  obtain ⟨n, hn, h⟩ := h
  simp only [sq_eq] at h
  exact haltAt_of_counterex n ⟨hn, h⟩

/-- Halting in terms of `PrimeDvd`. -/
theorem halts_iff_dvd :
    Halts delta start ↔ ∃ n, 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n+1) ^ 2 → ¬ PrimeDvd p := by
  simp only [sq_eq]
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ m n f, Inv m n f ∧ c = chk m n f) →
        ∃ c', (∃ m n f, Inv m n f ∧ c' = chk m n f) ∧ Rch1 c c' := by
      rintro c ⟨m, n, f, hI, rfl⟩
      have c := cycle m n f hI
      by_cases hh : m + 1 = (n+1)*(n+1) ∧ f = false
      · exfalso; apply hno
        refine ⟨n, hI.1, fun p hp1 hp2 hp => ?_⟩
        obtain ⟨hs, rfl⟩ := hh
        exact absurd (hI.2.2.2.2 ⟨p, hp, hp1, by omega⟩) (by simp)
      · obtain ⟨n', f', hI', hr⟩ := c.2 hh
        exact ⟨_, ⟨m+1, n', f', hI', rfl⟩, hr⟩
    exact not_halts_of_progress delta _ prog _ ⟨1, 1, false, inv_one, rfl⟩
      (halts_det hH seed_reach)
  · rintro ⟨n, hn, h⟩
    exact (haltAt_of_counterex n ⟨hn, h⟩).halts

theorem haltAt_of_false (h : ∃ n, 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n + 1) ^ 2 → ¬ TinyCryptids.Prime p) :
    HaltAt start :=
  haltAt_of_false_dvd (by simpa only [primeDvd_iff] using h)

/-- **Main theorem.** Started on a blank tape, the design machine halts if and
only if Legendre's conjecture is false: for some `n ≥ 1` no prime lies strictly
between `n²` and `(n+1)²`. -/
theorem halts_iff :
    Halts delta start ↔ ∃ n, 1 ≤ n ∧ ∀ p, n ^ 2 < p → p < (n + 1) ^ 2 → ¬ TinyCryptids.Prime p := by
  rw [halts_iff_dvd]; simp only [primeDvd_iff]

end TM.LegendreSieve
