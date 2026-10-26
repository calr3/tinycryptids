import TinyCryptids.Kurepa.Round
import TinyCryptids.Kurepa.Spec

/-!
# Main theorem: the design halts iff some odd prime `p` divides `!p`
-/

namespace TM.Kurepa

open TinyCryptids
open St

local notation "F" => false

/-! ## the test -/

/-- the N hole after `u` steps from cell `c` -/
def nxs (m c : Nat) : Nat → Nat
  | 0 => c
  | u + 1 => nx m (nxs m c u)

theorem nx_range (m c : Nat) (h1 : 1 ≤ c) (h2 : c ≤ m) : 1 ≤ nx m c ∧ nx m c ≤ m := by
  unfold nx; split <;> omega

theorem nxs_range (m c : Nat) (h1 : 1 ≤ c) (h2 : c ≤ m) : ∀ u, 1 ≤ nxs m c u ∧ nxs m c u ≤ m
  | 0 => ⟨h1, h2⟩
  | u + 1 => let ⟨a, b⟩ := nxs_range m c h1 h2 u; nx_range m _ a b

/-- `TP m c lam K j` runs to the end of the test, `j + 1` steps of the N hole later -/
theorem test_run (m lam K : Nat) (hl : 2 ≤ lam) : ∀ j c, j + 2 ≤ lam → 1 ≤ c → c ≤ m →
    Rch (TP m c lam K j) (TE m (nxs m c (j + 1)) lam K) := by
  intro j
  induction j with
  | zero => intro c _ h1 h2; exact test_last m c lam K h1 h2 hl
  | succ j ih =>
    intro c hj h1 h2
    refine Rch.tr (test_step m c lam K j h1 h2 (by omega)) ?_
    have ⟨a, b⟩ := nx_range m c h1 h2
    have := ih (nx m c) (by omega) a b
    suffices e : nxs m (nx m c) (j + 1) = nxs m c (j + 1 + 1) by rw [← e]; exact this
    clear this ih
    generalize j + 1 = u
    induction u with
    | zero => rfl
    | succ u ih => show nx m _ = nx m _; rw [ih]

/-- from cell `m`, the hole is back at `m` after `u` steps iff `m ∣ u` -/
theorem nxs_m (m : Nat) (hm : 1 ≤ m) : ∀ u, nxs m m u = (u + m - 1) % m + 1 := by
  intro u
  induction u with
  | zero => show m = _; rw [Nat.mod_eq_of_lt (by omega)]; omega
  | succ u ih =>
    show nx m (nxs m m u) = _
    rw [ih]; unfold nx
    have hlt := Nat.mod_lt (u + m - 1) (show 0 < m by omega)
    have hd := Nat.mod_add_div (u + m - 1) m
    split
    · have : (u + 1 + m - 1) % m = (u + m - 1) % m + 1 := by
        rw [show u + 1 + m - 1 = ((u + m - 1) % m + 1) + m * ((u + m - 1) / m) by omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      omega
    · have : (u + 1 + m - 1) % m = 0 := by
        rw [show u + 1 + m - 1 = m * ((u + m - 1) / m + 1) by
          rw [Nat.mul_add, Nat.mul_one]; omega, Nat.mul_mod_right]
      omega

theorem nxs_m_eq (m u : Nat) (hm : 1 ≤ m) : nxs m m u = m ↔ m ∣ u := by
  rw [nxs_m m hm]
  have hlt := Nat.mod_lt (u + m - 1) (show 0 < m by omega)
  constructor
  · intro h
    have hd := Nat.mod_add_div (u + m - 1) m
    exact ⟨(u + m - 1) / m, by omega⟩
  · rintro ⟨k, rfl⟩
    rw [show m * k + m - 1 = (m - 1) + m * k by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## the copies -/

theorem copies (m lam K : Nat) (hK : 1 ≤ K) : ∀ k a b q, (m - a) * K + (K - 1 - b) = k →
    1 ≤ a → a ≤ m → b < K → Rch (X m a lam K b q) (PMc m lam K (q + k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro a b q h ha ha' hb
    have h1 : K - 1 - b = 0 := by omega
    have h2 : (m - a) * K = 0 := by omega
    have h3 : m - a = 0 := by
      rcases Nat.eq_zero_or_pos (m - a) with h | h
      · exact h
      · have := Nat.mul_le_mul_right K h; omega
    obtain rfl : a = m := by omega
    exact Rch.tr (copy_last a a lam K b q (by omega) ha ha') (c_fall a lam K (q + 1) ha)
  | succ k ih =>
    intro a b q h ha ha' hb
    by_cases hb1 : b + 1 < K
    · refine Rch.tr (copy_one m a lam K b q hb1) ?_
      rw [show q + (k + 1) + 1 = q + 1 + k + 1 by omega]
      exact ih a (b + 1) (q + 1) (by omega) ha ha' hb1
    · have ha1 : a < m := by
        apply Classical.byContradiction; intro hc
        have : m - a = 0 := by omega
        rw [this] at h; omega
      refine Rch.tr (copy_last m a lam K b q (by omega) ha ha') ?_
      refine Rch.tr (c_next m a lam K (q + 1) ha1) ?_
      refine Rch.tr (pg_to_x m (a + 1) lam K (q + 1) hK) ?_
      have e : (m - a) * K = (m - (a + 1)) * K + K := by
        rw [show m - a = m - (a + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
      rw [show q + (k + 1) + 1 = q + 1 + k + 1 by omega]
      exact ih (a + 1) 0 (q + 1) (by omega) (by omega) (by omega) (by omega)

/-- the whole multiplication: `m * K` copies -/
theorem multiply (m lam K : Nat) (hm : 1 ≤ m) (hK : 1 ≤ K) :
    Rch (PGc m 1 lam K 0) (PMc m lam K (m * K)) := by
  refine Rch.tr (pg_to_x m 1 lam K 0 hK) ?_
  have := copies m lam K hK ((m - 1) * K + (K - 1)) 1 0 0 (by omega) (by omega) hm (by omega)
  have e : m * K = (m - 1) * K + K := by
    rw [show m * K = (m - 1 + 1) * K by rw [Nat.sub_add_cancel hm], Nat.add_mul, Nat.one_mul]
  rw [show 0 + ((m - 1) * K + (K - 1)) + 1 = m * K by rw [e]; omega] at this
  exact this

/-! ## rounds -/

/-- length of `L` in round `n` -/
def lam (n : Nat) : Nat := leftFact n + n + 1

/-- start of the test of round `n` -/
def RS (n : Nat) : Cfg St := TP n n (lam n) (fact n) (lam n - 2)

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

theorem round (n : Nat) (hn : 2 ≤ n) :
    (n ∣ leftFact n → HaltAt (RS n)) ∧ (¬ n ∣ leftFact n → Rch1 (RS n) (RS (n + 1))) := by
  have hK := fact_pos n
  have hl : 2 ≤ lam n := by unfold lam; omega
  have t := test_run n (lam n) (fact n) hl (lam n - 2) n (by omega) (by omega) (Nat.le_refl n)
  rw [show lam n - 2 + 1 = leftFact n + n by unfold lam; omega] at t
  have hiff : n ∣ leftFact n ↔ nxs n n (leftFact n + n) = n := by
    rw [nxs_m_eq n _ (by omega)]
    constructor
    · intro h; exact Nat.dvd_add h (Nat.dvd_refl n)
    · intro h; exact (Nat.dvd_add_iff_left (Nat.dvd_refl n)).mpr h
  refine ⟨fun h => HaltAt.back t ?_, fun h => ?_⟩
  · rw [hiff.mp h]; exact te_halt n _ _
  · have ⟨r1, r2⟩ := nxs_range n n (by omega) (Nat.le_refl n) (leftFact n + n)
    have hlt : nxs n n (leftFact n + n) < n := by
      rcases Nat.lt_or_ge (nxs n n (leftFact n + n)) n with h' | h'
      · exact h'
      · exact absurd (hiff.mpr (by omega)) h
    refine Reach1.trans_reach delta (reach1_of (Rch.tr t (te_grow n _ _ _ r1 hlt)) (by show p2 ≠ PG1; decide))
      (Rch.tr (multiply (n + 1) _ _ (by omega) hK) (Rch.tr (merge (n + 1) _ _ _ hK) ?_))
    unfold RS lam
    rw [show (n + 1) * fact n = fact (n + 1) by show _ = fact n * (n + 1); rw [Nat.mul_comm],
      show leftFact n + n + 1 + 1 + fact n = leftFact (n + 1) + (n + 1) + 1 by
        show _ = leftFact n + fact n + (n + 1) + 1; omega,
      show leftFact n + n + 1 + fact n - 1 = leftFact (n + 1) + (n + 1) + 1 - 2 by
        show _ = leftFact n + fact n + (n + 1) + 1 - 2; omega]
    exact Reach.refl delta _


/-! ## the seed and the main theorem -/

/-- the seed writes round 2 right to left (`F`, `m1`, `L`, `00`, `N`); then `N` grows as after a
test -/
theorem seed_reach : Rch start (PGc 3 1 5 2 0) := by
  unfold start PGc
  gL0; gL0; gL0; gL0; gL0; gL0; gL0; gL0; gL0; gL0; gL0; gL0; gL0; gR; gR
  simp only [ones_succ, ones_zero, tl_blank, cons_blank, tl_cons, cons_zero]; fin

theorem start_reach : Rch start (RS 3) :=
  Rch.tr seed_reach (Rch.tr (multiply 3 5 2 (by omega) (by omega)) (merge 3 5 2 _ (by omega)))

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- If some `n ≥ 3` divides `!n`, the machine reaches its explicit halting state. -/
theorem haltAt_of (h : ∃ n, 3 ≤ n ∧ n ∣ leftFact n) : HaltAt start := by
  obtain ⟨N, hN, hd⟩ := h
  suffices H : ∀ k n, 3 ≤ n → n + k = N → HaltAt (RS n) from
    HaltAt.back start_reach (H (N - 3) 3 (by omega) (by omega))
  intro k
  induction k with
  | zero => intro n _ h; subst h; exact (round _ (by omega)).1 hd
  | succ k ih =>
    intro n hn h
    by_cases hs : n ∣ leftFact n
    · exact (round n (by omega)).1 hs
    · exact HaltAt.back ((round n (by omega)).2 hs).reach (ih (n + 1) (by omega) (by omega))

/-- **Main theorem.** Started on a blank tape, the design halts if and only if some odd prime
`p` divides the left factorial `!p = 0! + 1! + … + (p - 1)!` (Kurepa's conjecture fails). -/
theorem halts_iff :
    Halts delta start ↔ ∃ p, Prime p ∧ 2 < p ∧ p ∣ leftFact p := by
  rw [← kurepa_iff]
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ n, 3 ≤ n ∧ c = RS n) → ∃ c', (∃ n, 3 ≤ n ∧ c' = RS n) ∧ Rch1 c c' := by
      rintro c ⟨n, hn, rfl⟩
      exact ⟨RS (n + 1), ⟨n + 1, by omega, rfl⟩,
        (round n (by omega)).2 (fun hd => hno ⟨n, hn, hd⟩)⟩
    exact not_halts_of_progress delta _ prog _ ⟨3, Nat.le_refl _, rfl⟩ (halts_det hH start_reach)
  · intro h; exact (haltAt_of h).halts

end TM.Kurepa
