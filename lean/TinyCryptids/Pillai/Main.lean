import TinyCryptids.Pillai.Enum
import TinyCryptids.Defs

/-!
# Main theorem: some beep count between boops repeats forever iff Pillai's conjecture fails

NEXCOM on `T4` (the four block lengths minus 4: `x = r₁ + 2`, `y = r₂ + 2`, `a = r₃ + 2`,
`b = r₄ + 2`) reaches every tuple but `0`; the machine checks the tuples `nxt seedT, nxt (nxt seedT),
…` in turn. The run is cut into one segment per tuple (the enumeration step, then the tuple),
whose events are `a ^ x - b ^ y - 1` beeps and a boop if `a ^ x > b ^ y` and none otherwise
(`seg_ex`), and `repeatsForever_of_segments` with `good_iff` gives the theorem.
-/

namespace TM.Pillai
open St TinyCryptids

abbrev T4 := Nat × Nat × Nat × Nat

def nxt : T4 → T4
  | (r1, r2, r3, r4) =>
    if 1 ≤ r1 then (r1 - 1, r2 + 1, r3, r4)
    else if 1 ≤ r2 then (r2 - 1, 0, r3 + 1, r4)
    else if 1 ≤ r3 then (r3 - 1, 0, 0, r4 + 1)
    else (r4 + 1, 0, 0, 0)

def NZ : T4 → Prop
  | (r1, r2, r3, r4) => 1 ≤ r1 + r2 + r3 + r4

def tot : T4 → Nat
  | (r1, r2, r3, r4) => r1 + r2 + r3 + r4

def seedT : T4 := (1, 0, 0, 0)

def itr : Nat → T4 → T4
  | 0, t => t
  | k + 1, t => nxt (itr k t)

theorem nxt_nz : ∀ t : T4, NZ (nxt t) := by
  rintro ⟨r1, r2, r3, r4⟩
  simp only [nxt, NZ]
  split <;> (try split) <;> (try split) <;> omega

theorem tot_nxt : ∀ t : T4, NZ t → tot t ≤ tot (nxt t) := by
  rintro ⟨r1, r2, r3, r4⟩ h
  simp only [nxt, tot, NZ] at h ⊢
  split <;> (try split) <;> (try split) <;> omega

macro "nx" : tactic => `(tactic| (simp only [nxt]; split <;> (try split) <;> (try split) <;>
  simp only [Prod.mk.injEq, and_true, true_and] <;> omega))

/-- every tuple but `0` is reached from the seed -/
theorem reached : ∀ r1 r2 r3 r4 : Nat, NZ (r1, r2, r3, r4) → ∃ k, itr k seedT = (r1, r2, r3, r4)
  | r1, r2, r3, r4, h => by
    by_cases h2 : 1 ≤ r2
    · obtain ⟨k, hk⟩ := reached (r1 + 1) (r2 - 1) r3 r4 (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h3 : 1 ≤ r3
    · obtain ⟨k, hk⟩ := reached 0 (r1 + 1) (r3 - 1) r4 (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h4 : 1 ≤ r4
    · obtain ⟨k, hk⟩ := reached 0 0 (r1 + 1) (r4 - 1) (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h1 : 2 ≤ r1
    · obtain ⟨k, hk⟩ := reached 0 0 0 (r1 - 1) (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    · refine ⟨0, ?_⟩
      simp only [NZ] at h
      simp only [itr, seedT, Prod.mk.injEq]; omega
termination_by r1 r2 r3 r4 => (r1 + r2 + r3 + r4, r4, r3, r2)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, true_and, and_true]; omega)

theorem itr_nz : ∀ k, NZ (itr k seedT)
  | 0 => by simp only [itr, seedT, NZ]; omega
  | k + 1 => nxt_nz _

theorem tot_mono (i : Nat) : ∀ j, i ≤ j → tot (itr i seedT) ≤ tot (itr j seedT) := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ j _ ih => exact Nat.le_trans ih (tot_nxt _ (itr_nz j))

/-- the totals grow without bound along the search -/
theorem tot_big (N : Nat) : ∃ K, ∀ k, K ≤ k → N ≤ tot (itr k seedT) := by
  obtain ⟨K, hK⟩ := reached (N + 1) 0 0 0 (by simp only [NZ]; omega)
  refine ⟨K, fun k hk => ?_⟩
  have := tot_mono K k hk
  rw [hK] at this
  exact Nat.le_trans (Nat.le_succ N) this

def en2T : T4 → Cfg St
  | (r1, r2, r3, r4) => en2C (r1 + 2) (r2 + 2) (r3 + 2) (r4 + 2)
def suT : T4 → Cfg St
  | (r1, r2, r3, r4) => suC (r1 + 2) (r2 + 2) (r3 + 2) (r4 + 2)

theorem enum_step : ∀ t : T4, NZ t → Rch (en2T t) (suT (nxt t)) := by
  rintro ⟨r1, r2, r3, r4⟩ h
  by_cases h1 : 1 ≤ r1
  · obtain ⟨e, rfl⟩ : ∃ e, r1 = e + 1 := ⟨r1 - 1, by omega⟩
    simp only [nxt, if_pos h1]
    exact enum_first e (r2 + 2 + 2) _
  obtain rfl : r1 = 0 := by omega
  by_cases h2 : 1 ≤ r2
  · obtain ⟨t, rfl⟩ : ∃ t, r2 = t + 1 := ⟨r2 - 1, by omega⟩
    simp only [nxt, if_neg h1, if_pos h2]
    exact enum_mid 0 t r3 _
  obtain rfl : r2 = 0 := by omega
  by_cases h3 : 1 ≤ r3
  · obtain ⟨t, rfl⟩ : ∃ t, r3 = t + 1 := ⟨r3 - 1, by omega⟩
    simp only [nxt, if_neg h1, if_neg h2, if_pos h3]
    exact enum_mid 1 t r4 _
  obtain rfl : r3 = 0 := by omega
  obtain ⟨t, rfl⟩ : ∃ t, r4 = t + 1 := ⟨r4 - 1, by simp only [NZ] at h; omega⟩
  simp only [nxt, if_neg h1, if_neg h2, if_neg h3]
  exact enum_last t

macro "c12" : tactic => `(tactic| repeat (first | exact Clean.nil | apply Clean.one | apply Clean.sep))

/-- from the blank tape: the seed writes x = 3 with a hole, then a round per block appends
`00 1111` (y, a, b = 2) while the hole moves right; then M, A and R, home: `en2` on `(3, 2, 2, 2)` -/
theorem seed_reach : Rch start (en2T seedT) := by
  unfold start
  iterate 166 (first | gRb | gLb)
  show Rch ⟨en2, F ::: true ::: F ::: F ::: F ::: blank, _⟩ _
  unfold en2T seedT en2C tupR RT
  simp only [ones_succ, ones_zero, cons_blank]
  fin

/-! ## one segment per tuple -/

/-- the exponents and bases of a tuple -/
def ex (t : T4) : Nat := t.1 + 2
def ey (t : T4) : Nat := t.2.1 + 2
def ba (t : T4) : Nat := t.2.2.1 + 2
def bb (t : T4) : Nat := t.2.2.2 + 2

/-- the tuple has events (`a ^ x > b ^ y`), and their number of beeps -/
def goodT (t : T4) : Prop := bb t ^ ey t + 2 ≤ 1 + ba t ^ ex t
def valT (t : T4) : Nat := 1 + ba t ^ ex t - bb t ^ ey t - 2

/-- the events of the tuple `t` -/
noncomputable def evsOf (t : T4) : List Bool := zev (1 + ba t ^ ex t) (bb t ^ ey t)

theorem tuple_t : ∀ t : T4, Tr (suT t) (evsOf t) (en2T t) := by
  rintro ⟨r1, r2, r3, r4⟩
  exact tuple_check (r1 + 2) (r2 + 2) (r3 + 2) (r4 + 2) (by omega) (by omega)

theorem hne : ¬ (zX3 = zX3 ∧ false = true) := fun h => by cases h.2

/-- the beeps and the boops of the run from the start -/
abbrev Bp := BeepsAt delta zX3 true start
abbrev Bo := BeepsAt delta zX3 false start

theorem en2T_q (t : T4) : (en2T t).q = en2 := by obtain ⟨_, _, _, _⟩ := t; rfl
theorem suT_q (t : T4) : (suT t).q = su0 := by obtain ⟨_, _, _, _⟩ := t; rfl

theorem seg_ex (k n : Nat) (hn : run delta n start = some (en2T (itr k seedT))) :
    ∃ m, run delta (n + m) start = some (en2T (itr (k + 1) seedT)) ∧ 0 < m ∧
      TM.evs Bp Bo n (n + m) = evsOf (itr (k + 1) seedT) := by
  have t1 : Tr (en2T (itr k seedT)) [] (suT (itr (k + 1) seedT)) := Tr.of (enum_step _ (itr_nz k))
  obtain ⟨m1, h1, e1⟩ := t1.evs deltaQ_sub rfl rfl hne hn
  obtain ⟨m2, h2, e2⟩ := (tuple_t (itr (k + 1) seedT)).evs deltaQ_sub rfl rfl hne h1
  have hm1 : 0 < m1 := by
    rcases Nat.eq_zero_or_pos m1 with e | e
    · rw [e, Nat.add_zero, hn] at h1
      have := congrArg Cfg.q (Option.some.inj h1)
      rw [en2T_q, suT_q] at this; cases this
    · exact e
  refine ⟨m1 + m2, by rw [← Nat.add_assoc]; exact h2, by omega, ?_⟩
  rw [← Nat.add_assoc, evs_append (b := n + m1) (by omega) (by omega), e1, e2]; rfl

theorem seed_ex : ∃ m, run delta (0 + m) start = some (en2T (itr 0 seedT)) ∧
    TM.evs Bp Bo 0 (0 + m) = [] :=
  (Tr.of seed_reach).evs deltaQ_sub rfl rfl hne rfl

/-- the step at which the `k`-th tuple's enumeration step starts -/
noncomputable def TT : (k : Nat) → {n : Nat // run delta n start = some (en2T (itr k seedT))}
  | 0 => ⟨0 + Classical.choose seed_ex, (Classical.choose_spec seed_ex).1⟩
  | k + 1 => ⟨(TT k).1 + Classical.choose (seg_ex k (TT k).1 (TT k).2),
      (Classical.choose_spec (seg_ex k (TT k).1 (TT k).2)).1⟩

noncomputable def Tm (k : Nat) : Nat := (TT k).1

theorem Tm_zero : TM.evs Bp Bo 0 (Tm 0) = [] := (Classical.choose_spec seed_ex).2

theorem Tm_seg (k : Nat) : TM.evs Bp Bo (Tm k) (Tm (k + 1)) = evsOf (itr (k + 1) seedT) :=
  (Classical.choose_spec (seg_ex k (TT k).1 (TT k).2)).2.2

theorem Tm_lt (k : Nat) : Tm k < Tm (k + 1) := by
  show (TT k).1 < (TT k).1 + Classical.choose (seg_ex k (TT k).1 (TT k).2)
  have := (Classical.choose_spec (seg_ex k (TT k).1 (TT k).2)).2.1
  omega

theorem Tm_ge (k : Nat) : k ≤ Tm k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => have := Tm_lt k; omega

/-! ## the main theorems -/

/-- The design never halts. -/
theorem never_halts : ¬ Halts delta start := by
  rintro ⟨n, hn⟩
  have := run_none_mono (δ := delta) hn (Tm n - n)
  rw [show n + (Tm n - n) = Tm n by have := Tm_ge n; omega] at this
  have h2 : run delta (Tm n) start = some _ := (TT n).2
  rw [h2] at this; cases this

theorem no_both (n : Nat) : ¬ (Bp n ∧ Bo n) := by
  rintro ⟨⟨c1, h1, -, b1, -⟩, ⟨c2, h2, -, b2, -⟩⟩
  rw [h1] at h2; cases h2; rw [b1] at b2; cases b2

open Classical in
theorem evsOf_eq (t : T4) : evsOf t = if goodT t then List.replicate (valT t) true ++ [false] else [] := by
  unfold evsOf zev goodT valT
  by_cases h : bb t ^ ey t + 2 ≤ 1 + ba t ^ ex t
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- some value repeats among the tuples' beep counts iff Pillai's conjecture fails -/
theorem good_iff : (∃ v, ∀ K, ∃ k, K ≤ k ∧ goodT (itr (k + 1) seedT) ∧ valT (itr (k + 1) seedT) = v) ↔
    ¬ PillaiConjecture := by
  constructor
  · rintro ⟨v, hv⟩ hP
    obtain ⟨N, hN⟩ := hP (v + 1) (by omega)
    obtain ⟨K, hK⟩ := tot_big N
    obtain ⟨k, hk, hg, hval⟩ := hv K
    have hT := hK (k + 1) (by omega)
    generalize itr (k + 1) seedT = t at hg hval hT
    obtain ⟨r1, r2, r3, r4⟩ := t
    simp only [goodT, valT, ex, ey, ba, bb] at hg hval
    have := hN (r3 + 2) (r4 + 2) (r1 + 2) (r2 + 2) (by omega) (by omega) (by omega) (by omega) (by omega)
    simp only [tot] at hT
    omega
  · intro hnp
    have : ∃ kk, 1 ≤ kk ∧ ∀ N, ∃ a b x y, 2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ x ∧ 2 ≤ y ∧ a ^ x = b ^ y + kk ∧
        N ≤ a + b + x + y := by
      apply Classical.byContradiction; intro h1; apply hnp; intro kk hkk
      apply Classical.byContradiction; intro h2; apply h1; refine ⟨kk, hkk, fun N => ?_⟩
      apply Classical.byContradiction; intro h3; apply h2; refine ⟨N, fun a b x y ha hb hx hy he => ?_⟩
      apply Classical.byContradiction; intro h4; apply h3
      exact ⟨a, b, x, y, ha, hb, hx, hy, he, by omega⟩
    obtain ⟨kk, hkk, hall⟩ := this
    refine ⟨kk - 1, fun K => ?_⟩
    obtain ⟨a, b, x, y, ha, hb, hx, hy, he, hN⟩ := hall (tot (itr (K + 1) seedT) + 9)
    obtain ⟨j, hj⟩ := reached (x - 2) (y - 2) (a - 2) (b - 2) (by simp only [NZ]; omega)
    have hjK : K + 1 < j := by
      apply Classical.byContradiction; intro hlt
      have := tot_mono j (K + 1) (by omega)
      have e : tot (x - 2, y - 2, a - 2, b - 2) = (x - 2) + (y - 2) + (a - 2) + (b - 2) := rfl
      rw [hj, e] at this; omega
    refine ⟨j - 1, by omega, ?_⟩
    rw [show j - 1 + 1 = j by omega, hj]
    simp only [goodT, valT, ex, ey, ba, bb]
    rw [show x - 2 + 2 = x by omega, show y - 2 + 2 = y by omega, show a - 2 + 2 = a by omega,
      show b - 2 + 2 = b by omega]
    omega

/-- **Main theorem.** Started on a blank tape, the design never halts, and some number of beeps
(`zX3` reading 1) between consecutive boops (`zX3` reading 0) occurs infinitely often iff
Pillai's conjecture is false. -/
theorem repeats_iff : RepeatsForever delta zX3 true zX3 false start ↔ ¬ PillaiConjecture := by
  rw [repeatsForever_of_segments delta zX3 true zX3 false start no_both Tm Tm_lt
    (fun k => goodT (itr (k + 1) seedT)) (fun k => valT (itr (k + 1) seedT))
    Tm_zero (fun k => (Tm_seg k).trans (evsOf_eq _))]
  exact good_iff

end TM.Pillai
