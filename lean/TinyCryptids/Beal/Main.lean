import TinyCryptids.Beal.Enum

/-!
# The main theorem

NEXCOM on `T6` (the six block lengths minus 4, `x = r₁ + 3`, …, `a = r₄ + 1`, …) reaches every
tuple but `0`; the machine checks the tuples `nxt seedT, nxt (nxt seedT), …` in turn.
-/

namespace TM.Beal
open St

abbrev T6 := Nat × Nat × Nat × Nat × Nat × Nat

def nxt : T6 → T6
  | (r1, r2, r3, r4, r5, r6) =>
    if 1 ≤ r1 then (r1 - 1, r2 + 1, r3, r4, r5, r6)
    else if 1 ≤ r2 then (r2 - 1, 0, r3 + 1, r4, r5, r6)
    else if 1 ≤ r3 then (r3 - 1, 0, 0, r4 + 1, r5, r6)
    else if 1 ≤ r4 then (r4 - 1, 0, 0, 0, r5 + 1, r6)
    else if 1 ≤ r5 then (r5 - 1, 0, 0, 0, 0, r6 + 1)
    else (r6 + 1, 0, 0, 0, 0, 0)

def NZ : T6 → Prop
  | (r1, r2, r3, r4, r5, r6) => 1 ≤ r1 + r2 + r3 + r4 + r5 + r6

def seedT : T6 := (1, 0, 0, 0, 0, 0)

def itr : Nat → T6 → T6
  | 0, t => t
  | k + 1, t => nxt (itr k t)

theorem nxt_nz : ∀ t : T6, NZ (nxt t) := by
  rintro ⟨r1, r2, r3, r4, r5, r6⟩
  simp only [nxt, NZ]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

macro "nx" : tactic => `(tactic| (simp only [nxt]; split <;> (try split) <;> (try split) <;> (try split) <;>
  (try split) <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega))

/-- every tuple but `0` is reached from the seed -/
theorem reached : ∀ r1 r2 r3 r4 r5 r6 : Nat, NZ (r1, r2, r3, r4, r5, r6) →
    ∃ k, itr k seedT = (r1, r2, r3, r4, r5, r6)
  | r1, r2, r3, r4, r5, r6, h => by
    by_cases h2 : 1 ≤ r2
    · obtain ⟨k, hk⟩ := reached (r1 + 1) (r2 - 1) r3 r4 r5 r6 (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h3 : 1 ≤ r3
    · obtain ⟨k, hk⟩ := reached 0 (r1 + 1) (r3 - 1) r4 r5 r6 (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h4 : 1 ≤ r4
    · obtain ⟨k, hk⟩ := reached 0 0 (r1 + 1) (r4 - 1) r5 r6 (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h5 : 1 ≤ r5
    · obtain ⟨k, hk⟩ := reached 0 0 0 (r1 + 1) (r5 - 1) r6 (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h6 : 1 ≤ r6
    · obtain ⟨k, hk⟩ := reached 0 0 0 0 (r1 + 1) (r6 - 1) (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    by_cases h1 : 2 ≤ r1
    · obtain ⟨k, hk⟩ := reached 0 0 0 0 0 (r1 - 1) (by simp only [NZ]; omega)
      exact ⟨k + 1, by show nxt (itr k seedT) = _; rw [hk]; nx⟩
    · refine ⟨0, ?_⟩
      simp only [NZ] at h
      simp only [itr, seedT, Prod.mk.injEq]; omega
termination_by r1 r2 r3 r4 r5 r6 => (r1 + r2 + r3 + r4 + r5 + r6, r6, r5, r4, r3, r2)
decreasing_by all_goals (simp_wf; simp only [Prod.lex_def, true_and, and_true]; omega)

def en2T : T6 → Cfg St
  | (r1, r2, r3, r4, r5, r6) => en2C (r1 + 3) (r2 + 3) (r3 + 3) (r4 + 1) (r5 + 1) (r6 + 1)
def gAT : T6 → Cfg St
  | (r1, r2, r3, r4, r5, r6) => gAC (r1 + 3) (r2 + 3) (r3 + 3) (r4 + 1) (r5 + 1) (r6 + 1)

/-- the counterexample condition for a tuple -/
def Sol : T6 → Prop
  | (r1, r2, r3, r4, r5, r6) => Nat.gcd (r4 + 1) (r5 + 1) = 1 ∧
      (r4 + 1) ^ (r1 + 3) + (r5 + 1) ^ (r2 + 3) = (r6 + 1) ^ (r3 + 3)

theorem enum_step : ∀ t : T6, NZ t → Rch (en2T t) (gAT (nxt t)) := by
  rintro ⟨r1, r2, r3, r4, r5, r6⟩ h
  by_cases h1 : 1 ≤ r1
  · obtain ⟨e, rfl⟩ : ∃ e, r1 = e + 1 := ⟨r1 - 1, by omega⟩
    simp only [nxt, if_pos h1]
    exact enum_first e (r2 + 3 + 1) _
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
  by_cases h4 : 1 ≤ r4
  · obtain ⟨t, rfl⟩ : ∃ t, r4 = t + 1 := ⟨r4 - 1, by omega⟩
    simp only [nxt, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    exact enum_mid 2 t r5 _
  obtain rfl : r4 = 0 := by omega
  by_cases h5 : 1 ≤ r5
  · obtain ⟨t, rfl⟩ : ∃ t, r5 = t + 1 := ⟨r5 - 1, by omega⟩
    simp only [nxt, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    exact enum_mid 3 t r6 _
  obtain rfl : r5 = 0 := by omega
  obtain ⟨t, rfl⟩ : ∃ t, r6 = t + 1 := ⟨r6 - 1, by simp only [NZ] at h; omega⟩
  simp only [nxt, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
  exact enum_last t

macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))
macro "gLb" : tactic => `(tactic| first | gL | (refine blankR ?_; gL))

/-- from the blank tape: write the seed tuple `(4, 3, 3, 1, 1, 1)` and reach `en2` -/
theorem seed_reach : Rch start (en2T seedT) := by
  unfold start
  iterate 38 gRb
  gRb; gRb; gRb; gLb
  refine Rch.tr (PHE.find (w := [true, F, F, true, F, F, true, true, true, true, F, F, true, true, true, true,
    F, F, true, true, true, true, F, F, true, true, true, true, F, F, true, true, true, true, F, F,
    true, true, true]) (by c12) _ _) ?_
  gR; gL
  show Rch (cfgL H1 (app [] (true ::: blank)) _) _
  refine Rch.tr (HH.go Clean12.nil _) ?_
  gR
  simp only [List.reverse_nil, app_nil]
  exact Reach.refl delta _

theorem tuple_t : ∀ t : T6, (Sol t → HaltAt (gAT t)) ∧ (¬ Sol t → Rch (gAT t) (en2T t)) := by
  rintro ⟨r1, r2, r3, r4, r5, r6⟩
  exact tuple_check (r1 + 3) (r2 + 3) (r3 + 3) (r4 + 1) (r5 + 1) (r6 + 1) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)

theorem reach1_of {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero =>
    simp only [Sys.run] at hn
    exact absurd (congrArg Cfg.q (Option.some.inj hn)) hq
  | succ n => exact ⟨n, hn⟩

theorem gAT_q (t : T6) : (gAT t).q = gA0 := by obtain ⟨_, _, _, _, _, _⟩ := t; rfl
theorem en2T_q (t : T6) : (en2T t).q = en2 := by obtain ⟨_, _, _, _, _, _⟩ := t; rfl

/-- one cycle of the main loop -/
theorem cycle (t : T6) (ht : NZ t) :
    (Sol (nxt t) → HaltAt (en2T t)) ∧ (¬ Sol (nxt t) → Rch1 (en2T t) (en2T (nxt t))) := by
  have e := enum_step t ht
  have tc := tuple_t (nxt t)
  refine ⟨fun hs => HaltAt.back e (tc.1 hs), fun hs => ?_⟩
  refine Reach.trans_reach1 delta (Reach.refl delta _) ?_
  exact Reach1.trans_reach delta (reach1_of e (by rw [en2T_q, gAT_q]; decide)) (tc.2 hs)

theorem itr_succ' (t : T6) : ∀ j, itr (j + 1) t = itr j (nxt t) := by
  intro j; induction j with
  | zero => rfl
  | succ j ih => show nxt (itr (j + 1) t) = nxt (itr j (nxt t)); rw [ih]

theorem halts_if_sol : ∀ k (t : T6), NZ t → (∃ j, 1 ≤ j ∧ j ≤ k ∧ Sol (itr j t)) → HaltAt (en2T t) := by
  intro k
  induction k with
  | zero => intro t _ ⟨j, h1, h2, _⟩; omega
  | succ k ih =>
    intro t ht ⟨j, h1, h2, hj⟩
    have c := cycle t ht
    by_cases hs : Sol (nxt t)
    · exact c.1 hs
    · have hj2 : 2 ≤ j := by
        rcases Nat.lt_or_ge j 2 with hlt | hge
        · obtain rfl : j = 1 := by omega
          exact absurd hj hs
        · exact hge
      have := ih (nxt t) (nxt_nz t) ⟨j - 1, by omega, by omega, by
        rw [← itr_succ', show j - 1 + 1 = j by omega]; exact hj⟩
      exact HaltAt.back (c.2 hs).reach this

/-- If a counterexample exists, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ a b c x y z, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
    Nat.gcd a b = 1 ∧ a ^ x + b ^ y = c ^ z) : HaltAt start := by
  obtain ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, hg, hs⟩ := h
  have hsol : Sol (x - 3, y - 3, z - 3, a - 1, b - 1, c - 1) := by
    simp only [Sol]
    rw [show a - 1 + 1 = a by omega, show b - 1 + 1 = b by omega, show c - 1 + 1 = c by omega,
      show x - 3 + 3 = x by omega, show y - 3 + 3 = y by omega, show z - 3 + 3 = z by omega]
    exact ⟨hg, hs⟩
  have hnz : NZ (x - 3, y - 3, z - 3, a - 1, b - 1, c - 1) := by
    simp only [NZ]
    apply Classical.byContradiction; intro hn
    obtain rfl : a = 1 := by omega
    obtain rfl : b = 1 := by omega
    obtain rfl : c = 1 := by omega
    simp at hs
  obtain ⟨k, hk⟩ := reached _ _ _ _ _ _ hnz
  have hk1 : 1 ≤ k := by
    rcases k with _ | k
    · simp only [itr, seedT, Prod.mk.injEq] at hk
      obtain ⟨h1, -, -, h4, h5, h6⟩ := hk
      obtain rfl : a = 1 := by omega
      obtain rfl : b = 1 := by omega
      obtain rfl : c = 1 := by omega
      simp at hs
    · omega
  refine HaltAt.back seed_reach (halts_if_sol k seedT (by simp only [NZ, seedT]; omega) ⟨k, hk1, Nat.le_refl _, ?_⟩)
  rw [hk]; exact hsol

/-- **Main theorem.** Started on a blank tape, the design halts if and only if Beal's
conjecture has a counterexample. -/
theorem halts_iff :
    Halts delta start ↔ ∃ a b c x y z, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
      Nat.gcd a b = 1 ∧ a ^ x + b ^ y = c ^ z := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ t, NZ t ∧ c = en2T t) → ∃ c', (∃ t, NZ t ∧ c' = en2T t) ∧ Rch1 c c' := by
      rintro c ⟨t, ht, rfl⟩
      refine ⟨en2T (nxt t), ⟨nxt t, nxt_nz t, rfl⟩, (cycle t ht).2 ?_⟩
      intro hs
      generalize nxt t = t' at hs
      obtain ⟨r1, r2, r3, r4, r5, r6⟩ := t'
      exact hno ⟨r4 + 1, r5 + 1, r6 + 1, r1 + 3, r2 + 3, r3 + 3, by omega, by omega, by omega, by omega,
        by omega, by omega, hs.1, hs.2⟩
    exact not_halts_of_progress delta _ prog _ ⟨seedT, by simp only [NZ, seedT]; omega, rfl⟩
      (Sys.Halts.of_reach seed_reach hH)
  · intro h; exact (haltAt_of h).halts

end TM.Beal
