import TinyCryptids.Fermat.Enum
import TinyCryptids.Fermat.Nexcom
namespace TM.Fermat
open St

def chkT (t : Tup) : Cfg St := chk t.1 t.2.1 t.2.2.1 t.2.2.2
def suT (t : Tup) : Cfg St := suC t.1 t.2.1 t.2.2.1 t.2.2.2
def en2T (t : Tup) : Cfg St := en2C t.1 t.2.1 t.2.2.1 t.2.2.2
def Sol (t : Tup) : Prop := t.2.1 ^ t.1 + t.2.2.1 ^ t.1 = t.2.2.2 ^ t.1

theorem enum_step : ∀ t : Tup, Valid t → t ≠ seedT → Rch (en2T t) (suT (nxt t))
  | (E, a, b, c), ⟨hE, ha, hb, hc⟩, hne => by
    unfold en2T suT
    by_cases h4 : 4 ≤ E
    · obtain ⟨e, rfl⟩ : ∃ e, E = e + 4 := ⟨E - 4, by omega⟩
      simp only [nxt, if_pos h4]
      rw [show e + 4 - 1 = e + 3 by omega]; exact enum_E e a b c
    obtain rfl : E = 3 := by omega
    by_cases ha2 : 2 ≤ a
    · simp only [nxt, if_neg h4, if_pos ha2]
      by_cases ha3 : a = 2
      · subst ha3; exact enum_B2a b c
      · obtain ⟨m, rfl⟩ : ∃ m, a = m + 3 := ⟨a - 3, by omega⟩; exact enum_B2b m b c
    obtain rfl : a = 1 := by omega
    by_cases hb2 : 2 ≤ b
    · simp only [nxt, if_neg h4, if_neg ha2, if_pos hb2]
      by_cases hb3 : b = 2
      · subst hb3; exact enum_B3a c
      · obtain ⟨m, rfl⟩ : ∃ m, b = m + 3 := ⟨b - 3, by omega⟩; exact enum_B3b m c
    obtain rfl : b = 1 := by omega
    have hc2 : 2 ≤ c := by
      apply Classical.byContradiction; intro h
      exact hne (by simp [seedT]; omega)
    simp only [nxt, if_neg h4, if_neg ha2, if_neg hb2, if_pos hc2]
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 2 := ⟨c - 2, by omega⟩
    rw [show m + 2 + 3 = m + 5 by omega]; exact enum_last m

theorem nxt_ne_seed : ∀ t : Tup, Valid t → nxt t ≠ seedT := by
  rintro ⟨E, a, b, c⟩ ⟨hE, ha, hb, hc⟩
  simp only [nxt, seedT]
  split <;> (try split) <;> (try split) <;> (try split) <;> simp only [ne_eq, Prod.mk.injEq] <;> omega

/-- one cycle of the main loop -/
theorem cycle (t : Tup) (ht : Valid t) (hne : t ≠ seedT) :
    (Sol (nxt t) → HaltAt (chkT t)) ∧ (¬ Sol (nxt t) → Rch1 (chkT t) (chkT (nxt t))) := by
  have hv := nxt_valid t ht
  have e := enum_step t ht hne
  have hs : step delta (chkT t) = some (en2T t) := chk_step _ _ _ _
  generalize nxt t = t' at hv e ⊢
  obtain ⟨E, a, b, c⟩ := t'
  obtain ⟨hE, ha, hb, hc⟩ := hv
  have tc := tuple_check E a b c (by omega) ha hb hc
  refine ⟨fun hsol => ?_, fun hsol => ?_⟩
  · exact HaltAt.back (Rch.tr (reach_step delta hs) e) (tc.1 hsol)
  · exact Reach1.of_step_reach delta hs (Rch.tr e (tc.2 hsol))

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

theorem itr_succ' (t : Tup) : ∀ j, itr (j+1) t = itr j (nxt t) := by
  intro j; induction j with
  | zero => rfl
  | succ j ih => show nxt (itr (j+1) t) = nxt (itr j (nxt t)); rw [ih]

theorem halts_if_sol : ∀ k (t : Tup), Valid t → t ≠ seedT → (∃ j, 1 ≤ j ∧ j ≤ k ∧ Sol (itr j t)) →
    HaltAt (chkT t) := by
  intro k
  induction k with
  | zero => intro t _ _ ⟨j, h1, h2, _⟩; omega
  | succ k ih =>
    intro t ht hne ⟨j, h1, h2, hj⟩
    have c := cycle t ht hne
    by_cases hs : Sol (nxt t)
    · exact c.1 hs
    · have hj2 : 2 ≤ j := by
        rcases Nat.lt_or_ge j 2 with hlt | hge
        · obtain rfl : j = 1 := by omega
          exact absurd hj hs
        · exact hge
      have := ih (nxt t) (nxt_valid t ht) (nxt_ne_seed t ht) ⟨j - 1, by omega, by omega, by
        rw [← itr_succ', show j - 1 + 1 = j by omega]; exact hj⟩
      exact HaltAt.back (c.2 hs).reach this

def seedT4 : Tup := (4, 1, 1, 1)

/-- from the blank tape, the machine writes the seed tuple and reaches the first checkpoint -/
theorem seed_reach : Rch start (chkT seedT4) := by
  refine Rch.tr ?_ (clear_home 4 1 1 1 (by omega))
  unfold start
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  gRb; gRb; gRb; gRb
  unfold clrC leftOf preC
  simp [app_append, app_replicate, ones_succ, cons_blank]
  fin

/-- If a counterexample exists, the machine reaches its explicit halting state. -/
theorem haltAt_of_sol (h : ∃ E x y z : Nat, 3 ≤ E ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x ^ E + y ^ E = z ^ E) :
    HaltAt start := by
  obtain ⟨E, x, y, z, hE, hx, hy, hz, hs⟩ := h
  obtain ⟨k, hk⟩ := reached E x y z ⟨hE, hx, hy, hz⟩
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp [itr, seedT] at hk; obtain ⟨rfl, rfl, rfl, rfl⟩ := hk; simp at hs
    · simp [itr, nxt, seedT] at hk; obtain ⟨rfl, rfl, rfl, rfl⟩ := hk; simp at hs
    · omega
  refine HaltAt.back seed_reach
    (halts_if_sol (k-1) seedT4 ⟨by decide, by decide, by decide, by decide⟩ (by decide)
      ⟨k - 1, by omega, Nat.le_refl _, ?_⟩)
  have h1 : itr (k - 1) seedT4 = itr k seedT := by
    rw [show seedT4 = nxt seedT from rfl, ← itr_succ', show k - 1 + 1 = k by omega]
  rw [h1, hk]; exact hs

/-- **Main theorem.** Started on a blank tape, the 127-state design halts if and
only if Fermat's Last Theorem has a counterexample. -/
theorem halts_iff :
    Halts delta start ↔ ∃ E x y z : Nat, 3 ≤ E ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x ^ E + y ^ E = z ^ E := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have prog : ∀ c, (∃ t, Valid t ∧ t ≠ seedT ∧ c = chkT t) → ∃ c', (∃ t, Valid t ∧ t ≠ seedT ∧ c' = chkT t) ∧ Rch1 c c' := by
      rintro c ⟨t, ht, hne, rfl⟩
      refine ⟨chkT (nxt t), ⟨nxt t, nxt_valid t ht, nxt_ne_seed t ht, rfl⟩, (cycle t ht hne).2 ?_⟩
      intro hs
      have hv := nxt_valid t ht
      generalize nxt t = t' at hv hs
      obtain ⟨E, a, b, c⟩ := t'
      obtain ⟨hE, ha, hb, hc⟩ := hv
      exact hno ⟨E, a, b, c, hE, ha, hb, hc, hs⟩
    exact not_halts_of_progress delta _ prog _ ⟨seedT4, ⟨by decide, by decide, by decide, by decide⟩, by decide, rfl⟩
      (halts_det hH seed_reach)
  · intro h; exact (haltAt_of_sol h).halts

end TM.Fermat
